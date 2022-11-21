// Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// Licensed under the Apache License, Version 2.0 (the "License"). You may not
// use this file except in compliance with the License. A copy of the
// License is located at
//
// http://aws.amazon.com/apache2.0/
//
// or in the "license" file accompanying this file. This file is distributed
// on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,
// either express or implied. See the License for the specific language governing
// permissions and limitations under the License.

// Package datachannel implements data channel which is used to interactively run commands.
package datachannel

import (
	"bytes"
	"container/list"
	"crypto/aes"
	"crypto/cipher"
	"crypto/elliptic"
	cryptoRand "crypto/rand"
	"crypto/sha512"
	"encoding/base64"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"math"
	"math/rand"
	"runtime/debug"
	"sync"
	"time"

	"github.com/aws/amazon-ssm-agent/agent/context"
	"github.com/aws/amazon-ssm-agent/agent/log"
	"github.com/aws/amazon-ssm-agent/agent/session/communicator"
	mgsConfig "github.com/aws/amazon-ssm-agent/agent/session/config"
	mgsContracts "github.com/aws/amazon-ssm-agent/agent/session/contracts"
	"github.com/aws/amazon-ssm-agent/agent/session/crypto"
	"github.com/aws/amazon-ssm-agent/agent/session/retry"
	"github.com/aws/amazon-ssm-agent/agent/session/service"
	"github.com/aws/amazon-ssm-agent/agent/task"
	"github.com/aws/amazon-ssm-agent/agent/version"
	"github.com/aws/amazon-ssm-agent/agent/versionutil"
	"github.com/aws/aws-sdk-go/aws"
	"github.com/gorilla/websocket"
	"github.com/twinj/uuid"
	"golang.org/x/crypto/hkdf"
)

const (
	schemaVersion  = 1
	sequenceNumber = 0
	messageFlags   = 3
	// Timeout period before a handshake operation expires on the agent.
	handshakeTimeout                        = 1500 * time.Second
	clientVersionWithoutOutputSeparation    = "1.2.295"
	firstVersionWithOutputSeparationFeature = "1.2.312.0"
)

type IDataChannel interface {
	Initialize(context context.T, mgsService service.Service, sessionId string, clientId string, instanceId string, role string, cancelFlag task.CancelFlag, inputStreamMessageHandler InputStreamMessageHandler)
	SetWebSocket(context context.T, mgsService service.Service, sessionId string, clientId string, onMessageHandler func(input []byte)) error
	Open(log log.T) error
	Close(log log.T) error
	Reconnect(log log.T) error
	SendMessage(log log.T, input []byte, inputType int) error
	SendStreamDataMessage(log log.T, dataType mgsContracts.PayloadType, inputData []byte) error
	ResendStreamDataMessageScheduler(log log.T) error
	ProcessAcknowledgedMessage(log log.T, acknowledgeMessageContent mgsContracts.AcknowledgeContent)
	SendAcknowledgeMessage(log log.T, agentMessage mgsContracts.AgentMessage) error
	SendAgentSessionStateMessage(log log.T, sessionStatus mgsContracts.SessionStatus) error
	AddDataToOutgoingMessageBuffer(streamMessage StreamingMessage)
	RemoveDataFromOutgoingMessageBuffer(streamMessageElement *list.Element)
	AddDataToIncomingMessageBuffer(streamMessage StreamingMessage)
	RemoveDataFromIncomingMessageBuffer(sequenceNumber int64)
	SkipHandshake(log log.T)
	PerformHandshake(log log.T, kmsKeyId string, encryptionEnabled bool, sessionTypeRequest mgsContracts.SessionTypeRequest) (err error)
	GetClientVersion() string
	GetInstanceId() string
	GetRegion() string
	IsActive() bool
	PrepareToCloseChannel(log log.T)
	GetSeparateOutputPayload() bool
	SetSeparateOutputPayload(separateOutputPayload bool)
}

// DataChannel used for session communication between the message gateway service and the agent.
type DataChannel struct {
	wsChannel  communicator.IWebSocketChannel
	context    context.T
	Service    service.Service
	ChannelId  string
	ClientId   string
	InstanceId string
	Role       string
	Pause      bool
	//records sequence number of last acknowledged message received over data channel
	ExpectedSequenceNumber int64
	//records sequence number of last stream data message sent over data channel
	StreamDataSequenceNumber int64
	//ensure only one goroutine sending message with current StreamDataSequenceNumber in data channel
	//check carefully for deadlock when not reusing of SendStreamDataMessage
	StreamDataSequenceNumberMutex *sync.Mutex
	//buffer to store outgoing stream messages until acknowledged
	//using linked list for this buffer as access to oldest message is required and it support faster deletion from any position of list
	OutgoingMessageBuffer ListMessageBuffer
	//buffer to store incoming stream messages if received out of sequence
	//using map for this buffer as incoming messages can be out of order and retrieval would be faster by sequenceId
	IncomingMessageBuffer MapMessageBuffer
	//round trip time of latest acknowledged message
	RoundTripTime float64
	//round trip time variation of latest acknowledged message
	RoundTripTimeVariation float64
	//timeout used for resending unacknowledged message
	RetransmissionTimeout time.Duration
	//cancelFlag is used for passing cancel signal to plugin in when channel_closed message is received over data channel
	cancelFlag task.CancelFlag
	//inputStreamMessageHandler is responsible for handling plugin specific input_stream_data message
	inputStreamMessageHandler func(log log.T, streamDataMessage mgsContracts.AgentMessage) error
	//handshake captures handshake state and error
	handshake Handshake
	//blockCipher stores encrytion keys and provides interface for encryption/decryption functions
	blockCipher crypto.IBlockCipher
	// Indicates whether encryption was enabled
	encryptionEnabled     bool
	separateOutputPayload bool
	state                 agentHandshakeState

	// kmsService is the KMS service used to sign and verify the handshake keyshare
	kmsService *crypto.KMSService
	// agentLTKeyARN is the ARN for the KMS long-term-key used to sign and verify the handshake
	agentLTKeyARN          string
	logLTKeyARN            string
	encryptedClientReadKey string
	encryptedAgentReadKey  string
}

// agentHandshakeState represents the state of the handshake.
type agentHandshakeState struct {
	agentSecret   []byte
	sharedSecret  []byte
	sessionID     []byte
	agentWriteKey []byte
	agentReadKey  []byte
}

type ListMessageBuffer struct {
	Messages *list.List
	Capacity int
	Mutex    *sync.Mutex
}

type MapMessageBuffer struct {
	Messages map[int64]StreamingMessage
	Capacity int
	Mutex    *sync.Mutex
}

type StreamingMessage struct {
	Content        []byte
	SequenceNumber int64
	LastSentTime   time.Time
}

type InputStreamMessageHandler func(log log.T, streamDataMessage mgsContracts.AgentMessage) error

type Handshake struct {
	// Version of the client
	clientVersion string
	// Channel used to signal when handshake response is received
	responseChan chan bool
	// Random byte string used to verify encryption
	encryptionChallenge []byte
	// This indicates encryption was validated using encryption challenge exchange
	encryptionConfirmedChan chan bool
	error                   error
	// Indicates handshake is complete (Handshake Complete message sent to client)
	complete bool
	// Indiciates if handshake has been skipped
	skipped            bool
	handshakeStartTime time.Time
	handshakeEndTime   time.Time
}

// NewDataChannel constructs datachannel objects.
func NewDataChannel(context context.T,
	channelId string,
	clientId string,
	inputStreamMessageHandler InputStreamMessageHandler,
	cancelFlag task.CancelFlag) (*DataChannel, error) {

	log := context.Log()
	log.Debug("HANDSHAKE SLEEPING")
	time.Sleep(10 * time.Second)

	identity := context.Identity()
	appConfig := context.AppConfig()

	messageGatewayServiceConfig := appConfig.Mgs
	if messageGatewayServiceConfig.Region == "" {
		fetchedRegion, err := identity.Region()
		if err != nil {
			return nil, fmt.Errorf("failed to get region with error: %s", err)
		}
		messageGatewayServiceConfig.Region = fetchedRegion
	}

	if messageGatewayServiceConfig.Endpoint == "" {
		fetchedEndpoint, err := getMgsEndpoint(context, messageGatewayServiceConfig.Region)
		if err != nil {
			return nil, fmt.Errorf("failed to get MessageGatewayService endpoint with error: %s", err)
		}
		messageGatewayServiceConfig.Endpoint = fetchedEndpoint
	}

	connectionTimeout := time.Duration(messageGatewayServiceConfig.StopTimeoutMillis) * time.Millisecond
	mgsService := service.NewService(context, messageGatewayServiceConfig, connectionTimeout)

	instanceID, err := identity.InstanceID()

	if instanceID == "" {
		return nil, fmt.Errorf("no instanceID provided, %s", err)
	}

	dataChannel := &DataChannel{}
	dataChannel.Initialize(
		context,
		mgsService,
		channelId,
		clientId,
		instanceID,
		mgsConfig.RolePublishSubscribe,
		cancelFlag,
		inputStreamMessageHandler)

	streamMessageHandler := func(input []byte) {
		if err := dataChannel.dataChannelIncomingMessageHandler(log, input); err != nil {
			log.Errorf("Invalid message %s\n", err)
		}
	}
	if err := dataChannel.SetWebSocket(context, mgsService, channelId, clientId, streamMessageHandler); err != nil {
		return nil, fmt.Errorf("failed to create websocket for datachannel with error: %s", err)
	}
	if err := dataChannel.Open(log); err != nil {
		return nil, fmt.Errorf("failed to open datachannel with error: %s", err)
	}
	dataChannel.ResendStreamDataMessageScheduler(log)
	return dataChannel, nil
}

// Initialize populates datachannel object.
func (dataChannel *DataChannel) Initialize(context context.T,
	mgsService service.Service,
	sessionId string,
	clientId string,
	instanceId string,
	role string,
	cancelFlag task.CancelFlag,
	inputStreamMessageHandler InputStreamMessageHandler) {

	dataChannel.context = context
	dataChannel.Service = mgsService
	dataChannel.ChannelId = sessionId
	dataChannel.ClientId = clientId
	dataChannel.InstanceId = instanceId
	dataChannel.Role = role
	dataChannel.Pause = false
	dataChannel.ExpectedSequenceNumber = 0
	dataChannel.StreamDataSequenceNumber = 0
	dataChannel.StreamDataSequenceNumberMutex = &sync.Mutex{}
	dataChannel.OutgoingMessageBuffer = ListMessageBuffer{
		list.New(),
		mgsConfig.OutgoingMessageBufferCapacity,
		&sync.Mutex{},
	}
	dataChannel.IncomingMessageBuffer = MapMessageBuffer{
		make(map[int64]StreamingMessage),
		mgsConfig.IncomingMessageBufferCapacity,
		&sync.Mutex{},
	}
	dataChannel.RoundTripTime = float64(mgsConfig.DefaultRoundTripTime)
	dataChannel.RoundTripTimeVariation = mgsConfig.DefaultRoundTripTimeVariation
	dataChannel.RetransmissionTimeout = mgsConfig.DefaultTransmissionTimeout
	dataChannel.wsChannel = &communicator.WebSocketChannel{}
	dataChannel.cancelFlag = cancelFlag
	dataChannel.inputStreamMessageHandler = inputStreamMessageHandler
	dataChannel.handshake = Handshake{
		responseChan:            make(chan bool),
		encryptionConfirmedChan: make(chan bool),
		error:                   nil,
		complete:                false,
		skipped:                 false,
		handshakeEndTime:        time.Now(),
		handshakeStartTime:      time.Now(),
	}
}

// SetWebSocket populates webchannel object.
func (dataChannel *DataChannel) SetWebSocket(context context.T,
	mgsService service.Service,
	sessionId string,
	clientId string,
	onMessageHandler func(input []byte)) error {

	log := context.Log()
	uuid.SwitchFormat(uuid.CleanHyphen)
	requestId := uuid.NewV4().String()

	log.Infof("Setting up datachannel for session: %s, requestId: %s, clientId: %s", sessionId, requestId, clientId)
	tokenValue, err := getDataChannelToken(log, mgsService, sessionId, requestId, clientId)
	if err != nil {
		log.Errorf("Failed to get datachannel token, error: %s", err)
		return err
	}

	onErrorHandler := func(err error) {
		uuid.SwitchFormat(uuid.CleanHyphen)
		requestId := uuid.NewV4().String()
		callable := func() (channel interface{}, err error) {
			tokenValue, err := getDataChannelToken(log, mgsService, sessionId, requestId, clientId)
			if err != nil {
				return dataChannel, err
			}
			dataChannel.wsChannel.SetChannelToken(tokenValue)
			if err = dataChannel.Reconnect(log); err != nil {
				return dataChannel, err
			}
			return dataChannel, nil
		}
		retryer := retry.ExponentialRetryer{
			CallableFunc:        callable,
			GeometricRatio:      mgsConfig.RetryGeometricRatio,
			InitialDelayInMilli: rand.Intn(mgsConfig.DataChannelRetryInitialDelayMillis) + mgsConfig.DataChannelRetryInitialDelayMillis,
			MaxDelayInMilli:     mgsConfig.DataChannelRetryMaxIntervalMillis,
			MaxAttempts:         mgsConfig.DataChannelNumMaxAttempts,
			NonRetryableErrors:  getNonRetryableDataChannelErrors(),
		}
		if _, err := retryer.Call(); err != nil {
			log.Error(err)
		}
	}

	if err := dataChannel.wsChannel.Initialize(context,
		sessionId,
		mgsConfig.DataChannel,
		mgsConfig.RolePublishSubscribe,
		tokenValue,
		mgsService.GetRegion(),
		mgsService.GetV4Signer(),
		onMessageHandler,
		onErrorHandler); err != nil {
		log.Errorf("failed to initialize websocket channel for datachannel, error: %s", err)
		return err
	}
	return nil
}

// Open opens the websocket connection and sends the token for service to acknowledge the connection.
func (dataChannel *DataChannel) Open(log log.T) error {
	// Opens websocket connection
	if err := dataChannel.wsChannel.Open(log, nil); err != nil {
		return fmt.Errorf("failed to connect data channel with error: %s", err)
	}

	// finalize handshake
	uuid.SwitchFormat(uuid.CleanHyphen)
	uid := uuid.NewV4().String()

	openDataChannelInput := service.OpenDataChannelInput{
		MessageSchemaVersion: aws.String(mgsConfig.MessageSchemaVersion),
		RequestId:            aws.String(uid),
		TokenValue:           aws.String(dataChannel.wsChannel.GetChannelToken()),
		ClientInstanceId:     aws.String(dataChannel.InstanceId),
		ClientId:             aws.String(dataChannel.ClientId),
	}
	jsonValue, err := json.Marshal(openDataChannelInput)
	if err != nil {
		return fmt.Errorf("error serializing openDataChannelInput: %s", err)
	}

	return dataChannel.SendMessage(log, jsonValue, websocket.TextMessage)
}

// SendMessage sends a message to the service through datachannel.
func (dataChannel *DataChannel) SendMessage(log log.T, input []byte, inputType int) error {
	return dataChannel.wsChannel.SendMessage(log, input, inputType)
}

// Reconnect reconnects datachannel to service endpoint.
func (dataChannel *DataChannel) Reconnect(log log.T) error {
	log.Debugf("Reconnecting datachannel: %s", dataChannel.ChannelId)

	if err := dataChannel.wsChannel.Close(log); err != nil {
		log.Debugf("Closing datachannel failed with error: %s", err)
	}

	if err := dataChannel.Open(log); err != nil {
		return fmt.Errorf("failed to reconnect datachannel with error: %s", err)
	}

	dataChannel.Pause = false
	log.Debugf("Successfully reconnected to datachannel %s", dataChannel.ChannelId)
	return nil
}

// Close closes datachannel - its web socket connection.
func (dataChannel *DataChannel) Close(log log.T) error {
	log.Infof("Closing datachannel with channel Id %s", dataChannel.ChannelId)
	return dataChannel.wsChannel.Close(log)
}

// PrepareToCloseChannel waits for all messages to be sent to MGS
func (dataChannel *DataChannel) PrepareToCloseChannel(log log.T) {
	done := make(chan bool)
	go func() {
		for dataChannel.OutgoingMessageBuffer.Messages.Len() > 0 {
			time.Sleep(10 * time.Millisecond)
		}
		done <- true
	}()

	select {
	case <-done:
		log.Tracef("Datachannel buffer is empty, datachannel can now be closed")
	case <-time.After(2 * time.Second):
		log.Debugf("Timeout waiting for datachannel buffer to empty.")
	}
}

// SendStreamDataMessage sends a data message in a form of AgentMessage for streaming.
func (dataChannel *DataChannel) SendStreamDataMessage(log log.T, payloadType mgsContracts.PayloadType, inputData []byte) (err error) {
	if len(inputData) == 0 {
		log.Debugf("Ignoring empty stream data payload. PayloadType: %d", payloadType)
		return nil
	}

	// If encryption has been enabled, encrypt the payload
	if dataChannel.encryptionEnabled && (payloadType == mgsContracts.Output || payloadType == mgsContracts.StdErr || payloadType == mgsContracts.ExitCode) {
		if inputData, err = dataChannel.blockCipher.EncryptWithAESGCM(inputData); err != nil {
			return fmt.Errorf("error encrypting stream data message sequence %d, err: %v", dataChannel.StreamDataSequenceNumber, err)
		}
	}

	// StreamDataSequenceNumber only changed in the code block below
	dataChannel.StreamDataSequenceNumberMutex.Lock()
	defer dataChannel.StreamDataSequenceNumberMutex.Unlock()

	var flag uint64 = 0
	if dataChannel.StreamDataSequenceNumber == 0 {
		flag = 1
	}

	uuid.SwitchFormat(uuid.CleanHyphen)
	messageId := uuid.NewV4()
	agentMessage := &mgsContracts.AgentMessage{
		MessageType:    mgsContracts.OutputStreamDataMessage,
		SchemaVersion:  1,
		CreatedDate:    uint64(time.Now().UnixNano() / 1000000),
		SequenceNumber: dataChannel.StreamDataSequenceNumber,
		Flags:          flag,
		MessageId:      messageId,
		PayloadType:    uint32(payloadType),
		Payload:        inputData,
	}
	msg, err := agentMessage.Serialize(log)
	if err != nil {
		return fmt.Errorf("cannot serialize StreamData message %v", agentMessage)
	}

	if dataChannel.Pause {
		log.Tracef("Sending stream data message has been paused, saving stream data message sequence %d to local map: ", dataChannel.StreamDataSequenceNumber)
	} else {
		log.Tracef("Send stream data message sequence number %d", dataChannel.StreamDataSequenceNumber)
		if err = dataChannel.SendMessage(log, msg, websocket.BinaryMessage); err != nil {
			log.Errorf("Error sending stream data message %v", err)
		}
	}

	streamingMessage := StreamingMessage{
		msg,
		dataChannel.StreamDataSequenceNumber,
		time.Now(),
	}

	log.Tracef("Add stream data to OutgoingMessageBuffer. Sequence Number: %d", streamingMessage.SequenceNumber)
	dataChannel.AddDataToOutgoingMessageBuffer(streamingMessage)
	dataChannel.StreamDataSequenceNumber = dataChannel.StreamDataSequenceNumber + 1
	return nil
}

// ResendStreamDataMessageScheduler spawns a separate go thread which keeps checking OutgoingMessageBuffer at fixed interval
// and resends first message if time elapsed since lastSentTime of the message is more than acknowledge wait time
func (dataChannel *DataChannel) ResendStreamDataMessageScheduler(log log.T) error {
	go func() {
		defer func() {
			if r := recover(); r != nil {
				log.Errorf("Resend stream data message scheduler panic: %v", r)
				log.Errorf("Stacktrace:\n%s", debug.Stack())
			}
		}()
		for {
			time.Sleep(mgsConfig.ResendSleepInterval)
			if dataChannel.Pause {
				log.Tracef("Resend stream data message has been paused")
				continue
			}
			streamMessageElement := dataChannel.OutgoingMessageBuffer.Messages.Front()
			if streamMessageElement == nil {
				continue
			}

			streamMessage := streamMessageElement.Value.(StreamingMessage)
			if time.Since(streamMessage.LastSentTime) > dataChannel.RetransmissionTimeout {
				log.Tracef("Resend stream data message: %d", streamMessage.SequenceNumber)
				if err := dataChannel.SendMessage(log, streamMessage.Content, websocket.BinaryMessage); err != nil {
					log.Errorf("Unable to send stream data message: %s", err)
				}
				streamMessage.LastSentTime = time.Now()
				streamMessageElement.Value = streamMessage
			}
		}
	}()
	return nil
}

// ProcessAcknowledgedMessage processes acknowledge messages by deleting them from OutgoingMessageBuffer.
func (dataChannel *DataChannel) ProcessAcknowledgedMessage(log log.T, acknowledgeMessageContent mgsContracts.AcknowledgeContent) {
	acknowledgeSequenceNumber := acknowledgeMessageContent.SequenceNumber
	for streamMessageElement := dataChannel.OutgoingMessageBuffer.Messages.Front(); streamMessageElement != nil; streamMessageElement = streamMessageElement.Next() {
		streamMessage := streamMessageElement.Value.(StreamingMessage)
		if streamMessage.SequenceNumber == acknowledgeSequenceNumber {

			//Calculate retransmission timeout based on latest round trip time of message
			dataChannel.calculateRetransmissionTimeout(log, streamMessage)

			log.Tracef("Delete stream data from OutgoingMessageBuffer. Sequence Number: %d", streamMessage.SequenceNumber)
			dataChannel.RemoveDataFromOutgoingMessageBuffer(streamMessageElement)
			break
		}
	}
}

// SendAcknowledgeMessage sends acknowledge message for stream data over data channel
func (dataChannel *DataChannel) SendAcknowledgeMessage(log log.T, streamDataMessage mgsContracts.AgentMessage) error {
	dataStreamAcknowledgeContent := &mgsContracts.AcknowledgeContent{
		MessageType:         streamDataMessage.MessageType,
		MessageId:           streamDataMessage.MessageId.String(),
		SequenceNumber:      streamDataMessage.SequenceNumber,
		IsSequentialMessage: true,
	}

	acknowledgeContentBytes, err := dataStreamAcknowledgeContent.Serialize(log)
	if err != nil {
		// should not happen
		log.Errorf("Cannot serialize Acknowledge message err: %v", err)
		return err
	}

	log.Tracef("Send %s message for stream data: %d", mgsContracts.AcknowledgeMessage, streamDataMessage.SequenceNumber)
	if err := dataChannel.sendAgentMessage(log, mgsContracts.AcknowledgeMessage, acknowledgeContentBytes); err != nil {
		return err
	}
	return nil
}

// SendAgentSessionStateMessage sends agent session state to MGS
func (dataChannel *DataChannel) SendAgentSessionStateMessage(log log.T, sessionStatus mgsContracts.SessionStatus) error {
	agentSessionStateContent := &mgsContracts.AgentSessionStateContent{
		SchemaVersion: schemaVersion,
		SessionState:  string(sessionStatus),
		SessionId:     dataChannel.ChannelId,
	}

	var agentSessionStateContentBytes []byte
	var err error
	if agentSessionStateContentBytes, err = json.Marshal(agentSessionStateContent); err != nil {
		log.Errorf("Cannot serialize AgentSessionState message err: %v", err)
		return err
	}

	log.Debugf("Send %s message with session status %s", mgsContracts.AgentSessionState, string(sessionStatus))
	if err := dataChannel.sendAgentMessage(log, mgsContracts.AgentSessionState, agentSessionStateContentBytes); err != nil {
		return err
	}
	return nil
}

// sendAgentMessage sends agent message for given messageType and content
func (dataChannel *DataChannel) sendAgentMessage(log log.T, messageType string, messageContent []byte) error {
	uuid.SwitchFormat(uuid.CleanHyphen)
	messageId := uuid.NewV4()
	agentMessage := &mgsContracts.AgentMessage{
		MessageType:    messageType,
		SchemaVersion:  schemaVersion,
		CreatedDate:    uint64(time.Now().UnixNano() / 1000000),
		SequenceNumber: sequenceNumber,
		Flags:          messageFlags,
		MessageId:      messageId,
		Payload:        messageContent,
	}

	msg, err := agentMessage.Serialize(log)
	if err != nil {
		log.Errorf("Cannot serialize agent message err: %v", err)
		return err
	}

	err = dataChannel.SendMessage(log, msg, websocket.BinaryMessage)
	if err != nil {
		log.Errorf("Error sending %s message %v", messageType, err)
		return err
	}
	return nil
}

// AddDataToOutgoingMessageBuffer adds given message at the end of OutputMessageBuffer if it has capacity.
func (dataChannel *DataChannel) AddDataToOutgoingMessageBuffer(streamMessage StreamingMessage) {
	if dataChannel.OutgoingMessageBuffer.Messages.Len() == dataChannel.OutgoingMessageBuffer.Capacity {
		return
	}
	dataChannel.OutgoingMessageBuffer.Mutex.Lock()
	dataChannel.OutgoingMessageBuffer.Messages.PushBack(streamMessage)
	dataChannel.OutgoingMessageBuffer.Mutex.Unlock()
}

// RemoveDataFromOutgoingMessageBuffer removes given element from OutgoingMessageBuffer.
func (dataChannel *DataChannel) RemoveDataFromOutgoingMessageBuffer(streamMessageElement *list.Element) {
	dataChannel.OutgoingMessageBuffer.Mutex.Lock()
	dataChannel.OutgoingMessageBuffer.Messages.Remove(streamMessageElement)
	dataChannel.OutgoingMessageBuffer.Mutex.Unlock()
}

// AddDataToIncomingMessageBuffer adds given message to IncomingMessageBuffer if it has capacity.
func (dataChannel *DataChannel) AddDataToIncomingMessageBuffer(streamMessage StreamingMessage) {
	if len(dataChannel.IncomingMessageBuffer.Messages) == dataChannel.IncomingMessageBuffer.Capacity {
		return
	}
	dataChannel.IncomingMessageBuffer.Mutex.Lock()
	dataChannel.IncomingMessageBuffer.Messages[streamMessage.SequenceNumber] = streamMessage
	dataChannel.IncomingMessageBuffer.Mutex.Unlock()
}

// RemoveDataFromIncomingMessageBuffer removes given sequence number message from IncomingMessageBuffer.
func (dataChannel *DataChannel) RemoveDataFromIncomingMessageBuffer(sequenceNumber int64) {
	dataChannel.IncomingMessageBuffer.Mutex.Lock()
	delete(dataChannel.IncomingMessageBuffer.Messages, sequenceNumber)
	dataChannel.IncomingMessageBuffer.Mutex.Unlock()
}

// dataChannelIncomingMessageHandler deserialize incoming message and
// processes that data based on MessageType.
func (dataChannel *DataChannel) dataChannelIncomingMessageHandler(log log.T, rawMessage []byte) error {

	streamDataMessage := &mgsContracts.AgentMessage{}
	if err := streamDataMessage.Deserialize(log, rawMessage); err != nil {
		log.Errorf("Cannot deserialize raw message, err: %v.", err)
		return err
	}

	if err := streamDataMessage.Validate(); err != nil {
		log.Errorf("Invalid StreamDataMessage, err: %v.", err)
		return err
	}

	switch streamDataMessage.MessageType {
	case mgsContracts.InputStreamDataMessage:
		return dataChannel.handleStreamDataMessage(log, *streamDataMessage, rawMessage)
	case mgsContracts.AcknowledgeMessage:
		return dataChannel.handleAcknowledgeMessage(log, *streamDataMessage)
	case mgsContracts.ChannelClosedMessage:
		return dataChannel.handleChannelClosedMessage(log, *streamDataMessage)
	case mgsContracts.PausePublicationMessage:
		dataChannel.handlePausePublicationMessage(log, *streamDataMessage)
		return nil
	case mgsContracts.StartPublicationMessage:
		dataChannel.handleStartPublicationMessage(log, *streamDataMessage)
		return nil
	default:
		log.Warnf("Invalid message type received: %s", streamDataMessage.MessageType)
	}

	return nil
}

// calculateRetransmissionTimeout calculates message retransmission timeout value based on round trip time on given message.
func (dataChannel *DataChannel) calculateRetransmissionTimeout(log log.T, streamingMessage StreamingMessage) {
	newRoundTripTime := float64(time.Since(streamingMessage.LastSentTime))

	dataChannel.RoundTripTimeVariation = ((1 - mgsConfig.RTTVConstant) * dataChannel.RoundTripTimeVariation) +
		(mgsConfig.RTTVConstant * math.Abs(dataChannel.RoundTripTime-newRoundTripTime))

	dataChannel.RoundTripTime = ((1 - mgsConfig.RTTConstant) * dataChannel.RoundTripTime) +
		(mgsConfig.RTTConstant * newRoundTripTime)

	dataChannel.RetransmissionTimeout = time.Duration(dataChannel.RoundTripTime +
		math.Max(float64(mgsConfig.ClockGranularity), float64(4*dataChannel.RoundTripTimeVariation)))

	// Ensure RetransmissionTimeout do not exceed maximum timeout defined
	if dataChannel.RetransmissionTimeout > mgsConfig.MaxTransmissionTimeout {
		dataChannel.RetransmissionTimeout = mgsConfig.MaxTransmissionTimeout
	}

	log.Tracef("Retransmission timeout calculated in mills. "+
		"AcknowledgeMessageSequenceNumber: %d, RoundTripTime: %d, RoundTripTimeVariation: %d, RetransmissionTimeout: %d",
		streamingMessage.SequenceNumber,
		dataChannel.RoundTripTime,
		dataChannel.RoundTripTimeVariation,
		dataChannel.RetransmissionTimeout/time.Millisecond)
}

// handleStreamDataMessage handles incoming stream data messages by processing the payload and updating expectedSequenceNumber.
func (dataChannel *DataChannel) handleStreamDataMessage(log log.T,
	streamDataMessage mgsContracts.AgentMessage,
	rawMessage []byte) (err error) {

	dataChannel.Pause = false
	// On receiving expected stream data message, send acknowledgement, process it and increment expected sequence number by 1.
	// Further process messages from IncomingMessageBuffer
	if streamDataMessage.SequenceNumber == dataChannel.ExpectedSequenceNumber {
		log.Tracef("Process new incoming stream data message. Sequence Number: %d", streamDataMessage.SequenceNumber)
		if err = dataChannel.processStreamDataMessage(log, streamDataMessage); err != nil {
			if errors.Is(err, mgsContracts.ErrHandlerNotReady) {
				return nil
			}
			log.Errorf("Unable to process stream data payload %v, err: %v.", streamDataMessage, err)
			return err
		}

		if err = dataChannel.SendAcknowledgeMessage(log, streamDataMessage); err != nil {
			return err
		}

		// Message is acknowledged so increment expected sequence number
		dataChannel.ExpectedSequenceNumber = dataChannel.ExpectedSequenceNumber + 1
		return dataChannel.processIncomingMessageBufferItems(log)

	} else if streamDataMessage.SequenceNumber > dataChannel.ExpectedSequenceNumber {
		// If incoming message sequence number is greater than expected sequence number and IncomingMessageBuffer has capacity,
		// add message to IncomingMessageBuffer and send acknowledgement
		log.Debugf("Unexpected sequence message received. Received Sequence Number: %d. Expected Sequence Number: %d",
			streamDataMessage.SequenceNumber, dataChannel.ExpectedSequenceNumber)

		if len(dataChannel.IncomingMessageBuffer.Messages) < dataChannel.IncomingMessageBuffer.Capacity {
			if err = dataChannel.SendAcknowledgeMessage(log, streamDataMessage); err != nil {
				return err
			}

			streamingMessage := StreamingMessage{
				rawMessage,
				streamDataMessage.SequenceNumber,
				time.Now(),
			}

			//Add message to buffer for future processing
			log.Debugf("Add stream data to IncomingMessageBuffer. Sequence Number: %d", streamDataMessage.SequenceNumber)
			dataChannel.AddDataToIncomingMessageBuffer(streamingMessage)
		}
	} else {
		log.Tracef("Discarding already processed message. Received Sequence Number: %d. Expected Sequence Number: %d",
			streamDataMessage.SequenceNumber, dataChannel.ExpectedSequenceNumber)
	}
	return nil
}

// handleAcknowledgeMessage deserialize acknowledge content and process it.
func (dataChannel *DataChannel) handleAcknowledgeMessage(log log.T, streamDataMessage mgsContracts.AgentMessage) (err error) {
	dataChannel.Pause = false
	acknowledgeMessage := &mgsContracts.AcknowledgeContent{}
	if err = acknowledgeMessage.Deserialize(log, streamDataMessage); err != nil {
		log.Errorf("Cannot deserialize payload to AcknowledgeMessage: %s, err: %v.", string(streamDataMessage.Payload), err)
		return err
	}

	dataChannel.ProcessAcknowledgedMessage(log, *acknowledgeMessage)
	return nil
}

// handleChannelClosedMessage deserialize channel_closed message content and terminate the session.
func (dataChannel *DataChannel) handleChannelClosedMessage(log log.T, streamDataMessage mgsContracts.AgentMessage) (err error) {
	channelClosedMessage := &mgsContracts.ChannelClosed{}
	if err = channelClosedMessage.Deserialize(log, streamDataMessage); err != nil {
		log.Errorf("Cannot deserialize payload to ChannelClosed message: %s, err: %v.", string(streamDataMessage.Payload), err)
		return err
	}

	log.Debugf("Processing terminate session request: messageId %s, sessionId %s", channelClosedMessage.MessageId, channelClosedMessage.SessionId)
	dataChannel.cancelFlag.Set(task.Canceled)

	return nil
}

// handlePausePublicationMessage sets pause status of datachannel to true.
func (dataChannel *DataChannel) handlePausePublicationMessage(log log.T, streamDataMessage mgsContracts.AgentMessage) {
	dataChannel.Pause = true
	log.Debugf("Processed %s message. Datachannel pause status set to %s", streamDataMessage.MessageType, dataChannel.Pause)
}

// handleStartPublicationMessage sets pause status of datachannel to false.
func (dataChannel *DataChannel) handleStartPublicationMessage(log log.T, streamDataMessage mgsContracts.AgentMessage) {
	dataChannel.Pause = false
	log.Debugf("Processed %s message. Datachannel pause status set to %s", streamDataMessage.MessageType, dataChannel.Pause)
}

// processIncomingMessageBufferItems checks if new expected sequence stream data is present in IncomingMessageBuffer.
// If so process it and increment expected sequence number.
// Repeat until expected sequence stream data is not found in IncomingMessageBuffer.
func (dataChannel *DataChannel) processIncomingMessageBufferItems(log log.T) (err error) {
	for {
		bufferedStreamMessage := dataChannel.IncomingMessageBuffer.Messages[dataChannel.ExpectedSequenceNumber]
		if bufferedStreamMessage.Content != nil {
			log.Debugf("Process stream data message from IncomingMessageBuffer. "+
				"Sequence Number: %d", bufferedStreamMessage.SequenceNumber)

			streamDataMessage := &mgsContracts.AgentMessage{}

			if err = streamDataMessage.Deserialize(log, bufferedStreamMessage.Content); err != nil {
				log.Errorf("Cannot deserialize raw message: %d, err: %v.", bufferedStreamMessage.SequenceNumber, err)
				return err
			}
			if err = dataChannel.processStreamDataMessage(log, *streamDataMessage); err != nil {
				log.Errorf("Unable to process stream data payload, err: %v.", err)
				return err
			}

			dataChannel.ExpectedSequenceNumber = dataChannel.ExpectedSequenceNumber + 1

			log.Debugf("Delete stream data from IncomingMessageBuffer. Sequence Number: %d", bufferedStreamMessage.SequenceNumber)
			dataChannel.RemoveDataFromIncomingMessageBuffer(bufferedStreamMessage.SequenceNumber)
		} else {
			break
		}
	}
	return nil
}

// processStreamDataMessage gets called for all messages of type OutputStreamDataMessage
func (dataChannel *DataChannel) processStreamDataMessage(log log.T, streamDataMessage mgsContracts.AgentMessage) (err error) {

	if dataChannel.encryptionEnabled && streamDataMessage.PayloadType == uint32(mgsContracts.Output) {
		if streamDataMessage.Payload, err = dataChannel.blockCipher.DecryptWithAESGCM(streamDataMessage.Payload); err != nil {
			return fmt.Errorf("Error decrypting stream data message sequence %d, err: %v", streamDataMessage.SequenceNumber, err)
		}
	}

	switch mgsContracts.PayloadType(streamDataMessage.PayloadType) {
	case mgsContracts.HandshakeResponse:
		{
			// PayloadType is HandshakeResponse so we call our own handler instead of the plugin handler
			if err = dataChannel.handleHandshakeResponse(log, streamDataMessage); err != nil {
				return fmt.Errorf("processing of HandshakeResponse message failed, %v", err)
			}
		}
	case mgsContracts.EncChallengeResponse:
		{
			// PayloadType is HandshakeResponse so we call our own handler instead of the plugin handler
			if err = dataChannel.handleEncryptionChallengeResponse(log, streamDataMessage); err != nil {
				return fmt.Errorf("processing of EncryptionChallengeReponse message failed, %v", err)
			}
		}
	default:
		// Ignore stream data message if handshake is neither skipped nor completed
		if !dataChannel.handshake.skipped && !dataChannel.handshake.complete {
			log.Tracef("Handshake still in progress, ignore stream data message sequence %d", streamDataMessage.SequenceNumber)
			return nil
		}

		if err = dataChannel.inputStreamMessageHandler(log, streamDataMessage); err != nil {
			return err
		}
	}

	return nil
}

// handleHandshakeResponse is the handler for payload type HandshakeResponse
func (dataChannel *DataChannel) handleHandshakeResponse(log log.T, streamDataMessage mgsContracts.AgentMessage) error {
	log.Debug("Received Handshake Response.")
	var handshakeResponse mgsContracts.HandshakeResponsePayload
	if err := json.Unmarshal(streamDataMessage.Payload, &handshakeResponse); err != nil {
		return fmt.Errorf("Unmarshalling of HandshakeResponse message failed, %s", err)
	}

	for _, action := range handshakeResponse.ProcessedClientActions {
		var err error
		if action.ActionStatus != mgsContracts.Success {
			err = fmt.Errorf("%s failed on client with status %v error: %s",
				action.ActionType, action.ActionStatus, action.Error)
		} else {
			switch action.ActionType {
			case mgsContracts.SecureSession:
				var resp mgsContracts.SecureSessionResponse
				if err = json.Unmarshal(action.ActionResult, &resp); err != nil {
					err = fmt.Errorf("failed to unmarshal action to SecureSessionResponse: %v", err)
					break
				}

				// decode the client share
				var clientShareBytes []byte
				clientShareBytes, err = base64.StdEncoding.DecodeString(resp.ClientShare)
				if err != nil {
					err = fmt.Errorf("failed to decode server share: %v", err)
					log.Error(err)
					break
				}

				clientx, clienty := elliptic.UnmarshalCompressed(elliptic.P384(), clientShareBytes)

				// check that the client share is on the curve
				if !elliptic.P384().IsOnCurve(clientx, clienty) {
					err = fmt.Errorf("client share is not on the curve")
					log.Error(err)
					break
				}

				// generate and store the shared secret
				ss, _ := elliptic.P384().ScalarMult(clientx, clienty, dataChannel.state.agentSecret) // TODO: Double check it's fine to just use x
				dataChannel.state.sharedSecret = ss.Bytes()

				// hash the shared secret to obtain the session identifier
				hash := sha512.New384()
				hash.Write(dataChannel.state.sharedSecret)
				dataChannel.state.sessionID = hash.Sum(nil)

				log.Debugf("agent computed session ID: %v", base64.StdEncoding.EncodeToString(dataChannel.state.sessionID))
				// decode the session ID
				var sessionIDBytes []byte
				sessionIDBytes, err = base64.StdEncoding.DecodeString(resp.SessionID)
				if err != nil {
					err = fmt.Errorf("failed to decode server session id: %v", err)
					log.Error(err)
					break
				}

				if !bytes.Equal(dataChannel.state.sessionID, sessionIDBytes) {
					err = fmt.Errorf("session ID mismatch: session ID %s does not match client session ID %s", sessionIDBytes, dataChannel.state.sessionID)
					log.Error(err)
					break
				}

				// use the shared secret to generate read and write keys
				hash512 := sha512.New
				hkPRK := hkdf.Extract(hash512, dataChannel.state.sharedSecret, nil) //it's pretty complicated what using a salt with HKDF means, we should double check this

				const keySize = 32
				dataChannel.state.agentReadKey = make([]byte, keySize)
				dataChannel.state.agentWriteKey = make([]byte, keySize)

				hkdf.Expand(hash512, hkPRK, []byte("C")).Read(dataChannel.state.agentReadKey)
				hkdf.Expand(hash512, hkPRK, []byte("S")).Read(dataChannel.state.agentWriteKey)
				agentReadKey := dataChannel.state.agentReadKey
				encodedAgentReadKey := base64.RawStdEncoding.EncodeToString(agentReadKey)
				log.Debugf("agent read key: %s", encodedAgentReadKey)

				var encryptionContext map[string]*string
				encryptedReadKey, err := dataChannel.kmsService.Encrypt(resp.LogLTKeyARN, dataChannel.state.agentReadKey, encryptionContext)
				if err != nil {
					panic(fmt.Errorf("failed to encrypt agent read key via KMS: %v", err))
				}
				encodedReadKey := base64.StdEncoding.EncodeToString(encryptedReadKey)
				log.Infof("encrypted base-64-encoded agent read key: %s", encodedReadKey)

				dataChannel.encryptedAgentReadKey = encodedReadKey
				dataChannel.encryptedClientReadKey = resp.EncryptedClientReadKey
				dataChannel.logLTKeyARN = resp.LogLTKeyARN

				dataChannel.encryptionEnabled = true

				if err := dataChannel.blockCipher.UpdateEncryptionKey(log, append(dataChannel.state.agentReadKey, dataChannel.state.agentWriteKey...), "", ""); err != nil {
					err = fmt.Errorf("failed to update block cipher: %v", err)
					log.Error(err)
					break
				}
			case mgsContracts.KMSEncryption:
				err = dataChannel.finalizeKMSEncryption(log, action.ActionResult)
				break
			case mgsContracts.SessionType:
				break
			default:
				log.Warnf("Unknown handshake client action found, %s", action.ActionType)
			}
		}
		if err != nil {
			log.Error(err)
			// Cancel the session because handshake FAILED
			dataChannel.cancelFlag.Set(task.Canceled)
			// Set handshake error. Initiate handshake waits on handshake.responseChan and will return this error when channel returns.
			dataChannel.handshake.error = err
		}
	}
	dataChannel.handshake.clientVersion = handshakeResponse.ClientVersion
	log.Infof("Client side session manager plugin version is: %s", handshakeResponse.ClientVersion)
	dataChannel.handshake.responseChan <- true
	return nil
}

// handleEncryptionChallengeResponse is the handler for payload type EncryptionChallengeRequest
func (dataChannel *DataChannel) handleEncryptionChallengeResponse(log log.T, streamDataMessage mgsContracts.AgentMessage) error {
	log.Debug("Received Encryption Challenge Response.")
	var encChallengeResponse mgsContracts.EncryptionChallengeResponse
	if err := json.Unmarshal(streamDataMessage.Payload, &encChallengeResponse); err != nil {
		return fmt.Errorf("Unmarshalling of EncryptionChallengeResponse message failed, %s AND %v", streamDataMessage.Payload, err)
	}

	log.Info("Verifying encryption challenge..")
	responseChallenge, err := dataChannel.blockCipher.DecryptWithAESGCM(encChallengeResponse.Challenge)
	if err != nil {
		dataChannel.handshake.error = err
		return err
	}
	if !bytes.Equal(responseChallenge, dataChannel.handshake.encryptionChallenge) {
		err = fmt.Errorf("Encryption challenge does not match!")
		dataChannel.handshake.error = err
		return err
	}
	if err != nil {
		dataChannel.handshake.encryptionConfirmedChan <- false
	} else {
		dataChannel.handshake.encryptionConfirmedChan <- true
	}
	return nil
}

// SkipHandshake is used to skip handshake if the plugin decides it is not necessary
func (dataChannel *DataChannel) SkipHandshake(log log.T) {
	log.Info("Skipping handshake.")
	dataChannel.handshake.skipped = true
}

// finalizeKMSEncryption parses encryption parameters returned from the client and sets up encryption
func (dataChannel *DataChannel) finalizeKMSEncryption(log log.T, actionResult json.RawMessage) error {
	encryptionResponse := mgsContracts.KMSEncryptionResponse{}

	if err := json.Unmarshal(actionResult, &encryptionResponse); err != nil {
		return err
	}

	sessionId := dataChannel.ChannelId // ChannelId is SessionId
	if err := dataChannel.blockCipher.UpdateEncryptionKey(log, encryptionResponse.KMSCipherTextKey, sessionId, dataChannel.InstanceId); err != nil {
		return fmt.Errorf("Fetching data key failed: %s", err)
	}
	dataChannel.encryptionEnabled = true
	return nil
}

type blockCipher struct {
	cipherTextKey    []byte
	encryptionKey    []byte
	decryptionKey    []byte
	encryptionCipher cipher.AEAD
	decryptionCipher cipher.AEAD
}

var _ crypto.IBlockCipher = (*blockCipher)(nil)

func (bc *blockCipher) UpdateEncryptionKey(log log.T, cipherTextBlob []byte, _, _ string) error {
	const keyLen = 32 // key length in bytes
	bc.cipherTextKey = cipherTextBlob
	bc.decryptionKey = cipherTextBlob[:keyLen]
	bc.encryptionKey = cipherTextBlob[keyLen:]
	log.Debugf("ENCRYPTION KEY: %x", bc.encryptionKey)
	log.Debugf("DECRYPTION KEY: %x", bc.decryptionKey)
	enc, err := getAEAD(bc.encryptionKey)
	bc.encryptionCipher = enc
	if err != nil {
		return fmt.Errorf("failed to get encryption cipher: %v", err)
	}
	dec, err := getAEAD(bc.decryptionKey)
	bc.decryptionCipher = dec
	if err != nil {
		return fmt.Errorf("failed to get decryption cipher: %v", err)
	}

	return nil
}

const nonceSize = 12

// EncryptWithGCM encrypts plain text using AES block cipher GCM mode
func (blockCipher *blockCipher) EncryptWithAESGCM(plainText []byte) (cipherText []byte, err error) {
	var aesgcm = blockCipher.encryptionCipher

	cipherText = make([]byte, nonceSize+len(plainText))
	nonce := make([]byte, nonceSize)
	if _, err := io.ReadFull(cryptoRand.Reader, nonce); err != nil {
		return nil, fmt.Errorf("failed to generate nonce for encryption: %v", err)
	}

	// Encrypt plain text using given key and newly generated nonce
	cipherTextWithoutNonce := aesgcm.Seal(nil, nonce, plainText, nil)

	// Append nonce to the beginning of the cipher text to be used while decrypting
	cipherText = append(cipherText[:nonceSize], nonce...)
	cipherText = append(cipherText[nonceSize:], cipherTextWithoutNonce...)
	return cipherText, nil
}

// DecryptWithGCM decrypts cipher text using AES block cipher GCM mode
func (blockCipher *blockCipher) DecryptWithAESGCM(cipherText []byte) (plainText []byte, err error) {
	var aesgcm = blockCipher.decryptionCipher

	// Pull the nonce out of the cipherText
	nonce := cipherText[:nonceSize]
	cipherTextWithoutNonce := cipherText[nonceSize:]

	// Decrypt just the actual cipherText using nonce extracted above
	if plainText, err = aesgcm.Open(nil, nonce, cipherTextWithoutNonce, nil); err != nil {
		return nil, fmt.Errorf("failed to decrypt encrypted text: %v", err)
	}
	return plainText, nil
}

// GetCipherTextKey returns cipherTextKey from BlockCipher
func (blockCipher *blockCipher) GetCipherTextKey() []byte {
	return blockCipher.cipherTextKey
}

// GetKMSKeyId returns kmsKeyId from BlockCipher
func (blockCipher *blockCipher) GetKMSKeyId() string {
	return ""
}

// getAEAD gets AEAD which is a GCM cipher mode providing authenticated encryption with associated data
func getAEAD(plainTextKey []byte) (aesgcm cipher.AEAD, err error) {
	var block cipher.Block
	if block, err = aes.NewCipher(plainTextKey); err != nil {
		return nil, fmt.Errorf("error creating NewCipher, %v", err)
	}

	if aesgcm, err = cipher.NewGCM(block); err != nil {
		return nil, fmt.Errorf("error creating NewGCM, %v", err)
	}

	return aesgcm, nil
}

// var newBlockCipher = func(context context.T, kmsKeyId string) (blockCipher crypto.IBlockCipher, err error) {
// 	return crypto.NewBlockCipher(context, kmsKeyId)
// }

// PerformHandshake performs handshake to share version string and encryption information with clients like cli/console
func (dataChannel *DataChannel) PerformHandshake(log log.T,
	kmsKeyId string,
	encryptionEnabled bool,
	sessionTypeRequest mgsContracts.SessionTypeRequest) (err error) {

	if encryptionEnabled {
		// if dataChannel.blockCipher, err = newBlockCipher(dataChannel.context, kmsKeyId); err != nil {
		// 	return fmt.Errorf("Initializing BlockCipher failed: %s", err)
		// }
		log.Info("Encryption enabled: initializing block cipher")
		dataChannel.blockCipher = &blockCipher{}
	}

	dataChannel.handshake.handshakeStartTime = time.Now()
	dataChannel.encryptionEnabled = encryptionEnabled

	log.Info("Initiating Handshake")
	handshakeRequestPayload :=
		dataChannel.buildHandshakeRequestPayload(log, dataChannel.encryptionEnabled, sessionTypeRequest)
	if err := dataChannel.sendHandshakeRequest(log, handshakeRequestPayload); err != nil {
		return err
	}

	// Block until handshake response is received or handshake times out
	select {
	case <-dataChannel.handshake.responseChan:
		{
			if dataChannel.handshake.error != nil {
				return dataChannel.handshake.error
			}
		}
	case <-time.After(handshakeTimeout):
		{
			// If handshake times out here this usually means that the client does not understand handshake or something
			// failed critically when processing handshake request.
			return errors.New("Handshake timed out. Please ensure that you have the latest version of the session manager plugin.")
		}
	}

	// If encryption was enabled send encryption challenge and block until challenge is received
	if dataChannel.encryptionEnabled {
		dataChannel.sendEncryptionChallenge(log)
		select {
		case <-dataChannel.handshake.encryptionConfirmedChan:
			if dataChannel.handshake.error != nil {
				return dataChannel.handshake.error
			}
			log.Info("Encryption challenge confirmed.")
		case <-time.After(handshakeTimeout):
			{
				// If handshake times out here this means the cli is too old and does not understand handshake protocol.
				return errors.New("Timed out waiting for encryption challenge.")
			}
		}
	}

	dataChannel.handshake.handshakeEndTime = time.Now()
	handshakeCompletePayload := dataChannel.buildHandshakeCompletePayload(log)
	if err := dataChannel.sendHandshakeComplete(log, handshakeCompletePayload); err != nil {
		return err
	}
	dataChannel.handshake.complete = true
	log.Info("Handshake successfully completed.")
	return
}

// buildHandshakeRequestPayload builds payload for HandshakeRequest
func (dataChannel *DataChannel) buildHandshakeRequestPayload(log log.T,
	encryptionRequested bool,
	request mgsContracts.SessionTypeRequest) mgsContracts.HandshakeRequestPayload {

	handshakeRequest := mgsContracts.HandshakeRequestPayload{}
	handshakeRequest.AgentVersion = version.Version
	handshakeRequest.RequestedClientActions = []mgsContracts.RequestedClientAction{
		{
			ActionType:       mgsContracts.SessionType,
			ActionParameters: request,
		}}
	if encryptionRequested {
		// Generate the secret using secure randomness from rand
		agentSecret, x, y, err := elliptic.GenerateKey(elliptic.P384(), cryptoRand.Reader)
		if err != nil {
			log.Errorf("failed to generate client secret: %v", err)
			panic(err)
		}

		dataChannel.state.agentSecret = agentSecret

		// Base64 encode the public part and put it in the message
		agentShare := elliptic.MarshalCompressed(elliptic.P384(), x, y)
		compressedPublic := base64.StdEncoding.EncodeToString(agentShare)

		dataChannel.kmsService, err = crypto.NewKMSService(dataChannel.context)
		if err != nil {
			err := fmt.Errorf("failed to initialize KMS service: %v", err)
			log.Error(err)
			panic(err)
		}

		metadata, err := dataChannel.kmsService.CreateKeyAssymetric()
		if err != nil {
			err := fmt.Errorf("failed to create agent LTK: %v", err)
			log.Error(err)
			panic(err)
		}

		if metadata.Arn == nil {
			err := fmt.Errorf("asymmetric key ARN is nil, metadata: %+v", metadata)
			log.Error(err)
			panic(err)
		}

		dataChannel.agentLTKeyARN = *metadata.Arn

		sig, err := dataChannel.kmsService.Sign(dataChannel.agentLTKeyARN, agentShare)
		if err != nil {
			err := fmt.Errorf("failed to sign agent share: %v", err)
			log.Error(err)
			panic(err)
		}

		log.Debugf("agent signed keyshare: %x", sig)

		req := mgsContracts.SecureSessionRequest{
			Version:        1,
			ShareAlgorithm: "P384",
			AgentShare:     compressedPublic,
			Signature:      base64.StdEncoding.EncodeToString(sig),
			AgentLTKeyARN:  dataChannel.agentLTKeyARN,
		}

		log.Debugf("client generated SecureSessionRequest: %+v", req)

		handshakeRequest.RequestedClientActions = append(handshakeRequest.RequestedClientActions, mgsContracts.RequestedClientAction{
			ActionType:       mgsContracts.SecureSession,
			ActionParameters: req,
		})
		// handshakeRequest.RequestedClientActions = append(handshakeRequest.RequestedClientActions,
		// 	mgsContracts.RequestedClientAction{
		// 		ActionType: mgsContracts.KMSEncryption,
		// 		ActionParameters: mgsContracts.KMSEncryptionRequest{
		// 			KMSKeyID: dataChannel.blockCipher.GetKMSKeyId(),
		// 		}})
	}

	return handshakeRequest
}

// buildHandshakeCompletePayload builds payload for HandshakeComplete
func (dataChannel *DataChannel) buildHandshakeCompletePayload(log log.T) mgsContracts.HandshakeCompletePayload {
	handshakeComplete := mgsContracts.HandshakeCompletePayload{}
	handshakeComplete.HandshakeTimeToComplete =
		dataChannel.handshake.handshakeEndTime.Sub(dataChannel.handshake.handshakeStartTime)

	clientVersion := dataChannel.GetClientVersion()
	if dataChannel.separateOutputPayload == true && versionutil.Compare(clientVersion, clientVersionWithoutOutputSeparation, true) <= 0 {
		handshakeComplete.CustomerMessage = "Please update session manager plugin version (minimum required version " +
			firstVersionWithOutputSeparationFeature +
			") for fully support of separate StdOut/StdErr output.\r\n"
	}

	if dataChannel.encryptionEnabled {
		handshakeComplete.CustomerMessage += fmt.Sprintf(
			"This session is encrypted using AWS KMS.\nlog LTK ARN: %s\nbase-64 encoded client read key: %s\nbase-64 encoded agent read key: %s",
			dataChannel.logLTKeyARN,
			dataChannel.encryptedClientReadKey,
			dataChannel.encryptedAgentReadKey,
		)
	}

	return handshakeComplete
}

// sendHandshakeRequest sends handshake request
func (dataChannel *DataChannel) sendHandshakeRequest(log log.T, handshakeRequestPayload mgsContracts.HandshakeRequestPayload) (err error) {
	var handshakeRequestPayloadBytes []byte
	if handshakeRequestPayloadBytes, err = json.Marshal(handshakeRequestPayload); err != nil {
		return fmt.Errorf("Could not serialize HandshakeRequest message %v, err: %s", handshakeRequestPayload, err)
	}

	log.Debug("Sending Handshake Request.")
	log.Tracef("Sending HandshakeRequest message with content %v", handshakeRequestPayload)
	if err = dataChannel.SendStreamDataMessage(log, mgsContracts.HandshakeRequest, handshakeRequestPayloadBytes); err != nil {
		return fmt.Errorf("Failed sending of HandshakeRequest message, err: %s", err)
	}
	return nil
}

// sendHandshakeComplete sends handshake complete
func (dataChannel *DataChannel) sendHandshakeComplete(log log.T, handshakeCompletePayload mgsContracts.HandshakeCompletePayload) (err error) {
	var handshakeCompletePayloadBytes []byte
	if handshakeCompletePayloadBytes, err = json.Marshal(handshakeCompletePayload); err != nil {
		return fmt.Errorf("Could not serialize HandshakeComplete message %v, err: %s", handshakeCompletePayload, err)
	}

	log.Debug("Sending HandshakeComplete.")
	log.Tracef("Sending HandshakeComplete message with content %v", handshakeCompletePayload)
	if err = dataChannel.SendStreamDataMessage(log, mgsContracts.HandshakeComplete, handshakeCompletePayloadBytes); err != nil {
		return err
	}
	return nil
}

// sendEncryptionChallenge sends encryption challenge
func (dataChannel *DataChannel) sendEncryptionChallenge(log log.T) (err error) {
	// Build the request
	encChallengeRequest := mgsContracts.EncryptionChallengeRequest{}
	randBytes := make([]byte, 64)
	cryptoRand.Read(randBytes)
	dataChannel.handshake.encryptionChallenge = randBytes
	randBytes, err = dataChannel.blockCipher.EncryptWithAESGCM(randBytes)
	if err != nil {
		return err
	}
	encChallengeRequest.Challenge = randBytes

	// Send it
	log.Debug("Sending EncryptionChallengeRequest.")
	err = dataChannel.sendStreamDataMessageJson(log, mgsContracts.EncChallengeRequest, encChallengeRequest)
	if err != nil {
		return err
	}
	return
}

// sendStreamDataMessageJson is utility method that serializes a struct into json and sends with the given payload type
func (dataChannel *DataChannel) sendStreamDataMessageJson(log log.T,
	payloadType mgsContracts.PayloadType, serializableStruct interface{}) (err error) {
	var messageBytes []byte
	if messageBytes, err = json.Marshal(serializableStruct); err != nil {
		return fmt.Errorf("Could not serialize message %v, err: %s", serializableStruct, err)
	}
	log.Tracef("Sending message with content %v", serializableStruct)
	err = dataChannel.SendStreamDataMessage(log, payloadType, messageBytes)
	return err
}

// GetClientVersion returns version of the client
func (dataChannel *DataChannel) GetClientVersion() string {
	return dataChannel.handshake.clientVersion
}

// GetInstanceId returns id of the target
func (dataChannel *DataChannel) GetInstanceId() string {
	return dataChannel.InstanceId
}

// GetRegion returns aws region of the target
func (dataChannel *DataChannel) GetRegion() string {
	return dataChannel.Service.GetRegion()
}

// IsActive returns a boolean value indicating the datachannel is actively listening
// and communicating with service
func (dataChannel *DataChannel) IsActive() bool {
	return !dataChannel.Pause
}

// GetSeparateOutputPayload returns boolean value indicating separate
// stdout/stderr output for non-interactive session or not
func (dataChannel *DataChannel) GetSeparateOutputPayload() bool {
	return dataChannel.separateOutputPayload
}

// SetSeparateOutputPayload set separateOutputPayload value
func (dataChannel *DataChannel) SetSeparateOutputPayload(separateOutputPayload bool) {
	dataChannel.separateOutputPayload = separateOutputPayload
}

// getDataChannelToken calls CreateDataChannel to get the token for this session.
func getDataChannelToken(log log.T,
	mgsService service.Service,
	sessionId string,
	requestId string,
	clientId string) (tokenValue string, err error) {

	createDataChannelInput := &service.CreateDataChannelInput{
		MessageSchemaVersion: aws.String(mgsConfig.MessageSchemaVersion),
		RequestId:            aws.String(requestId),
		ClientId:             aws.String(clientId),
	}

	createDataChannelOutput, err := mgsService.CreateDataChannel(log, createDataChannelInput, sessionId)
	if err != nil || createDataChannelOutput == nil {
		return "", fmt.Errorf("CreateDataChannel failed with no output or error: %s", err)
	}

	log.Debugf("Successfully get datachannel token")
	return *createDataChannelOutput.TokenValue, nil
}

// getMgsEndpoint builds mgs endpoint.
func getMgsEndpoint(context context.T, region string) (string, error) {
	hostName := mgsConfig.GetMgsEndpoint(context, region)
	if hostName == "" {
		return "", fmt.Errorf("no MGS endpoint found in region %s", region)
	}
	var endpointBuilder bytes.Buffer
	endpointBuilder.WriteString(mgsConfig.HttpsPrefix)
	endpointBuilder.WriteString(hostName)
	return endpointBuilder.String(), nil
}

// getNonRetryableDataChannelErrors returns list of non retryable errors for data channel retry strategy
func getNonRetryableDataChannelErrors() []string {
	return []string{mgsConfig.SessionAlreadyTerminatedError}
}
