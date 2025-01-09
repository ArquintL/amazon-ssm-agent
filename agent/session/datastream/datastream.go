package datastream

import (
	"bytes"
	"container/list"
	"encoding/json"
	"errors"
	"fmt"
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
	"github.com/aws/aws-sdk-go/aws"
	"github.com/gorilla/websocket"
	"github.com/twinj/uuid"
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

type DataStream struct {
	wsChannel   communicator.IWebSocketChannel
	context     context.T
	Service     service.Service
	ChannelId   string
	ClientId    string
	InstanceId  string
	LogReaderId string
	Role        string
	Pause       bool
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
	//streamDataHandler handles (possibly encrypted) messages received from the stream
	streamDataHandler func(msg *mgsContracts.AgentMessage) error
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

func NewDataStream(context context.T,
	channelId string,
	clientId string,
	logReaderId string,
	streamDataHandler func(msg *mgsContracts.AgentMessage) error,
	cancelFlag task.CancelFlag) (*DataStream, error) {

	if context == nil || streamDataHandler == nil || cancelFlag == nil {
		return nil, errors.New("nil arguments provided to DataStream.NewDataStream")
	}

	log := context.Log()
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

	dataStream := &DataStream{}
	dataStream.initialize(
		context,
		mgsService,
		channelId,
		clientId,
		instanceID,
		logReaderId,
		mgsConfig.RolePublishSubscribe,
		streamDataHandler,
		cancelFlag)

	streamMessageHandler := func(input []byte) {
		if err := dataStream.dataChannelIncomingMessageHandler(log, input); err != nil {
			log.Errorf("Invalid message")
		}
	}
	if err := dataStream.SetWebSocket(context, mgsService, channelId, clientId, streamMessageHandler); err != nil {
		return nil, fmt.Errorf("failed to create websocket for datachannel with error: %s", err)
	}
	if err := dataStream.Open(log); err != nil {
		return nil, fmt.Errorf("failed to open datachannel with error: %s", err)
	}
	dataStream.ResendStreamDataMessageScheduler(log)

	return dataStream, nil
}

// Initialize populates datastream object.
func (dataStream *DataStream) initialize(context context.T,
	mgsService service.Service,
	sessionId string,
	clientId string,
	instanceId string,
	logReaderId string,
	role string,
	streamDataHandler func(msg *mgsContracts.AgentMessage) error,
	cancelFlag task.CancelFlag) {

	dataStream.context = context
	dataStream.Service = mgsService
	dataStream.ChannelId = sessionId
	dataStream.ClientId = clientId
	dataStream.InstanceId = instanceId
	dataStream.LogReaderId = logReaderId
	dataStream.Role = role
	dataStream.Pause = false
	dataStream.ExpectedSequenceNumber = 0
	dataStream.StreamDataSequenceNumber = 0
	dataStream.StreamDataSequenceNumberMutex = &sync.Mutex{}
	dataStream.OutgoingMessageBuffer = ListMessageBuffer{
		list.New(),
		mgsConfig.OutgoingMessageBufferCapacity,
		&sync.Mutex{},
	}
	dataStream.IncomingMessageBuffer = MapMessageBuffer{
		make(map[int64]StreamingMessage),
		mgsConfig.IncomingMessageBufferCapacity,
		&sync.Mutex{},
	}
	dataStream.RoundTripTime = float64(mgsConfig.DefaultRoundTripTime)
	dataStream.RoundTripTimeVariation = mgsConfig.DefaultRoundTripTimeVariation
	dataStream.RetransmissionTimeout = mgsConfig.DefaultTransmissionTimeout
	dataStream.wsChannel = &communicator.WebSocketChannel{}
	dataStream.streamDataHandler = streamDataHandler
	dataStream.cancelFlag = cancelFlag
}

func (dataStream *DataStream) GetKMSService() (*crypto.KMSService, error) {
	return crypto.NewKMSService(dataStream.context)
}

// SetWebSocket populates webchannel object.
func (dataStream *DataStream) SetWebSocket(context context.T,
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
				return dataStream, err
			}
			dataStream.wsChannel.SetChannelToken(tokenValue)
			if err = dataStream.Reconnect(log); err != nil {
				return dataStream, err
			}
			return dataStream, nil
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
			log.Errorf("failed to set data stream token")
		}
	}

	if err := dataStream.wsChannel.Initialize(context,
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

func (dataStream *DataStream) GetStreamDataSequenceNumber() int64 {
	dataStream.StreamDataSequenceNumberMutex.Lock()
	defer dataStream.StreamDataSequenceNumberMutex.Unlock()

	return dataStream.StreamDataSequenceNumber
}

func (dataStream *DataStream) GetInstanceId() string {
	return dataStream.InstanceId
}

func (dataStream *DataStream) GetClientId() string {
	return dataStream.ClientId
}

func (dataStream *DataStream) GetLogReaderId() string {
	return dataStream.LogReaderId
}

func (dataStream *DataStream) GetChannelId() string {
	return dataStream.ChannelId
}

func (dataStream *DataStream) GetRegion() string {
	return dataStream.Service.GetRegion()
}

// IsActive returns a boolean value indicating the datachannel is actively listening
// and communicating with service
func (dataStream *DataStream) IsActive() bool {
	return !dataStream.Pause
}

// CancelSession cancels session because handshake failed
func (dataStream *DataStream) CancelSession() {
	dataStream.cancelFlag.Set(task.Canceled)
}

// Open opens the websocket connection and sends the token for service to acknowledge the connection.
func (dataStream *DataStream) Open(log log.T) error {
	// Opens websocket connection
	if err := dataStream.wsChannel.Open(log, nil); err != nil {
		return fmt.Errorf("failed to connect data channel with error: %s", err)
	}

	// finalize handshake
	uuid.SwitchFormat(uuid.CleanHyphen)
	uid := uuid.NewV4().String()

	openDataChannelInput := service.OpenDataChannelInput{
		MessageSchemaVersion: aws.String(mgsConfig.MessageSchemaVersion),
		RequestId:            aws.String(uid),
		TokenValue:           aws.String(dataStream.wsChannel.GetChannelToken()),
		ClientInstanceId:     aws.String(dataStream.InstanceId),
		ClientId:             aws.String(dataStream.ClientId),
	}
	jsonValue, err := json.Marshal(openDataChannelInput)
	if err != nil {
		return fmt.Errorf("error serializing openDataChannelInput: %s", err)
	}

	return dataStream.SendMessage(log, jsonValue, websocket.TextMessage)
}

// SendMessage sends a message to the service through datachannel.
func (dataStream *DataStream) SendMessage(log log.T, input []byte, inputType int) error {
	return dataStream.wsChannel.SendMessage(log, input, inputType)
}

// Reconnect reconnects datachannel to service endpoint.
func (dataStream *DataStream) Reconnect(log log.T) error {
	log.Debugf("Reconnecting datachannel: %s", dataStream.ChannelId)

	if err := dataStream.wsChannel.Close(log); err != nil {
		log.Debugf("Closing datachannel failed with error: %s", err)
	}

	if err := dataStream.Open(log); err != nil {
		return fmt.Errorf("failed to reconnect datachannel with error: %s", err)
	}

	dataStream.Pause = false
	log.Debugf("Successfully reconnected to datachannel %s", dataStream.ChannelId)
	return nil
}

// Close closes datachannel - its web socket connection.
func (dataStream *DataStream) Close(log log.T) error {
	log.Infof("Closing datachannel with channel Id %s", dataStream.ChannelId)
	return dataStream.wsChannel.Close(log)
}

// PrepareToCloseChannel waits for all messages to be sent to MGS
func (dataStream *DataStream) PrepareToCloseChannel(log log.T) {
	done := make(chan bool)
	go func() {
		dataStream.OutgoingMessageBuffer.Mutex.Lock()
		len := dataStream.OutgoingMessageBuffer.Messages.Len()
		dataStream.OutgoingMessageBuffer.Mutex.Unlock()
		for len > 0 {
			time.Sleep(10 * time.Millisecond)
			dataStream.OutgoingMessageBuffer.Mutex.Lock()
			len = dataStream.OutgoingMessageBuffer.Messages.Len()
			dataStream.OutgoingMessageBuffer.Mutex.Unlock()
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

func (dataStream *DataStream) Send(log log.T, payloadType mgsContracts.PayloadType, inputData []byte) error {
	// StreamDataSequenceNumber only changed in the code block below
	dataStream.StreamDataSequenceNumberMutex.Lock()
	defer dataStream.StreamDataSequenceNumberMutex.Unlock()

	var flag uint64 = 0
	if dataStream.StreamDataSequenceNumber == 0 {
		flag = 1
	}

	uuid.SwitchFormat(uuid.CleanHyphen)
	messageId := uuid.NewV4()
	agentMessage := &mgsContracts.AgentMessage{
		MessageType:    mgsContracts.OutputStreamDataMessage,
		SchemaVersion:  1,
		CreatedDate:    uint64(time.Now().UnixNano() / 1000000),
		SequenceNumber: dataStream.StreamDataSequenceNumber,
		Flags:          flag,
		MessageId:      messageId,
		PayloadType:    uint32(payloadType), // TODO: treat this message symbolically as being a 2-tuple of payloadType and inputData
		Payload:        inputData,
	}
	msg, err := agentMessage.Serialize(log)
	if err != nil {
		return fmt.Errorf("cannot serialize StreamData message %v", agentMessage)
	}

	if dataStream.Pause {
		log.Tracef("Sending stream data message has been paused, saving stream data message sequence %d to local map: ", dataStream.StreamDataSequenceNumber)
	} else {
		log.Tracef("Send stream data message sequence number %d", dataStream.StreamDataSequenceNumber)
		if err = dataStream.SendMessage(log, msg, websocket.BinaryMessage); err != nil {
			log.Errorf("Error sending stream data message %v", err)
		}
	}

	streamingMessage := StreamingMessage{
		msg,
		dataStream.StreamDataSequenceNumber,
		time.Now(),
	}

	log.Tracef("Add stream data to OutgoingMessageBuffer. Sequence Number: %d", streamingMessage.SequenceNumber)
	dataStream.AddDataToOutgoingMessageBuffer(streamingMessage)
	dataStream.StreamDataSequenceNumber = dataStream.StreamDataSequenceNumber + 1
	return nil
}

// ResendStreamDataMessageScheduler spawns a separate go thread which keeps checking OutgoingMessageBuffer at fixed interval
// and resends first message if time elapsed since lastSentTime of the message is more than acknowledge wait time
func (dataStream *DataStream) ResendStreamDataMessageScheduler(log log.T) error {
	go func() {
		defer func() {
			if r := recover(); r != nil {
				log.Errorf("Resend stream data message scheduler panic: %v", r)
				log.Errorf("Stacktrace:\n%s", debug.Stack())
			}
		}()
		for {
			time.Sleep(mgsConfig.ResendSleepInterval)
			if dataStream.Pause {
				log.Tracef("Resend stream data message has been paused")
				continue
			}
			dataStream.OutgoingMessageBuffer.Mutex.Lock()
			streamMessageElement := dataStream.OutgoingMessageBuffer.Messages.Front()
			if streamMessageElement == nil {
				dataStream.OutgoingMessageBuffer.Mutex.Unlock()
				continue
			}

			streamMessage := streamMessageElement.Value.(StreamingMessage)
			if time.Since(streamMessage.LastSentTime) > dataStream.RetransmissionTimeout {
				log.Tracef("Resend stream data message: %d", streamMessage.SequenceNumber)
				if err := dataStream.SendMessage(log, streamMessage.Content, websocket.BinaryMessage); err != nil {
					log.Errorf("Unable to send stream data message: %s", err)
				}
				streamMessage.LastSentTime = time.Now()
				streamMessageElement.Value = streamMessage
			}
			dataStream.OutgoingMessageBuffer.Mutex.Unlock()
		}
	}()
	return nil
}

// ProcessAcknowledgedMessage processes acknowledge messages by deleting them from OutgoingMessageBuffer.
func (dataStream *DataStream) ProcessAcknowledgedMessage(log log.T, acknowledgeMessageContent mgsContracts.AcknowledgeContent) {
	acknowledgeSequenceNumber := acknowledgeMessageContent.SequenceNumber
	dataStream.OutgoingMessageBuffer.Mutex.Lock()
	defer dataStream.OutgoingMessageBuffer.Mutex.Unlock()
	for streamMessageElement := dataStream.OutgoingMessageBuffer.Messages.Front(); streamMessageElement != nil; streamMessageElement = streamMessageElement.Next() {
		streamMessage := streamMessageElement.Value.(StreamingMessage)
		if streamMessage.SequenceNumber == acknowledgeSequenceNumber {

			//Calculate retransmission timeout based on latest round trip time of message
			dataStream.calculateRetransmissionTimeout(log, streamMessage)

			log.Tracef("Delete stream data from OutgoingMessageBuffer. Sequence Number: %d", streamMessage.SequenceNumber)
			dataStream.OutgoingMessageBuffer.Messages.Remove(streamMessageElement)
			break
		}
	}
}

// SendAcknowledgeMessage sends acknowledge message for stream data over data channel
func (dataStream *DataStream) SendAcknowledgeMessage(log log.T, messageType string, messageId string, sequenceNumber int64) error {
	dataStreamAcknowledgeContent := &mgsContracts.AcknowledgeContent{
		MessageType:         messageType,
		MessageId:           messageId,
		SequenceNumber:      sequenceNumber,
		IsSequentialMessage: true,
	}

	acknowledgeContentBytes, err := dataStreamAcknowledgeContent.Serialize(log)
	if err != nil {
		// should not happen
		log.Errorf("Cannot serialize Acknowledge message err: %v", err)
		return err
	}

	log.Tracef("Send %s message for stream data: %d", mgsContracts.AcknowledgeMessage, sequenceNumber)
	if err := dataStream.SendAgentMessage(log, mgsContracts.AcknowledgeMessage, acknowledgeContentBytes); err != nil {
		return err
	}
	return nil
}

// sendAgentMessage sends agent message for given messageType and content
func (dataStream *DataStream) SendAgentMessage(log log.T, messageType string, messageContent []byte) error {
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

	err = dataStream.SendMessage(log, msg, websocket.BinaryMessage)
	if err != nil {
		log.Errorf("Error sending %s message %v", messageType, err)
		return err
	}
	return nil
}

// AddDataToOutgoingMessageBuffer adds given message at the end of OutputMessageBuffer if it has capacity.
func (dataStream *DataStream) AddDataToOutgoingMessageBuffer(streamMessage StreamingMessage) {
	dataStream.OutgoingMessageBuffer.Mutex.Lock()
	defer dataStream.OutgoingMessageBuffer.Mutex.Unlock()

	if dataStream.OutgoingMessageBuffer.Messages.Len() == dataStream.OutgoingMessageBuffer.Capacity {
		return
	}
	dataStream.OutgoingMessageBuffer.Messages.PushBack(streamMessage)
}

// RemoveDataFromOutgoingMessageBuffer removes given element from OutgoingMessageBuffer.
func (dataStream *DataStream) RemoveDataFromOutgoingMessageBuffer(streamMessageElement *list.Element) {
	dataStream.OutgoingMessageBuffer.Mutex.Lock()
	dataStream.OutgoingMessageBuffer.Messages.Remove(streamMessageElement)
	dataStream.OutgoingMessageBuffer.Mutex.Unlock()
}

// dataChannelIncomingMessageHandler deserialize incoming message and
// processes that data based on MessageType.
func (dataStream *DataStream) dataChannelIncomingMessageHandler(log log.T, rawMessage []byte) error {

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
		return dataStream.handleStreamDataMessage(log, streamDataMessage, rawMessage)
	case mgsContracts.AcknowledgeMessage:
		return dataStream.handleAcknowledgeMessage(log, streamDataMessage)
	case mgsContracts.ChannelClosedMessage:
		return dataStream.handleChannelClosedMessage(log, streamDataMessage)
	case mgsContracts.PausePublicationMessage:
		dataStream.handlePausePublicationMessage(log, streamDataMessage)
		return nil
	case mgsContracts.StartPublicationMessage:
		dataStream.handleStartPublicationMessage(log, streamDataMessage)
		return nil
	default:
		log.Warnf("Invalid message type received: %s", streamDataMessage.MessageType)
	}

	return nil
}

// calculateRetransmissionTimeout calculates message retransmission timeout value based on round trip time on given message.
func (dataStream *DataStream) calculateRetransmissionTimeout(log log.T, streamingMessage StreamingMessage) {
	newRoundTripTime := float64(time.Since(streamingMessage.LastSentTime))

	dataStream.RoundTripTimeVariation = ((1 - mgsConfig.RTTVConstant) * dataStream.RoundTripTimeVariation) +
		(mgsConfig.RTTVConstant * math.Abs(dataStream.RoundTripTime-newRoundTripTime))

	dataStream.RoundTripTime = ((1 - mgsConfig.RTTConstant) * dataStream.RoundTripTime) +
		(mgsConfig.RTTConstant * newRoundTripTime)

	dataStream.RetransmissionTimeout = time.Duration(dataStream.RoundTripTime +
		math.Max(float64(mgsConfig.ClockGranularity), float64(4*dataStream.RoundTripTimeVariation)))

	// Ensure RetransmissionTimeout do not exceed maximum timeout defined
	if dataStream.RetransmissionTimeout > mgsConfig.MaxTransmissionTimeout {
		dataStream.RetransmissionTimeout = mgsConfig.MaxTransmissionTimeout
	}

	log.Tracef("Retransmission timeout calculated in mills. "+
		"AcknowledgeMessageSequenceNumber: %d, RoundTripTime: %d, RoundTripTimeVariation: %d, RetransmissionTimeout: %d",
		streamingMessage.SequenceNumber,
		dataStream.RoundTripTime,
		dataStream.RoundTripTimeVariation,
		dataStream.RetransmissionTimeout/time.Millisecond)
}

// handleStreamDataMessage handles incoming stream data messages by processing the payload and updating expectedSequenceNumber.
func (dataStream *DataStream) handleStreamDataMessage(log log.T,
	streamDataMessage *mgsContracts.AgentMessage,
	rawMessage []byte) (err error) {

	// since we forward `streamDataMessage` to a closure over which we do not have any control,
	// we copy the few fields we need such that we do not rely on the closure leaving `streamDataMessage` unmodified.
	streamDataMessageType := streamDataMessage.MessageType
	streamDataMessageId := streamDataMessage.MessageId.String()
	streamDataMessageSequenceNumber := streamDataMessage.SequenceNumber

	dataStream.Pause = false
	// On receiving expected stream data message, send acknowledgement, process it and increment expected sequence number by 1.
	// Further process messages from IncomingMessageBuffer
	if streamDataMessageSequenceNumber == dataStream.ExpectedSequenceNumber {
		log.Tracef("Process new incoming stream data message. Sequence Number: %d", streamDataMessage.SequenceNumber)
		if err = dataStream.streamDataHandler(streamDataMessage); err != nil {
			if errors.Is(err, mgsContracts.ErrHandlerNotReady) {
				return nil
			}
			return err
		}

		if err = dataStream.SendAcknowledgeMessage(log, streamDataMessageType, streamDataMessageId, streamDataMessageSequenceNumber); err != nil {
			return err
		}

		// Message is acknowledged so increment expected sequence number
		dataStream.ExpectedSequenceNumber = dataStream.ExpectedSequenceNumber + 1
		return dataStream.processIncomingMessageBufferItems(log)

	} else if streamDataMessageSequenceNumber > dataStream.ExpectedSequenceNumber {
		// If incoming message sequence number is greater than expected sequence number and IncomingMessageBuffer has capacity,
		// add message to IncomingMessageBuffer and send acknowledgement
		log.Debugf("Unexpected sequence message received. Received Sequence Number: %d. Expected Sequence Number: %d",
			streamDataMessageSequenceNumber, dataStream.ExpectedSequenceNumber)

		dataStream.IncomingMessageBuffer.Mutex.Lock()
		defer dataStream.IncomingMessageBuffer.Mutex.Unlock()
		if len(dataStream.IncomingMessageBuffer.Messages) < dataStream.IncomingMessageBuffer.Capacity {
			if err = dataStream.SendAcknowledgeMessage(log, streamDataMessageType, streamDataMessageId, streamDataMessageSequenceNumber); err != nil {
				return err
			}

			streamingMessage := StreamingMessage{
				rawMessage,
				streamDataMessageSequenceNumber,
				time.Now(),
			}

			//Add message to buffer for future processing
			log.Debugf("Add stream data to IncomingMessageBuffer. Sequence Number: %d", streamDataMessage.SequenceNumber)
			dataStream.IncomingMessageBuffer.Messages[streamingMessage.SequenceNumber] = streamingMessage
		}
	} else {
		log.Tracef("Discarding already processed message. Received Sequence Number: %d. Expected Sequence Number: %d",
			streamDataMessageSequenceNumber, dataStream.ExpectedSequenceNumber)
	}
	return nil
}

// handleAcknowledgeMessage deserialize acknowledge content and process it.
func (dataStream *DataStream) handleAcknowledgeMessage(log log.T, streamDataMessage *mgsContracts.AgentMessage) (err error) {
	dataStream.Pause = false
	acknowledgeMessage := &mgsContracts.AcknowledgeContent{}
	if err = acknowledgeMessage.Deserialize(log, streamDataMessage); err != nil {
		log.Errorf("Cannot deserialize payload to AcknowledgeMessage: %s, err: %v.", string(streamDataMessage.Payload), err)
		return err
	}

	dataStream.ProcessAcknowledgedMessage(log, *acknowledgeMessage)
	return nil
}

// handleChannelClosedMessage deserialize channel_closed message content and terminate the session.
func (dataStream *DataStream) handleChannelClosedMessage(log log.T, streamDataMessage *mgsContracts.AgentMessage) (err error) {
	channelClosedMessage := &mgsContracts.ChannelClosed{}
	if err = channelClosedMessage.Deserialize(log, streamDataMessage); err != nil {
		log.Errorf("Cannot deserialize payload to ChannelClosed message: %s, err: %v.", string(streamDataMessage.Payload), err)
		return err
	}

	log.Debugf("Processing terminate session request: messageId %s, sessionId %s", channelClosedMessage.MessageId, channelClosedMessage.SessionId)
	dataStream.cancelFlag.Set(task.Canceled)

	return nil
}

// handlePausePublicationMessage sets pause status of datachannel to true.
func (dataStream *DataStream) handlePausePublicationMessage(log log.T, streamDataMessage *mgsContracts.AgentMessage) {
	dataStream.Pause = true
	log.Debugf("Processed %s message. Datachannel pause status set to %s", streamDataMessage.MessageType, dataStream.Pause)
}

// handleStartPublicationMessage sets pause status of datachannel to false.
func (dataStream *DataStream) handleStartPublicationMessage(log log.T, streamDataMessage *mgsContracts.AgentMessage) {
	dataStream.Pause = false
	log.Debugf("Processed %s message. Datachannel pause status set to %s", streamDataMessage.MessageType, dataStream.Pause)
}

// processIncomingMessageBufferItems checks if new expected sequence stream data is present in IncomingMessageBuffer.
// If so process it and increment expected sequence number.
// Repeat until expected sequence stream data is not found in IncomingMessageBuffer.
func (dataStream *DataStream) processIncomingMessageBufferItems(log log.T) (err error) {
	dataStream.IncomingMessageBuffer.Mutex.Lock()
	defer dataStream.IncomingMessageBuffer.Mutex.Unlock()

	for {
		bufferedStreamMessage := dataStream.IncomingMessageBuffer.Messages[dataStream.ExpectedSequenceNumber]
		if bufferedStreamMessage.Content != nil {
			// log.Debugf("Process stream data message from IncomingMessageBuffer. "+
			// 	"Sequence Number: %d", bufferedStreamMessage.SequenceNumber)

			streamDataMessage := &mgsContracts.AgentMessage{}

			if err = streamDataMessage.Deserialize(log, bufferedStreamMessage.Content); err != nil {
				// log.Errorf("Cannot deserialize raw message: %d, err: %v.", bufferedStreamMessage.SequenceNumber, err)
				return err
			}
			if err = dataStream.streamDataHandler(streamDataMessage); err != nil {
				// log.Errorf("Unable to process stream data payload, err: %v.", err)
				return err
			}

			dataStream.ExpectedSequenceNumber = dataStream.ExpectedSequenceNumber + 1

			// log.Debugf("Delete stream data from IncomingMessageBuffer. Sequence Number: %d", bufferedStreamMessage.SequenceNumber)
			delete(dataStream.IncomingMessageBuffer.Messages, sequenceNumber)
		} else {
			break
		}
	}
	return nil
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
