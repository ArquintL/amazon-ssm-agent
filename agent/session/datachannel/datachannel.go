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
	"crypto/elliptic"
	cryptoRand "crypto/rand"
	"crypto/rsa"
	"crypto/sha512"
	"encoding/base64"
	"encoding/json"
	"errors"
	"fmt"
	stdLog "log"
	"time"

	contextPkg "github.com/aws/amazon-ssm-agent/agent/context"
	logger "github.com/aws/amazon-ssm-agent/agent/log"
	mgsContracts "github.com/aws/amazon-ssm-agent/agent/session/contracts"
	"github.com/aws/amazon-ssm-agent/agent/session/crypto"
	"github.com/aws/amazon-ssm-agent/agent/session/datachannel/cryptolib"
	"github.com/aws/amazon-ssm-agent/agent/session/datastream"
	"github.com/aws/amazon-ssm-agent/agent/task"
	"github.com/aws/amazon-ssm-agent/agent/version"
	"github.com/aws/amazon-ssm-agent/agent/versionutil"
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
	channelStatusTimeout                    = 150 * time.Millisecond
)

type IDataChannel interface {
	Initialize(dataStream *datastream.DataStream, inputStreamMessageHandler InputStreamMessageHandler)
	// Initialize(context contextPkg.T, mgsService service.Service, sessionId string, clientId string, instanceId string, role string, cancelFlag task.CancelFlag, inputStreamMessageHandler InputStreamMessageHandler)
	// SetWebSocket(context contextPkg.T, mgsService service.Service, sessionId string, clientId string, onMessageHandler func(input []byte)) error
	// Open(log logger.T) error
	Close(log logger.T) error
	// Reconnect(log logger.T) error
	// SendMessage(log logger.T, input []byte, inputType int) error
	SendStreamDataMessage(log logger.T, dataType mgsContracts.PayloadType, inputData []byte) error
	// ResendStreamDataMessageScheduler(log logger.T) error
	// ProcessAcknowledgedMessage(log logger.T, acknowledgeMessageContent mgsContracts.AcknowledgeContent)
	// SendAcknowledgeMessage(log logger.T, agentMessage mgsContracts.AgentMessage) error
	SendAgentSessionStateMessage(log logger.T, sessionStatus mgsContracts.SessionStatus) error
	// AddDataToOutgoingMessageBuffer(streamMessage datastream.StreamingMessage)
	// RemoveDataFromOutgoingMessageBuffer(streamMessageElement *list.Element)
	// AddDataToIncomingMessageBuffer(streamMessage datastream.StreamingMessage)
	// RemoveDataFromIncomingMessageBuffer(sequenceNumber int64)
	SkipHandshake(log logger.T)
	PerformHandshake(log logger.T, kmsKeyId string, encryptionEnabled bool, sessionTypeRequest mgsContracts.SessionTypeRequest) (err error)
	GetClientVersion() string
	GetInstanceId() string
	GetRegion() string
	IsActive() bool
	PrepareToCloseChannel(log logger.T)
	// GetSeparateOutputPayload() bool
	SetSeparateOutputPayload(separateOutputPayload bool)
}

type DataChannelState int

const (
	Uninitialized          DataChannelState = 0
	Initialized            DataChannelState = 1
	HandshakeSkipped       DataChannelState = 2
	BlockCipherInitialized DataChannelState = 3
	AgentSecretCreated     DataChannelState = 4
	HandshakeCompleted     DataChannelState = 5
)

// DataChannel used for session communication between the message gateway service and the agent.
type DataChannel struct {
	//dataChannelState keeps track of the data channel's state such that calls violating the implicit state machine transitions can be rejected
	dataChannelState DataChannelState
	//dataStream handles low-level communication incl. retransmitting and acknowledging messages
	dataStream *datastream.DataStream
	//inputStreamMessageHandler is responsible for handling plugin specific input_stream_data message
	inputStreamMessageHandler InputStreamMessageHandler
	//handshake captures handshake state and error
	handshake Handshake
	//blockCipher stores encrytion keys and provides interface for encryption/decryption functions
	blockCipher *cryptolib.BlockCipherT
	// Indicates whether encryption was enabled
	encryptionEnabled     bool
	separateOutputPayload bool
	state                 AgentHandshakeState
	// agentLTKeyARN is the ARN for the KMS long-term-key used to sign and verify the handshake
	agentLTKeyARN string
	logReaderId   string
	logLTPk       *rsa.PublicKey
	// logLTKeyARN is the logReaderId's ARN for the long-term public key to decrypt session keys
	// logLTKeyARN            string
	/*@ msgHandlerCtx StreamDataHandlerContext @*/ // TODO: mark this as ghost as soon as Gobra supports ghost fields
}

// AgentHandshakeState represents the state of the handshake.
type AgentHandshakeState struct {
	// kmsService is the KMS service used to sign and verify the handshake keyshare
	kmsService    *crypto.KMSService
	agentSecret   []byte
	sharedSecret  []byte
	sessionID     []byte
	agentWriteKey []byte
	agentReadKey  []byte
}

type InputStreamMessageHandler = func(log logger.T, streamDataMessage *mgsContracts.AgentMessage) error

type MessageReceptionStatus int

const (
	ReceiveHandshakeResponeEncryptionEnabled  MessageReceptionStatus = 1
	ReceiveHandshakeResponeEncryptionDisabled MessageReceptionStatus = 2
	ReceiveOtherResponse                      MessageReceptionStatus = 3
)

type Handshake struct {
	// Version of the client
	clientVersion string
	// Channel used to signal that a message is to be expected
	startReceivingChan chan MessageReceptionStatus
	// Channel used to signal when handshake response is received
	responseChan chan bool
	error        error
	// Indicates handshake is complete (Handshake Complete message sent to client)
	complete bool
	// Indiciates if handshake has been skipped
	skipped            bool
	handshakeStartTime time.Time
	handshakeEndTime   time.Time
}

type TestStruct struct{}

// @ requires acc(dataChannel.Mem(), _)
// @ pure
func (dataChannel *DataChannel) GetState() DataChannelState {
	return /*@ unfolding acc(dataChannel.Mem(), _) in @*/ dataChannel.dataChannelState
}

/*@
pred (testStruct *TestStruct) Inv() {
	true
}
@*/

/*@
// TODO remove
ghost
requires context.Mem() && cancelFlag.Mem()
func test_client(context contextPkg.T, cancelFlag task.CancelFlag) {
	tmp @ := TestStruct{}
	testStruct := &tmp
	cl := // @ preserves true
		func callHandler (log logger.T, agentMessage *mgsContracts.AgentMessage) (err error) {
			return
		}
	proof cl implements StreamDataHandlerSpec{testStruct} {
	    unfold testStruct.Inv()
	    err = cl(log, agentMessage) as callHandler
		fold testStruct.Inv()
	}

	fold testStruct.Inv()
	NewDataChannel(context, "bla", "blu", cl, cancelFlag, testStruct)
}

ghost
requires log != nil
preserves dataChannel.RecvRoutineMem() && acc(log.Mem(), _)
func (dataChannel *DataChannel) test_call(log logger.T, streamDataMessage *mgsContracts.AgentMessage) (err error) {
	unfold dataChannel.RecvRoutineMem()
	err = dataChannel.inputStreamMessageHandler(log, streamDataMessage) as StreamDataHandlerSpec{dataChannel.msgHandlerCtx}
	fold dataChannel.RecvRoutineMem()
	return
}
@*/

/*@
type StreamDataHandlerContext interface {
	pred Inv()
}

ghost
requires ctx != nil && log != nil
preserves ctx.Inv() && acc(log.Mem(), _)
func StreamDataHandlerSpec(ghost ctx StreamDataHandlerContext, log logger.T, agentMessage *mgsContracts.AgentMessage) (err error)

pred (dataChannel *DataChannel) RecvRoutineMem() {
	dataChannel != nil &&
	acc(&dataChannel.inputStreamMessageHandler) &&
	acc(&dataChannel.msgHandlerCtx) &&
	dataChannel.msgHandlerCtx != nil && dataChannel.msgHandlerCtx.Inv() &&
	dataChannel.inputStreamMessageHandler implements StreamDataHandlerSpec{dataChannel.msgHandlerCtx} &&
	acc(&dataChannel.handshake.startReceivingChan, 1/2) &&
	acc(dataChannel.handshake.startReceivingChan.RecvChannel()) &&
	dataChannel.handshake.startReceivingChan.RecvGivenPerm() == PredTrue!<!> &&
	dataChannel.handshake.startReceivingChan.RecvGotPerm() == StartReceivingChanInv!<dataChannel, _!> &&
	acc(&dataChannel.handshake.responseChan, 1/2) &&
	dataChannel.handshake.responseChan.SendChannel() &&
	dataChannel.handshake.responseChan.SendGivenPerm() == ResponseChanInv!<dataChannel, _!> &&
	dataChannel.handshake.responseChan.SendGotPerm() == PredTrue!<!>
}

// pred (dataChannel *DataChannel) Mem() {
// 	acc(dataChannel) && dataChannel.dataStream.Mem() &&
// 	dataChannel.msgHandlerCtx != nil && dataChannel.msgHandlerCtx.Inv() &&
// 	dataChannel.inputStreamMessageHandler implements StreamDataHandlerSpec{dataChannel.msgHandlerCtx} &&
// 	(dataChannel.encryptionEnabled ==> dataChannel.blockCipher != nil)
// }

// permissions in `RecvRoutineMem` are already subtracted:
pred (dataChannel *DataChannel) Mem() {
	dataChannel != nil &&
	acc(&dataChannel.dataChannelState) &&
	acc(&dataChannel.dataStream) &&
	// acc(&dataChannel.inputStreamMessageHandler) &&
	acc(&dataChannel.handshake.clientVersion) &&
	acc(&dataChannel.handshake.startReceivingChan, 1/2) &&
	acc(&dataChannel.handshake.responseChan, 1/2) &&
	acc(&dataChannel.handshake.error) &&
	acc(&dataChannel.handshake.complete) &&
	acc(&dataChannel.handshake.skipped) &&
	acc(&dataChannel.handshake.handshakeStartTime) &&
	acc(&dataChannel.handshake.handshakeEndTime) &&
	acc(&dataChannel.blockCipher) &&
	acc(&dataChannel.encryptionEnabled) &&
	acc(&dataChannel.separateOutputPayload) &&
	acc(&dataChannel.state) &&
	acc(&dataChannel.agentLTKeyARN) &&
	acc(&dataChannel.logReaderId) &&
	acc(&dataChannel.logLTPk) &&
	// acc(&dataChannel.msgHandlerCtx) &&
	(dataChannel.dataChannelState >= Initialized ==>
		dataChannel.dataStream.Mem()) &&
	// dataChannel.msgHandlerCtx != nil && dataChannel.msgHandlerCtx.Inv() &&
	// dataChannel.inputStreamMessageHandler implements StreamDataHandlerSpec{dataChannel.msgHandlerCtx} &&
	// (dataChannel.encryptionEnabled ==> dataChannel.blockCipher != nil && dataChannel.blockCipher.Mem()) &&
	(dataChannel.dataChannelState <= Initialized ==>
		dataChannel.handshake.startReceivingChan.SendChannel()) &&
	(dataChannel.dataChannelState > Initialized ==>
		acc(dataChannel.handshake.startReceivingChan.SendChannel(), _)) &&
	dataChannel.handshake.startReceivingChan.SendGivenPerm() == StartReceivingChanInv!<dataChannel, _!> &&
	dataChannel.handshake.startReceivingChan.SendGotPerm() == PredTrue!<!> &&
	dataChannel.handshake.responseChan.RecvChannel() &&
	dataChannel.handshake.responseChan.RecvGivenPerm() == PredTrue!<!> &&
	dataChannel.handshake.responseChan.RecvGotPerm() == ResponseChanInv!<dataChannel, _!> &&
	(dataChannel.dataChannelState == Initialized ==>
		!dataChannel.handshake.skipped) &&
	(dataChannel.dataChannelState == HandshakeSkipped ==>
		dataChannel.handshake.skipped) &&
	(dataChannel.dataChannelState >= BlockCipherInitialized ==>
		!dataChannel.handshake.skipped &&
		dataChannel.blockCipher != nil && dataChannel.blockCipher.Mem()) &&
	(dataChannel.dataChannelState >= AgentSecretCreated && dataChannel.dataChannelState < HandshakeCompleted ==>
		dataChannel.logLTPk.Mem() &&
		dataChannel.state.kmsService.Mem() &&
		bytes.SliceMem(dataChannel.state.agentSecret))
}

pred (dataChannel *DataChannel) MemTransfer() {
	dataChannel != nil &&
	acc(&dataChannel.dataChannelState) &&
	acc(&dataChannel.dataStream) &&
	// acc(&dataChannel.inputStreamMessageHandler) &&
	acc(&dataChannel.handshake.clientVersion) &&
	// we only transfer parts of the permissions for `startReceivingChan` and `responseChan`:
	acc(&dataChannel.handshake.startReceivingChan, 1/4) &&
	acc(&dataChannel.handshake.responseChan, 1/4) &&
	acc(&dataChannel.handshake.error) &&
	acc(&dataChannel.handshake.complete) &&
	acc(&dataChannel.handshake.skipped) &&
	acc(&dataChannel.handshake.handshakeStartTime) &&
	acc(&dataChannel.handshake.handshakeEndTime) &&
	acc(&dataChannel.blockCipher) &&
	acc(&dataChannel.encryptionEnabled) &&
	acc(&dataChannel.separateOutputPayload) &&
	acc(&dataChannel.state) &&
	acc(&dataChannel.agentLTKeyARN) &&
	acc(&dataChannel.logReaderId) &&
	acc(&dataChannel.logLTPk) &&
	// acc(&dataChannel.msgHandlerCtx) &&
	dataChannel.dataStream.Mem() &&
	// dataChannel.msgHandlerCtx != nil && dataChannel.msgHandlerCtx.Inv() &&
	// dataChannel.inputStreamMessageHandler implements StreamDataHandlerSpec{dataChannel.msgHandlerCtx} &&
	// (dataChannel.encryptionEnabled ==> dataChannel.blockCipher != nil && dataChannel.blockCipher.Mem()) &&
	// dataChannel.blockCipher != nil && dataChannel.blockCipher.Mem() &&
	acc(dataChannel.handshake.startReceivingChan.SendChannel(), _) &&
	dataChannel.handshake.startReceivingChan.SendGivenPerm() == StartReceivingChanInv!<dataChannel, _!> &&
	dataChannel.handshake.startReceivingChan.SendGotPerm() == PredTrue!<!> &&
	!dataChannel.handshake.skipped &&
	(dataChannel.dataChannelState >= BlockCipherInitialized ==>
		dataChannel.blockCipher != nil && dataChannel.blockCipher.Mem()) &&
	(dataChannel.dataChannelState >= AgentSecretCreated ==>
		dataChannel.logLTPk.Mem() &&
		dataChannel.state.kmsService.Mem() &&
		bytes.SliceMem(dataChannel.state.agentSecret))
}

pred (dataChannel *DataChannel) Inv() {
	dataChannel.RecvRoutineMem()
}

pred StartReceivingChanInv(dataChannel *DataChannel, msg MessageReceptionStatus) {
	(msg == ReceiveHandshakeResponeEncryptionEnabled ==> dataChannel.MemTransfer() &&
		unfolding dataChannel.MemTransfer() in dataChannel.dataChannelState == AgentSecretCreated) && // acc(dataChannel.Mem(), 1/2) && acc(&dataChannel.handshake.clientVersion, 1/2)) &&
	(msg == ReceiveHandshakeResponeEncryptionDisabled ==> dataChannel.MemTransfer() &&
		unfolding dataChannel.MemTransfer() in dataChannel.dataChannelState == BlockCipherInitialized) &&
	(msg == ReceiveOtherResponse ==> acc(dataChannel.Mem(), 1/2) &&
		dataChannel.GetState() == AgentSecretCreated &&
		unfolding acc(dataChannel.Mem(), 1/2) in dataChannel.handshake.complete)
}

pred ResponseChanInv(dataChannel *DataChannel, encryptionEnabled bool) {
	dataChannel.MemTransfer() &&
	unfolding dataChannel.MemTransfer() in (encryptionEnabled ==> dataChannel.dataChannelState == AgentSecretCreated) && (!encryptionEnabled ==> dataChannel.dataChannelState == BlockCipherInitialized)
}
@*/

// TODO: make `ctx` a ghost parameter as soon as Gobra supports
// ghost fields

// NewDataChannel constructs datachannel objects.
// @ requires context.Mem() && cancelFlag.Mem()
// @ requires ctx != nil && ctx.Inv() && inputStreamMessageHandler implements StreamDataHandlerSpec{ctx}
// @ ensures  err == nil ==> res.Mem() && res.GetState() == Initialized
func NewDataChannel(context contextPkg.T,
	channelId string,
	clientId string,
	inputStreamMessageHandler InputStreamMessageHandler,
	cancelFlag task.CancelFlag,
	/*@ ctx StreamDataHandlerContext @*/) (res *DataChannel, err error) {

	// logger.Debug("HANDSHAKE SLEEPING")
	// time.Sleep(10 * time.Second)

	tmp /*@ @ @*/ := DataChannel{}
	dataChannel := &tmp
	cl := // @ requires log != nil
		// @ preserves acc(log.Mem(), _) && tmp.RecvRoutineMem() && msg.Mem()
		func /*@ callHandler @*/ (log logger.T, msg *mgsContracts.AgentMessage) (err error) {
			err = tmp.processStreamDataMessage(log, msg)
			return
		}
	/*@
		proof cl implements datastream.StreamDataHandlerSpec{dataChannel} {
	        unfold dataChannel.Inv()
	        err = cl(log, msg) as callHandler
			fold dataChannel.Inv()
	    }
	@*/

	dataChannel.dataChannelState = Uninitialized
	dataChannel.handshake.startReceivingChan = make(chan MessageReceptionStatus)
	//@ dataChannel.handshake.startReceivingChan.Init(StartReceivingChanInv!<dataChannel, _!>, PredTrue!<!>)
	dataChannel.inputStreamMessageHandler = inputStreamMessageHandler
	//@ dataChannel.msgHandlerCtx = ctx
	dataChannel.handshake.responseChan = make(chan bool)
	//@ dataChannel.handshake.responseChan.Init(ResponseChanInv!<dataChannel, _!>, PredTrue!<!>)

	//@ fold dataChannel.RecvRoutineMem()
	//@ fold dataChannel.Mem()
	//@ fold dataChannel.Inv()
	dataStream, err := datastream.NewDataStream(context,
		channelId,
		clientId,
		cl,
		cancelFlag,
		/*@ dataChannel @*/)
	if err != nil {
		return nil, fmt.Errorf("failed to create data stream with error: %s", err)
	}

	dataChannel.Initialize(dataStream, inputStreamMessageHandler /*@, ctx @*/)

	return dataChannel, nil
}

// initialize populates datachannel object.
// @ requires dataChannel.Mem() && dataChannel.GetState() == Uninitialized && dataStream.Mem()
// @ ensures  dataChannel.Mem() && dataChannel.GetState() == Initialized
func (dataChannel *DataChannel) Initialize(dataStream *datastream.DataStream,
	inputStreamMessageHandler InputStreamMessageHandler /*@, msgHandlerCtx StreamDataHandlerContext @*/) {
	// @ unfold dataChannel.Mem()
	dataChannel.dataChannelState = Initialized
	dataChannel.dataStream = dataStream
	dataChannel.encryptionEnabled = false
	/*
		dataChannel.handshake = Handshake{
			startReceivingChan: make(chan MessageReceptionStatus),
			responseChan:       make(chan bool),
			error:              nil,
			complete:           false,
			skipped:            false,
			handshakeEndTime:   time.Now(),
			handshakeStartTime: time.Now(),
		}
	*/
	dataChannel.handshake.error = nil
	dataChannel.handshake.complete = false
	dataChannel.handshake.skipped = false
	dataChannel.handshake.handshakeEndTime = time.Now()
	dataChannel.handshake.handshakeStartTime = time.Now()
	// @ fold dataChannel.Mem()
}

// SendStreamDataMessage sends a data message in a form of AgentMessage for streaming.
// Requires that the handshake is either complete or skipped
// @ requires log != nil && noPerm < p && p <= writePerm
// @ requires acc(bytes.SliceMem(inputData), p)
// @ preserves dataChannel.Mem() && dataChannel.GetState() == AgentSecretCreated
// @ preserves acc(log.Mem(), _)
func (dataChannel *DataChannel) SendStreamDataMessage(log logger.T, payloadType mgsContracts.PayloadType, inputData []byte /*@, ghost p perm @*/) (err error) {
	if len(inputData) == 0 {
		log.Debugf("Ignoring empty stream data payload. PayloadType: %d", payloadType)
		return nil
	}

	return dataChannel.sendData(log, payloadType, inputData /*@, p/2 @*/)
}

// @ requires log != nil && noPerm < p && p <= writePerm
// @ requires acc(dataChannel.Mem(), p) && dataChannel.GetState() >= BlockCipherInitialized
// @ requires acc(bytes.SliceMem(inputData), p)
// @ preserves acc(log.Mem(), _)
// @ ensures acc(dataChannel.Mem(), p) && dataChannel.GetState() == old(dataChannel.GetState())
func (dataChannel *DataChannel) sendData(log logger.T, payloadType mgsContracts.PayloadType, inputData []byte /*@, ghost p perm @*/) (err error) {
	// @ oldState := dataChannel.GetState()
	// @ unfold acc(dataChannel.Mem(), p/2)
	// If encryption has been enabled, encrypt the payload
	if dataChannel.encryptionEnabled && (payloadType == mgsContracts.Output || payloadType == mgsContracts.StdErr || payloadType == mgsContracts.ExitCode || payloadType == mgsContracts.HandshakeComplete) {
		if inputData, err = dataChannel.blockCipher.EncryptWithAESGCM(inputData /*@, p/2 @*/); err != nil {
			err = fmt.Errorf("error encrypting stream data message sequence %d, err: %v", dataChannel.dataStream.GetStreamDataSequenceNumber( /*@ p/2 @*/ ), err)
			// @ fold acc(dataChannel.Mem(), p/2)
			return
		}
	}

	dataChannel.dataStream.Send(log, payloadType, inputData /*@, p/2 @*/)
	// @ fold acc(dataChannel.Mem(), p/2)
	return nil
}

// TODO: treat this function as trusted / unrelated to the security protocol because it
// does not involve any cryptography. We might have to model in Tamarin that `GetChannelId()`
// can savely be sent to the network.
// SendAgentSessionStateMessage sends agent session state to MGS
// @ trusted
// @ requires log != nil
// @ preserves dataChannel.Mem() && acc(log.Mem(), _)
// @ ensures dataChannel.GetState() == old(dataChannel.GetState())
func (dataChannel *DataChannel) SendAgentSessionStateMessage(log logger.T, sessionStatus mgsContracts.SessionStatus) error {
	agentSessionStateContent := &mgsContracts.AgentSessionStateContent{
		SchemaVersion: schemaVersion,
		SessionState:  string(sessionStatus),
		SessionId:     dataChannel.dataStream.GetChannelId(),
	}

	var agentSessionStateContentBytes []byte
	var err error
	if agentSessionStateContentBytes, err = json.Marshal(agentSessionStateContent); err != nil {
		log.Errorf("Cannot serialize AgentSessionState message err: %v", err)
		return err
	}

	log.Debugf("Send %s message with session status %s", mgsContracts.AgentSessionState, string(sessionStatus))
	if err := dataChannel.dataStream.SendAgentMessage(log, mgsContracts.AgentSessionState, agentSessionStateContentBytes); err != nil {
		return err
	}
	return nil
}

// @ trusted
// @ preserves dataChannel.RecvRoutineMem()
// @ ensures  err == nil ==> StartReceivingChanInv!<dataChannel, _!>(res)
func (dataChannel *DataChannel) tryReceiveMessageReceptionStatus(timeout time.Duration) (res MessageReceptionStatus, err error) {
	var ok bool
	select {
	case res, ok = <-dataChannel.handshake.startReceivingChan:
		if !ok {
			err = fmt.Errorf("Channel has been closed")
		}
	case <-time.After(timeout):
		err = fmt.Errorf("Timeout occurred waiting for receiving a message on a channel")
	}
	return
}

// @ trusted
// @ requires noPerm < p
// @ preserves acc(dataChannel.Mem(), p) && dataChannel.GetState() == AgentSecretCreated
// @ ensures  err == nil ==> ResponseChanInv!<dataChannel, _!>(res)
func (dataChannel *DataChannel) tryReceiveResponse(timeout time.Duration /*@, ghost p perm @*/) (res bool, err error) {
	var ok bool
	select {
	case res, ok = <-dataChannel.handshake.responseChan:
		if !ok {
			err = fmt.Errorf("Channel has been closed")
		}
	case <-time.After(timeout):
		err = fmt.Errorf("Timeout occurred waiting for receiving a message on a channel")
	}
	return
}

// @ trusted
// @ requires noPerm < p
// @ preserves acc(responseChan.RecvChannel(), p)
// @ preserves responseChan.RecvGivenPerm() == PredTrue!<!>
// @ preserves responseChan.RecvGotPerm() == ResponseChanInv!<dataChannel, _!>
// @ ensures  err == nil ==> ResponseChanInv!<dataChannel, _!>(res)
func (dataChannel *DataChannel) tryReceiveResponseAlt(responseChan chan bool, timeout time.Duration /*@, ghost p perm @*/) (res bool, err error) {
	var ok bool
	select {
	case res, ok = <-responseChan:
		if !ok {
			err = fmt.Errorf("Channel has been closed")
		}
	case <-time.After(timeout):
		err = fmt.Errorf("Timeout occurred waiting for receiving a message on a channel")
	}
	return
}

/*@
// `nonDeterministicChoice` returns either true or false.
// Since we do not constrain the result value, the verifier
// considers both return values for any invocation of `nonDeterministicChoice()`
ghost
func nonDeterministicChoice() bool

// this models `tryReceiveMessageReceptionStatus` as Gobra does not yet support the `select` statement
// we use this function to validate the spec of `tryReceiveMessageReceptionStatus`
ghost
preserves dataChannel.RecvRoutineMem()
ensures  err == nil ==> StartReceivingChanInv!<dataChannel, _!>(res)
func (dataChannel *DataChannel) tryReceiveMessageReceptionStatusModel(timeout time.Duration) (res MessageReceptionStatus, err error) {
	if nonDeterministicChoice() {
		unfold dataChannel.RecvRoutineMem()
		fold PredTrue!<!>()
		var ok bool
		res, ok = <-dataChannel.handshake.startReceivingChan
		fold dataChannel.RecvRoutineMem()
		if !ok {
			err = fmt.Errorf("Channel has been closed")
			return
		}
	} else {
		err = fmt.Errorf("Timeout occurred waiting for receiving a message on a channel")
	}
	return
}

// this models `tryReceiveResponse` as Gobra does not yet support the `select` statement
// we use this function to validate the spec of `tryReceiveResponse`
ghost
requires noPerm < p
preserves acc(dataChannel.Mem(), p) && dataChannel.GetState() == AgentSecretCreated
ensures  err == nil ==> ResponseChanInv!<dataChannel, _!>(res)
func (dataChannel *DataChannel) tryReceiveResponseModel(timeout time.Duration, ghost p perm) (res bool, err error) {
	if nonDeterministicChoice() {
		unfold acc(dataChannel.Mem(), p)
		fold PredTrue!<!>()
		var ok bool
		res, ok = <-dataChannel.handshake.responseChan
		fold acc(dataChannel.Mem(), p)
		if !ok {
			err = fmt.Errorf("Channel has been closed")
			return
		}
	} else {
		err = fmt.Errorf("Timeout occurred waiting for receiving a message on a channel")
	}
	return
}

ghost
requires noPerm < p
preserves acc(responseChan.RecvChannel(), p)
preserves responseChan.RecvGivenPerm() == PredTrue!<!>
preserves responseChan.RecvGotPerm() == ResponseChanInv!<dataChannel, _!>
ensures  err == nil ==> ResponseChanInv!<dataChannel, _!>(res)
func (dataChannel *DataChannel) tryReceiveResponseModelAlt(responseChan chan bool, timeout time.Duration, ghost p perm) (res bool, err error) {
	if nonDeterministicChoice() {
		fold PredTrue!<!>()
		var ok bool
		res, ok = <-responseChan
		if !ok {
			err = fmt.Errorf("Channel has been closed")
			return
		}
	} else {
		err = fmt.Errorf("Timeout occurred waiting for receiving a message on a channel")
	}
	return
}
@*/

// processStreamDataMessage gets called for all messages of type OutputStreamDataMessage
// @ requires log != nil
// @ preserves acc(log.Mem(), _) && dataChannel.RecvRoutineMem() && streamDataMessage.Mem()
func (dataChannel *DataChannel) processStreamDataMessage(log logger.T, streamDataMessage *mgsContracts.AgentMessage) (err error) {

	channelStatus, err := dataChannel.tryReceiveMessageReceptionStatus(channelStatusTimeout)
	if err != nil {
		log.Info("Timeout while receiving channel status")
		return err
	}

	switch channelStatus {
	case ReceiveHandshakeResponeEncryptionEnabled:
		payloadType := /*@ unfolding streamDataMessage.Mem() in @*/ streamDataMessage.PayloadType
		switch mgsContracts.PayloadType(payloadType) {
		case mgsContracts.HandshakeResponse:
			{
				// PayloadType is HandshakeResponse so we call our own handler instead of the plugin handler
				//@ unfold StartReceivingChanInv!<dataChannel, _!>(ReceiveHandshakeResponeEncryptionEnabled)
				if err = dataChannel.handleHandshakeResponse(log, streamDataMessage, true); err != nil {
					return fmt.Errorf("processing of HandshakeResponse message failed, %v", err)
				}
			}
		default:
			return fmt.Errorf("received message with unexpected payload type")
		}
	case ReceiveHandshakeResponeEncryptionDisabled:
		payloadType := /*@ unfolding streamDataMessage.Mem() in @*/ streamDataMessage.PayloadType
		switch mgsContracts.PayloadType(payloadType) {
		case mgsContracts.HandshakeResponse:
			{
				// PayloadType is HandshakeResponse so we call our own handler instead of the plugin handler
				//@ unfold StartReceivingChanInv!<dataChannel, _!>(ReceiveHandshakeResponeEncryptionDisabled)
				if err = dataChannel.handleHandshakeResponse(log, streamDataMessage, false); err != nil {
					return fmt.Errorf("processing of HandshakeResponse message failed, %v", err)
				}
			}
		default:
			return fmt.Errorf("received message with unexpected payload type")
		}
	case ReceiveOtherResponse:
		//@ unfold StartReceivingChanInv!<dataChannel, _!>(ReceiveOtherResponse)
		//@ unfold acc(dataChannel.Mem(), 1/2)
		//@ unfold streamDataMessage.Mem()
		if dataChannel.encryptionEnabled && streamDataMessage.PayloadType == uint32(mgsContracts.Output) {
			plaintext, err := dataChannel.blockCipher.DecryptWithAESGCM(streamDataMessage.Payload /*@, perm(1/2) @*/)
			if err != nil {
				// send a message to the channel to prepare for next message reception:
				//@ fold acc(dataChannel.Mem(), 1/2)
				dataChannel.resendReceiveOtherResponse()
				err = fmt.Errorf("Error decrypting stream data message sequence %d, err: %v", streamDataMessage.SequenceNumber, err)
				//@ fold streamDataMessage.Mem()
				return err
			}
			streamDataMessage.Payload = plaintext
		}
		//@ fold streamDataMessage.Mem()

		// Ignore stream data message if handshake is neither skipped nor completed
		if !dataChannel.handshake.skipped && !dataChannel.handshake.complete {
			// this case should provably not occur as status `ReceiveOtherResponse`
			// is supposed to be sent on the `startReceivingChan` channel AFTER the
			// handshake has completed.
			// We can indeed proof the inexistence of this branch:
			// @ assert false
			/*
				log.Tracef("Handshake still in progress, ignore stream data message sequence %d", streamDataMessage.SequenceNumber)
				// send a message to the channel to prepare for next message reception:
				//@ fold acc(dataChannel.Mem(), 1/2)
				dataChannel.resendReceiveOtherResponse()
				return nil
			*/
		}

		//@ fold acc(dataChannel.Mem(), 1/2)
		//@ unfold dataChannel.RecvRoutineMem()
		err = dataChannel.inputStreamMessageHandler(log, streamDataMessage) /*@ as StreamDataHandlerSpec{dataChannel.msgHandlerCtx} @*/
		//@ fold dataChannel.RecvRoutineMem()
		if err != nil {
			dataChannel.resendReceiveOtherResponse()
			return err
		}
		dataChannel.resendReceiveOtherResponse()
	}

	return nil
}

// @ requires acc(dataChannel.Mem(), 1/2) && dataChannel.GetState() == AgentSecretCreated && unfolding acc(dataChannel.Mem(), 1/2) in dataChannel.handshake.complete
// @ preserves dataChannel.RecvRoutineMem()
func (dataChannel *DataChannel) resendReceiveOtherResponse() {
	//@ unfold acc(dataChannel.Mem(), 1/2)
	// unfold `RecvRoutineMem` before folding `Mem` such that equality of `startReceivingChan` is derived
	//@ unfold dataChannel.RecvRoutineMem()
	//@ fold acc(dataChannel.Mem(), 1/2)
	//@ fold StartReceivingChanInv!<dataChannel, _!>(ReceiveOtherResponse)
	dataChannel.handshake.startReceivingChan <- ReceiveOtherResponse
	//@ fold dataChannel.RecvRoutineMem()
}

// @ trusted
// @ requires noPerm < p
// @ preserves acc(bytes.SliceMem(input), p)
// @ ensures bytes.SliceMem(res)
func computeSHA384(input []byte /*@, ghost p perm @*/) (res []byte) {
	hash := sha512.New384()
	hash.Write(input)
	return hash.Sum(nil)
}

// @ trusted
// @ requires noPerm < p
// @ preserves acc(bytes.SliceMem(input), p)
// @ ensures err == nil ==> bytes.SliceMem(res)
func computeKdf(input []byte, isKdf1 bool /*@, ghost p perm @*/) (res []byte, err error) {
	hash512 := sha512.New
	hkPRK := hkdf.Extract(hash512, input, nil) //it's pretty complicated what using a salt with HKDF means, we should double check this

	const keySize = 32
	res = make([]byte, keySize)

	var ctx string
	if isKdf1 {
		ctx = "S"
	} else {
		ctx = "C"
	}

	bytesRead, err := hkdf.Expand(hash512, hkPRK, []byte(ctx)).Read(res)
	if err != nil {
		return nil, err
	}
	if bytesRead != keySize {
		return nil, errors.New("result of applying KDF has unexpected length")
	}
	return
}

// TODO remove
type HandshakeResponsePayloadTest struct {
	ClientVersion          string                               `json:"ClientVersion"`
	ProcessedClientActions []mgsContracts.ProcessedClientAction `json:"ProcessedClientActions"`
	Errors                 []string                             `json:"Errors"`
}

/*@
// TODO remove
pred (handshakeResponsePayload *HandshakeResponsePayloadTest) Mem() {
	acc(handshakeResponsePayload) &&
	(forall i int :: { handshakeResponsePayload.ProcessedClientActions[i] } 0 <= i && i < len(handshakeResponsePayload.ProcessedClientActions) ==> handshakeResponsePayload.ProcessedClientActions[i].Mem()) &&
	acc(handshakeResponsePayload.Errors)
}
@*/

// TODO remove
// @ requires bytes.SliceMem(data)
// @ ensures  res.Mem()
func foo2(data json.RawMessage) (res *mgsContracts.ProcessedClientAction) {
	s /*@ @ @*/ := mgsContracts.ProcessedClientAction{}
	res = &s
	s.Error = "bla"
	s.ActionResult = data
	//@ fold res.Mem()
	return
}

// TODO remove
// @ requires action.Mem()
func foo(action *mgsContracts.ProcessedClientAction) {
	s /*@ @ @*/ := HandshakeResponsePayloadTest{}
	//@ unfold action.Mem()
	a /*@ @ @*/ := [1]mgsContracts.ProcessedClientAction{*action}
	s.ProcessedClientActions = a[:]
	//@ assert acc(&s.ProcessedClientActions[0])
	//@ fold s.ProcessedClientActions[0].Mem()
	//@ fold s.Mem()
}

// handleHandshakeResponse is the handler for payload type HandshakeResponse
// requires log != nil && acc(dataChannel.Mem(), 1/2) && acc(&dataChannel.handshake.clientVersion, 1/2)
// @ requires log != nil && dataChannel.MemTransfer()
// @ requires unfolding dataChannel.MemTransfer() in (encryptionEnabled ==> dataChannel.dataChannelState == AgentSecretCreated) && (!encryptionEnabled ==> dataChannel.dataChannelState == BlockCipherInitialized)
// @ preserves acc(log.Mem(), _) && dataChannel.RecvRoutineMem()
// @ preserves streamDataMessage.Mem()
func (dataChannel *DataChannel) handleHandshakeResponse(log logger.T, streamDataMessage *mgsContracts.AgentMessage, encryptionEnabled bool) error {
	log.Debug("Received Handshake Response.")
	var handshakeResponse /*@ @ @*/ mgsContracts.HandshakeResponsePayload
	//@ fold handshakeResponse.Mem()
	//@ unfold streamDataMessage.Mem()
	if err := json.Unmarshal(streamDataMessage.Payload, &handshakeResponse); err != nil {
		//@ fold streamDataMessage.Mem()
		return fmt.Errorf("Unmarshalling of HandshakeResponse message failed, %s", err)
	}
	//@ fold streamDataMessage.Mem()
	//@ unfold handshakeResponse.Mem()
	// assert forall i uint :: { handshakeResponse.ProcessedClientActions[i] } 0 <= i && i < len(handshakeResponse.ProcessedClientActions) ==> handshakeResponse.ProcessedClientActions[i].Mem()

	actions := handshakeResponse.ProcessedClientActions
	//@ invariant dataChannel.MemTransfer()
	//@ invariant unfolding dataChannel.MemTransfer() in (encryptionEnabled ==> dataChannel.dataChannelState == AgentSecretCreated) && (!encryptionEnabled ==> dataChannel.dataChannelState == BlockCipherInitialized)
	//@ invariant acc(log.Mem(), _)
	//@ invariant forall i int :: { actions[i] } 0 <= i && i < len(actions) ==> actions[i].Mem()
	for i := range actions {
		//@ unfold actions[i].Mem()
		action := actions[i]
		var err error
		if action.ActionStatus != mgsContracts.Success {
			err = fmt.Errorf("%s failed on client with status %v error: %s",
				action.ActionType, action.ActionStatus, action.Error)
			//@ fold actions[i].Mem()
		} else {
			switch action.ActionType {
			case mgsContracts.SecureSession:
				var resp /*@ @ @*/ mgsContracts.SecureSessionResponse
				//@ fold resp.Mem()
				if !encryptionEnabled {
					//@ fold actions[i].Mem()
					err = fmt.Errorf("unexpected action type 'SecureSession' because encryption is disabled")
					break
				}

				if err = json.Unmarshal(action.ActionResult, &resp); err != nil {
					//@ fold actions[i].Mem()
					err = fmt.Errorf("failed to unmarshal action to SecureSessionResponse: %v", err)
					break
				}
				//@ fold actions[i].Mem()

				// verify client signature
				//@ unfold resp.Mem()
				sig, err := base64.StdEncoding.DecodeString(resp.Signature)
				if err != nil {
					err = fmt.Errorf("failed to decode signature: %v", err)
					break
				}

				//@ unfold dataChannel.MemTransfer()
				agentId := dataChannel.dataStream.GetInstanceId()
				//@ fold dataChannel.MemTransfer()
				clientSignPayload := &mgsContracts.SignClientSharePayload{
					ClientShare: resp.ClientShare,
					AgentId:     agentId,
				}

				//@ fold clientSignPayload.Mem()
				clientSignPayloadBytes, err := json.Marshal(clientSignPayload /*@, perm(1/2) @*/)
				if err != nil {
					err = fmt.Errorf("failed to encode client sign payload: %v", err)
					log.Error(err)
					return err
				}

				//@ unfold dataChannel.MemTransfer()
				ok, err := dataChannel.state.kmsService.Verify(resp.ClientLTKeyARN, clientSignPayloadBytes, sig /*@, perm(1/2) @*/)
				//@ fold dataChannel.MemTransfer()
				if !ok || err != nil {
					err = fmt.Errorf("failed to verify signature: %v", err)
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

				// TODO add spec to `UnmarshalCompressed`!
				clientx, clienty := elliptic.UnmarshalCompressed(elliptic.P384(), clientShareBytes /*@, perm(1/2) @*/)

				// check that the client share is on the curve
				if !elliptic.P384().IsOnCurve(clientx, clienty /*@, perm(1/2) @*/) {
					err = fmt.Errorf("client share is not on the curve")
					log.Error(err)
					return err
				}

				// generate and store the shared secret
				//@ unfold dataChannel.MemTransfer()
				ss, _ := elliptic.P384().ScalarMult(clientx, clienty, dataChannel.state.agentSecret /*@, perm(1/2) @*/) // TODO: Double check it's fine to just use x
				dataChannel.state.sharedSecret = ss.Bytes( /*@ perm(1/2) @*/ )

				// hash the shared secret to obtain the session identifier
				dataChannel.state.sessionID = computeSHA384(dataChannel.state.sharedSecret /*@, 1/2 @*/)

				log.Debugf("agent computed session ID: %v", base64.StdEncoding.EncodeToString(dataChannel.state.sessionID /*@, perm(1/2) @*/))
				// decode the session ID
				var sessionIDBytes []byte
				sessionIDBytes, err = base64.StdEncoding.DecodeString(resp.SessionID)
				if err != nil {
					//@ fold dataChannel.MemTransfer()
					err = fmt.Errorf("failed to decode server session id: %v", err)
					log.Error(err)
					break
				}

				if !bytes.Equal(dataChannel.state.sessionID, sessionIDBytes) {
					err = fmt.Errorf("session ID mismatch: session ID %s does not match client session ID %s", sessionIDBytes, dataChannel.state.sessionID)
					//@ fold dataChannel.MemTransfer()
					log.Error(err)
					break
				}

				// use the shared secret to generate read and write keys
				dataChannel.state.agentWriteKey, err = computeKdf(dataChannel.state.sharedSecret, true /*@, 1/2 @*/)
				if err != nil {
					return err
				}
				dataChannel.state.agentReadKey, err = computeKdf(dataChannel.state.sharedSecret, false /*@, 1/2 @*/)
				if err != nil {
					return err
				}

				agentReadKey := dataChannel.state.agentReadKey
				encodedAgentReadKey := base64.RawStdEncoding.EncodeToString(agentReadKey /*@, perm(1/2) @*/)
				agentWriteKey := dataChannel.state.agentWriteKey
				encodedAgentWriteKey := base64.RawStdEncoding.EncodeToString(agentWriteKey /*@, perm(1/2) @*/)
				log.Debugf("agent read key: %s", encodedAgentReadKey)
				log.Debugf("agent write key: %s", encodedAgentWriteKey)

				// create ciphertext containing session keys:
				sessionKeys := &mgsContracts.SessionKeys{
					AgentReadKey:  encodedAgentReadKey,
					AgentWriteKey: encodedAgentWriteKey,
				}
				//@ fold sessionKeys.Mem()
				sessionKeysBytes, err := json.Marshal(sessionKeys /*@, perm(1/2) @*/)
				if err != nil {
					err = fmt.Errorf("failed to encode session keys: %v", err)
					log.Error(err)
					return err
				}

				// var encryptionContext map[string]*string
				// encryptedSessionKeys, err := dataChannel.kmsService.Encrypt(resp.LogLTKeyARN, sessionKeysBytes, encryptionContext)
				//@ cryptoRand.GetReaderMem()
				encryptedSessionKeys, err := rsa.EncryptPKCS1v15(cryptoRand.Reader, dataChannel.logLTPk, sessionKeysBytes /*@, perm(1/2) @*/)
				if err != nil {
					return fmt.Errorf("failed to encrypt session keys: %v", err)
				}
				encodedEncryptedSessionKeys := base64.StdEncoding.EncodeToString(encryptedSessionKeys /*@, perm(1/2) @*/)
				log.Infof("encrypted base-64-encoded session keys: %s", encodedEncryptedSessionKeys)

				// sign ciphertext containing session keys using KMS:
				signSessionKeysPayload := &mgsContracts.SignSessionKeysPayload{
					EncryptedSessionKeys: encodedEncryptedSessionKeys,
					ClientId:             dataChannel.dataStream.GetClientId(),
				}

				//@ fold signSessionKeysPayload.Mem()
				signSessionKeysPayloadBytes, err := json.Marshal(signSessionKeysPayload /*@, perm(1/2) @*/)
				if err != nil {
					err = fmt.Errorf("failed to encode sign session keys payload: %v", err)
					log.Error(err)
					return err
				}

				sigSessionKeys, err := dataChannel.state.kmsService.Sign(dataChannel.agentLTKeyARN, signSessionKeysPayloadBytes /*@, perm(1/2) @*/)
				if err != nil {
					err = fmt.Errorf("failed to sign session keys payload: %v", err)
					log.Error(err)
					return err
				}

				encodedSigSessionKeys := base64.StdEncoding.EncodeToString(sigSessionKeys /*@, perm(1/2) @*/)

				// send ciphertext containing session keys and the corresponding signature to the log server:
				encryptedSessionKeysPayload := &mgsContracts.EncryptedSessionKeysPayload{
					AgentLTKeyARN:        dataChannel.agentLTKeyARN,
					ClientId:             dataChannel.dataStream.GetClientId(),
					EncryptedSessionKeys: encodedEncryptedSessionKeys,
					Signature:            encodedSigSessionKeys,
				}
				//@ fold encryptedSessionKeysPayload.Mem()
				encryptedSessionKeysPayloadBytes, err := json.Marshal(encryptedSessionKeysPayload /*@, perm(1/2) @*/)
				if err != nil {
					err = fmt.Errorf("failed to encode encrypted session keys payload: %v", err)
					log.Error(err)
					return err
				}
				encodedEncryptedSessionKeysPayloadBytes := base64.StdEncoding.EncodeToString(encryptedSessionKeysPayloadBytes /*@, perm(1/2) @*/)
				log.Infof("encrypted session keys payload that should be sent to log server: %s", encodedEncryptedSessionKeysPayloadBytes)

				// TODO: actually send `encodedEncryptedSessionKeysPayloadBytes` to the log server!

				// dataChannel.encryptedAgentReadKey = encodedReadKey
				// dataChannel.encryptedClientReadKey = resp.EncryptedClientReadKey
				// dataChannel.logLTKeyARN = resp.LogLTKeyARN

				dataChannel.encryptionEnabled = true

				if err = dataChannel.blockCipher.UpdateEncryptionKeys(log, dataChannel.state.agentReadKey, dataChannel.state.agentWriteKey /*@, perm(1/2) @*/); err != nil {
					//@ fold dataChannel.MemTransfer()
					err = fmt.Errorf("failed to update block cipher: %v", err)
					log.Error(err)
					break
				}
				//@ fold dataChannel.MemTransfer()
			// case mgsContracts.KMSEncryption:
			// 	err = dataChannel.finalizeKMSEncryption(log, action.ActionResult)
			// 	break
			case mgsContracts.SessionType:
				//@ fold actions[i].Mem()
				break
			default:
				//@ fold actions[i].Mem()
				log.Warnf("Unknown handshake client action found, %s", action.ActionType)
			}
		}
		if err != nil {
			log.Error(err)
			// Cancel the session because handshake FAILED
			//@ unfold dataChannel.MemTransfer()
			dataChannel.dataStream.CancelSession( /*@ perm(1/2) @*/ )
			// Set handshake error. Initiate handshake waits on handshake.responseChan and will return this error when channel returns.
			dataChannel.handshake.error = err
			//@ fold dataChannel.MemTransfer()
		}
	}
	// unfold acc(dataChannel.Mem(), 1/2)
	//@ unfold dataChannel.MemTransfer()
	dataChannel.handshake.clientVersion = handshakeResponse.ClientVersion
	log.Infof("Client side session manager plugin version is: %s", handshakeResponse.ClientVersion)
	// fold acc(dataChannel.Mem(), 1/2)
	//@ fold dataChannel.MemTransfer()
	//@ fold ResponseChanInv!<dataChannel, _!>(encryptionEnabled)
	//@ unfold dataChannel.RecvRoutineMem()
	dataChannel.handshake.responseChan <- encryptionEnabled
	//@ fold dataChannel.RecvRoutineMem()
	return nil
}

// SkipHandshake is used to skip handshake if the plugin decides it is not necessary
// @ requires log != nil && dataChannel.Mem() && dataChannel.GetState() == Initialized
// @ preserves acc(log.Mem(), _)
// @ ensures dataChannel.Mem() && dataChannel.GetState() == HandshakeSkipped
func (dataChannel *DataChannel) SkipHandshake(log logger.T) {
	log.Info("Skipping handshake.")
	//@ unfold dataChannel.Mem()
	dataChannel.handshake.skipped = true
	dataChannel.dataChannelState = HandshakeSkipped
	//@ fold dataChannel.Mem()
}

// // finalizeKMSEncryption parses encryption parameters returned from the client and sets up encryption
// func (dataChannel *DataChannel) finalizeKMSEncryption(log logger.T, actionResult json.RawMessage) error {
// 	encryptionResponse /*@ @ @*/ := mgsContracts.KMSEncryptionResponse{}

// 	if err := json.Unmarshal(actionResult, &encryptionResponse); err != nil {
// 		return err
// 	}

// 	sessionId := dataChannel.dataStream.GetChannelId() // ChannelId is SessionId
// 	if err := dataChannel.blockCipher.UpdateEncryptionKey(log, encryptionResponse.KMSCipherTextKey, sessionId, dataChannel.dataStream.GetInstanceId()); err != nil {
// 		return fmt.Errorf("Fetching data key failed: %s", err)
// 	}
// 	dataChannel.encryptionEnabled = true
// 	return nil
// }

// PerformHandshake performs handshake to share version string and encryption information with clients like cli/console
// Note that sessionplugin.go first calls `NewDataChannel` followed by at most 1 call to `PerformHandshake`.
// Hence, we can require in the specification that no other handshake is currently on-going for `dataChannel` without
// restricting the current client of `DataChannel`.
// @ requires log != nil && dataChannel.Mem() && dataChannel.GetState() == Initialized
// @ preserves acc(log.Mem(), _)
// unfortunately, we can only return `Mem` if the channel receive operation does not timeout
// @ ensures err == nil ==> dataChannel.Mem() && dataChannel.GetState() == HandshakeCompleted
// ensures err == nil && encryptionEnabled ==> dataChannel.GetState() == AgentSecretCreated
// ensures err == nil && !encryptionEnabled ==> dataChannel.GetState() == BlockCipherInitialized
func (dataChannel *DataChannel) PerformHandshake(log logger.T,
	kmsKeyId string,
	encryptionEnabled bool,
	sessionTypeRequest mgsContracts.SessionTypeRequest) (err error) {
	stdLog.Printf("PerformHandshake")

	//@ unfold dataChannel.Mem()

	if encryptionEnabled {
		// if dataChannel.blockCipher, err = newBlockCipher(dataChannel.context, kmsKeyId); err != nil {
		// 	return fmt.Errorf("Initializing BlockCipher failed: %s", err)
		// }
		log.Info("Encryption enabled: initializing block cipher")
		// dataChannel.blockCipher = &cryptolib.BlockCipherT{}
	}
	// initializing the block cipher independently of `encryptionEnabled` simplifies reasoning
	dataChannel.blockCipher = &cryptolib.BlockCipherT{}
	//@ fold dataChannel.blockCipher.Mem()

	dataChannel.handshake.handshakeStartTime = time.Now()
	dataChannel.encryptionEnabled = encryptionEnabled
	dataChannel.dataChannelState = BlockCipherInitialized
	//@ fold dataChannel.Mem()

	log.Info("Initiating Handshake")
	stdLog.Printf("Initiating Handshake")
	handshakeRequestPayload, err :=
		dataChannel.buildHandshakeRequestPayload(log, encryptionEnabled, sessionTypeRequest)
	if err != nil {
		return err
	}
	if err := dataChannel.sendHandshakeRequest(log, handshakeRequestPayload); err != nil {
		return err
	}

	// notify Go routing handling received messages that it can process a message:
	//@ unfold dataChannel.Mem()
	startReceivingChan := dataChannel.handshake.startReceivingChan
	responseChan := dataChannel.handshake.responseChan
	//@ fold dataChannel.MemTransfer()
	if encryptionEnabled {
		//@ fold StartReceivingChanInv!<dataChannel, _!>(ReceiveHandshakeResponeEncryptionEnabled)
		startReceivingChan <- ReceiveHandshakeResponeEncryptionEnabled
	} else {
		//@ fold StartReceivingChanInv!<dataChannel, _!>(ReceiveHandshakeResponeEncryptionDisabled)
		startReceivingChan <- ReceiveHandshakeResponeEncryptionDisabled
	}

	// Block until handshake response is received or handshake times out
	// res, err := dataChannel.tryReceiveResponse(handshakeTimeout /*@, perm(1/4) @*/)
	res, err := dataChannel.tryReceiveResponseAlt(responseChan, handshakeTimeout /*@, perm(1/4) @*/)
	if err != nil {
		// If handshake times out here this usually means that the client does not understand handshake or something
		// failed critically when processing handshake request.
		return errors.New("Handshake timed out. Please ensure that you have the latest version of the session manager plugin.")
	}
	// we send the flag `encryptionEnabled` back via the channel such that we are able to express the data channel's
	// state. This flag is expected to be identical to `encryptionEnabled`:
	if res != encryptionEnabled {
		return errors.New("Unexpected result from processing handshake response")
	}
	//@ unfold ResponseChanInv!<dataChannel, _!>(res)
	//@ unfold dataChannel.MemTransfer()
	err = dataChannel.handshake.error
	if err != nil {
		//@ fold dataChannel.Mem()
		return err
	}
	stdLog.Printf("Handshake response received")

	dataChannel.handshake.handshakeEndTime = time.Now()
	//@ fold dataChannel.Mem()
	handshakeCompletePayload := dataChannel.buildHandshakeCompletePayload(log)
	if err := dataChannel.sendHandshakeComplete(log, handshakeCompletePayload); err != nil {
		return err
	}
	//@ unfold dataChannel.Mem()
	dataChannel.handshake.complete = true
	dataChannel.dataChannelState = HandshakeCompleted
	log.Info("Handshake successfully completed.")
	stdLog.Printf("Handshake successfully completed.")
	//@ fold dataChannel.Mem()
	return
}

// buildHandshakeRequestPayload builds payload for HandshakeRequest
// @ requires log != nil && dataChannel.Mem() && dataChannel.GetState() == BlockCipherInitialized
// @ preserves acc(log.Mem(), _)
// @ ensures  err == nil ==> dataChannel.Mem() && payload.Mem()
// @ ensures  err == nil && !encryptionRequested ==> dataChannel.GetState() == BlockCipherInitialized
// @ ensures  err == nil && encryptionRequested ==> dataChannel.GetState() == AgentSecretCreated
func (dataChannel *DataChannel) buildHandshakeRequestPayload(log logger.T,
	encryptionRequested bool,
	request mgsContracts.SessionTypeRequest) (payload *mgsContracts.HandshakeRequestPayload, err error) {

	handshakeRequest := &mgsContracts.HandshakeRequestPayload{}
	handshakeRequest.AgentVersion = version.Version
	/*
		handshakeRequest.RequestedClientActions = []mgsContracts.RequestedClientAction{
			{
				ActionType:       mgsContracts.SessionType,
				ActionParameters: request,
			}}
	*/
	sessionTypeAction := mgsContracts.RequestedClientAction{
		ActionType:       mgsContracts.SessionType,
		ActionParameters: request,
	}

	if encryptionRequested {
		// Generate the secret using secure randomness from rand
		//@ cryptoRand.GetReaderMem()
		agentSecret, x, y, err := elliptic.GenerateKey(elliptic.P384(), cryptoRand.Reader)
		if err != nil {
			log.Errorf("failed to generate client secret: %v", err)
			return nil, err
		}

		//@ unfold dataChannel.Mem()
		dataChannel.state.agentSecret = agentSecret

		// Base64 encode the public part and put it in the message
		agentShare := elliptic.MarshalCompressed(elliptic.P384(), x, y /*@, perm(1/2) @*/)
		compressedPublic := base64.StdEncoding.EncodeToString(agentShare /*@, perm(1/2) @*/)

		dataChannel.state.kmsService, err = dataChannel.dataStream.GetKMSService( /*@ perm(1/2) @*/ )
		if err != nil {
			//@ fold dataChannel.Mem()
			err = fmt.Errorf("failed to initialize KMS service: %v", err)
			log.Error(err)
			return nil, err
		}

		// TODO: do this beforehand and set `dataChannel.agentLTKeyARN` and `dataChannel.logLTPk`
		metadata, err := dataChannel.state.kmsService.CreateKeyAssymetric()
		if err != nil {
			err = fmt.Errorf("failed to create agent LTK: %v", err)
			log.Error(err)
			return nil, err
		}

		//@ unfold metadata.Mem()
		if metadata.Arn == nil {
			err = fmt.Errorf("asymmetric key ARN is nil, metadata: %+v", metadata)
			log.Error(err)
			return nil, err
		}
		dataChannel.agentLTKeyARN = *metadata.Arn
		sk, err := rsa.GenerateKey(cryptoRand.Reader, 4096 /*@, perm(1/2) @*/)
		if err != nil {
			err = fmt.Errorf("failed to create log secret key: %v", err)
			log.Error(err)
			return nil, err
		}
		//@ unfold sk.Mem()
		dataChannel.logLTPk = &sk.PublicKey
		// only now do we have all permissions required to satisfy the state transition:
		dataChannel.dataChannelState = AgentSecretCreated

		signPayload := &mgsContracts.SignAgentSharePayload{
			AgentShare:  compressedPublic,
			ClientId:    dataChannel.dataStream.GetClientId(),
			LogReaderId: dataChannel.logReaderId,
		}

		//@ fold signPayload.Mem()
		signPayloadBytes, err := json.Marshal(signPayload /*@, perm(1/2) @*/)
		if err != nil {
			err = fmt.Errorf("failed to encode sign payload: %v", err)
			log.Error(err)
			return nil, err
		}

		sig, err := dataChannel.state.kmsService.Sign(dataChannel.agentLTKeyARN, signPayloadBytes /*@, perm(1/2) @*/)
		if err != nil {
			err = fmt.Errorf("failed to sign agent sign payload: %v", err)
			log.Error(err)
			return nil, err
		}

		log.Debugf("agent signed sign payload: %x", sig)

		req := mgsContracts.SecureSessionRequest{
			Version:        1,
			ShareAlgorithm: "P384",
			AgentShare:     compressedPublic,
			Signature:      base64.StdEncoding.EncodeToString(sig /*@, perm(1/2)@*/),
			AgentLTKeyARN:  dataChannel.agentLTKeyARN,
			LogReaderId:    dataChannel.logReaderId,
		}
		//@ fold dataChannel.Mem()

		log.Debugf("client generated SecureSessionRequest: %+v", req)

		// handshakeRequest.RequestedClientActions = append( /*@ perm(1/1), @*/ handshakeRequest.RequestedClientActions, mgsContracts.RequestedClientAction{
		// 	ActionType:       mgsContracts.SecureSession,
		// 	ActionParameters: req,
		// })
		secureSessionAction := mgsContracts.RequestedClientAction{
			ActionType:       mgsContracts.SecureSession,
			ActionParameters: req,
		}
		handshakeRequest.RequestedClientActions = []mgsContracts.RequestedClientAction{sessionTypeAction, secureSessionAction}
		// handshakeRequest.RequestedClientActions = append(handshakeRequest.RequestedClientActions,
		// 	mgsContracts.RequestedClientAction{
		// 		ActionType: mgsContracts.KMSEncryption,
		// 		ActionParameters: mgsContracts.KMSEncryptionRequest{
		// 			KMSKeyID: dataChannel.blockCipher.GetKMSKeyId(),
		// 		}})
		//@ fold handshakeRequest.Mem()
	} else {
		handshakeRequest.RequestedClientActions = []mgsContracts.RequestedClientAction{sessionTypeAction}
		//@ fold handshakeRequest.Mem()
	}

	return handshakeRequest, nil
}

// buildHandshakeCompletePayload builds payload for HandshakeComplete
// @ requires log != nil
// @ preserves dataChannel.Mem() && acc(log.Mem(), _)
// @ ensures payload.Mem() && dataChannel.GetState() == old(dataChannel.GetState())
func (dataChannel *DataChannel) buildHandshakeCompletePayload(log logger.T) (payload *mgsContracts.HandshakeCompletePayload) {
	handshakeComplete := &mgsContracts.HandshakeCompletePayload{}
	//@ unfold dataChannel.Mem()
	handshakeComplete.HandshakeTimeToComplete =
		dataChannel.handshake.handshakeEndTime.Sub(dataChannel.handshake.handshakeStartTime)
	//@ fold dataChannel.Mem()
	clientVersion := dataChannel.GetClientVersion()
	//@ unfold dataChannel.Mem()
	if dataChannel.separateOutputPayload == true && versionutil.Compare(clientVersion, clientVersionWithoutOutputSeparation, true) <= 0 {
		handshakeComplete.CustomerMessage = "Please update session manager plugin version (minimum required version " +
			firstVersionWithOutputSeparationFeature +
			") for fully support of separate StdOut/StdErr output.\r\n"
	}

	if dataChannel.encryptionEnabled {
		handshakeComplete.CustomerMessage += "This session is encrypted using AWS KMS."
	}
	//@ fold dataChannel.Mem()
	//@ fold handshakeComplete.Mem()

	return handshakeComplete
}

// sendHandshakeRequest sends handshake request
// @ requires log != nil && handshakeRequestPayload.Mem()
// @ requires dataChannel.Mem() && dataChannel.GetState() >= BlockCipherInitialized
// @ preserves acc(log.Mem(), _)
// @ ensures dataChannel.Mem() && dataChannel.GetState() == old(dataChannel.GetState())
func (dataChannel *DataChannel) sendHandshakeRequest(log logger.T, handshakeRequestPayload *mgsContracts.HandshakeRequestPayload) (err error) {
	var handshakeRequestPayloadBytes []byte
	if handshakeRequestPayloadBytes, err = json.Marshal(handshakeRequestPayload /*@, perm(1/2) @*/); err != nil {
		return fmt.Errorf("Could not serialize HandshakeRequest message %v, err: %s", handshakeRequestPayload, err)
	}

	log.Debug("Sending Handshake Request.")
	log.Tracef("Sending HandshakeRequest message with content %v", handshakeRequestPayload)
	if err = dataChannel.sendData(log, mgsContracts.HandshakeRequest, handshakeRequestPayloadBytes /*@, perm(1/2) @*/); err != nil {
		return fmt.Errorf("Failed sending of HandshakeRequest message, err: %s", err)
	}
	return nil
}

// sendHandshakeComplete sends handshake complete
// @ requires log != nil && handshakeCompletePayload.Mem()
// @ requires dataChannel.Mem() && dataChannel.GetState() >= BlockCipherInitialized
// @ preserves acc(log.Mem(), _)
// @ ensures dataChannel.Mem() && dataChannel.GetState() == old(dataChannel.GetState())
func (dataChannel *DataChannel) sendHandshakeComplete(log logger.T, handshakeCompletePayload *mgsContracts.HandshakeCompletePayload) (err error) {
	var handshakeCompletePayloadBytes []byte
	if handshakeCompletePayloadBytes, err = json.Marshal(handshakeCompletePayload /*@, perm(1/2) @*/); err != nil {
		return fmt.Errorf("Could not serialize HandshakeComplete message %v, err: %s", handshakeCompletePayload, err)
	}

	log.Debug("Sending HandshakeComplete.")
	log.Tracef("Sending HandshakeComplete message with content %v", handshakeCompletePayload)
	if err = dataChannel.sendData(log, mgsContracts.HandshakeComplete, handshakeCompletePayloadBytes /*@, perm(1/2) @*/); err != nil {
		return err
	}
	return nil
}

/*
// sendStreamDataMessageJson is utility method that serializes a struct into json and sends with the given payload type
func (dataChannel *DataChannel) sendStreamDataMessageJson(log logger.T,
	payloadType mgsContracts.PayloadType, serializableStruct interface{}) (err error) {
	var messageBytes []byte
	if messageBytes, err = json.Marshal(serializableStruct); err != nil {
		return fmt.Errorf("Could not serialize message %v, err: %s", serializableStruct, err)
	}
	log.Tracef("Sending message with content %v", serializableStruct)
	err = dataChannel.SendStreamDataMessage(log, payloadType, messageBytes)
	return err
}
*/
// GetClientVersion returns version of the client
// @ requires acc(dataChannel.Mem(), _)
// @ pure
func (dataChannel *DataChannel) GetClientVersion() string {
	return /*@ unfolding acc(dataChannel.Mem(), _) in @*/ dataChannel.handshake.clientVersion
}

// GetInstanceId returns id of the target
// @ requires acc(dataChannel.Mem(), _) && dataChannel.GetState() >= Initialized
// @ pure
func (dataChannel *DataChannel) GetInstanceId() string {
	return /*@ unfolding acc(dataChannel.Mem(), _) in @*/ dataChannel.dataStream.GetInstanceId()
}

// GetRegion returns aws region of the target
// @ requires acc(dataChannel.Mem(), _) && dataChannel.GetState() >= Initialized
// @ pure
func (dataChannel *DataChannel) GetRegion() string {
	return /*@ unfolding acc(dataChannel.Mem(), _) in @*/ dataChannel.dataStream.GetRegion()
}

// IsActive returns a boolean value indicating the datachannel is actively listening
// and communicating with service
// @ requires acc(dataChannel.Mem(), _) && dataChannel.GetState() >= Initialized
// @ pure
func (dataChannel *DataChannel) IsActive() bool {
	return /*@ unfolding acc(dataChannel.Mem(), _) in @*/ dataChannel.dataStream.IsActive()
}

// GetSeparateOutputPayload returns boolean value indicating separate
// stdout/stderr output for non-interactive session or not
// @ requires acc(dataChannel.Mem(), _)
// @ pure
func (dataChannel *DataChannel) GetSeparateOutputPayload() bool {
	return /*@ unfolding acc(dataChannel.Mem(), _) in @*/ dataChannel.separateOutputPayload
}

// SetSeparateOutputPayload set separateOutputPayload value
// @ preserves dataChannel.Mem()
// @ ensures dataChannel.GetState() == old(dataChannel.GetState())
func (dataChannel *DataChannel) SetSeparateOutputPayload(separateOutputPayload bool) {
	//@ unfold dataChannel.Mem()
	dataChannel.separateOutputPayload = separateOutputPayload
	//@ fold dataChannel.Mem()
}

// @ requires dataChannel.Mem() && dataChannel.GetState() >= Initialized
// @ ensures  dataChannel.Mem() && dataChannel.GetState() == old(dataChannel.GetState())
func (dataChannel *DataChannel) Close(log logger.T) (err error) {
	//@ unfold dataChannel.Mem()
	err = dataChannel.dataStream.Close(log)
	//@ fold dataChannel.Mem()
	return
}

// @ requires dataChannel.Mem() && dataChannel.GetState() >= Initialized
// @ ensures  dataChannel.Mem() && dataChannel.GetState() == old(dataChannel.GetState())
func (dataChannel *DataChannel) PrepareToCloseChannel(log logger.T) {
	//@ unfold dataChannel.Mem()
	dataChannel.dataStream.PrepareToCloseChannel(log)
	//@ fold dataChannel.Mem()
}
