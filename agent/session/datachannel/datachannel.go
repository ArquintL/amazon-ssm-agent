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

	//@ pred Mem()

	// @ requires log != nil && noPerm < p && p <= writePerm
	// @ requires acc(bytes.SliceMem(inputData), p)
	// @ preserves Mem()
	// @ preserves acc(log.Mem(), _)
	SendStreamDataMessage(log logger.T, dataType mgsContracts.PayloadType, inputData []byte /*@, ghost p perm @*/) error

	// @ requires log != nil
	// @ preserves Mem() && acc(log.Mem(), _)
	SendAgentSessionStateMessage(log logger.T, sessionStatus mgsContracts.SessionStatus) error

	// @ requires log != nil
	// @ preserves Mem() && acc(log.Mem(), _)
	SkipHandshake(log logger.T) error

	// @ requires log != nil
	// @ preserves Mem() && acc(log.Mem(), _)
	PerformHandshake(log logger.T, kmsKeyId string, encryptionEnabled bool, sessionTypeRequest mgsContracts.SessionTypeRequest) (err error)

	// @ requires noPerm < p
	// @ preserves acc(Mem(), p)
	GetClientVersion( /*@ ghost p perm @*/ ) (string, error)

	// @ requires noPerm < p
	// @ preserves acc(Mem(), p)
	GetInstanceId( /*@ ghost p perm @*/ ) (string, error)

	// @ requires noPerm < p
	// @ preserves acc(Mem(), p)
	GetRegion( /*@ ghost p perm @*/ ) (string, error)

	// @ requires noPerm < p
	// @ preserves acc(Mem(), p)
	IsActive( /*@ ghost p perm @*/ ) (bool, error)

	// @ requires noPerm < p
	// @ preserves acc(Mem(), p)
	GetSeparateOutputPayload( /*@ ghost p perm @*/ ) (bool, error)

	// @ preserves Mem()
	SetSeparateOutputPayload(separateOutputPayload bool) error

	// @ requires log != nil
	// @ preserves Mem() && acc(log.Mem(), _)
	PrepareToCloseChannel(log logger.T) error

	// @ requires log != nil
	// @ preserves Mem() && acc(log.Mem(), _)
	Close(log logger.T) error
}

// instruct Gobra to prove that DataChannel is a behavioral subtype of IDataChannel:
//@ (* dataChannel) implements IDataChannel

type DataChannelState int

const (
	Erroneous              DataChannelState = 0
	Uninitialized          DataChannelState = 1
	Initialized            DataChannelState = 2
	HandshakeSkipped       DataChannelState = 3
	BlockCipherInitialized DataChannelState = 4
	AgentSecretCreated     DataChannelState = 5
	HandshakeCompleted     DataChannelState = 6
)

// dataChannel used for session communication between the message gateway service and the agent.
type dataChannel struct {
	//dataChannelState keeps track of the data channel's state such that calls violating the implicit state machine transitions can be rejected
	dataChannelState DataChannelState
	//dataStream handles low-level communication incl. retransmitting and acknowledging messages
	dataStream *datastream.DataStream
	//inputStreamMessageHandler is responsible for handling plugin specific input_stream_data message
	inputStreamMessageHandler InputStreamMessageHandler
	//hs captures handshake state and error
	hs handshake
	//blockCipher stores encrytion keys and provides interface for encryption/decryption functions
	blockCipher *cryptolib.BlockCipherT
	// Indicates whether encryption was enabled
	encryptionEnabled     bool
	separateOutputPayload bool
	state                 agentHandshakeState
	// agentLTKeyARN is the ARN for the KMS long-term-key used to sign and verify the handshake
	agentLTKeyARN string
	logReaderId   string
	logLTPk       *rsa.PublicKey
	/*@ msgHandlerCtx StreamDataHandlerContext @*/ // TODO: mark this as ghost as soon as Gobra supports ghost fields
}

// AgentHandshakeState represents the state of the handshake.
type agentHandshakeState struct {
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

type handshake struct {
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

// @ requires acc(dc.Mem(), _)
// @ pure
func (dc *dataChannel) getState() DataChannelState {
	return /*@ unfolding acc(dc.Mem(), _) in @*/ dc.dataChannelState
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
preserves dc.RecvRoutineMem() && acc(log.Mem(), _)
func (dc *dataChannel) test_call(log logger.T, streamDataMessage *mgsContracts.AgentMessage) (err error) {
	unfold dc.RecvRoutineMem()
	err = dc.inputStreamMessageHandler(log, streamDataMessage) as StreamDataHandlerSpec{dc.msgHandlerCtx}
	fold dc.RecvRoutineMem()
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

pred (dc *dataChannel) RecvRoutineMem() {
	dc != nil &&
	acc(&dc.inputStreamMessageHandler) &&
	acc(&dc.msgHandlerCtx) &&
	dc.msgHandlerCtx != nil && dc.msgHandlerCtx.Inv() &&
	dc.inputStreamMessageHandler implements StreamDataHandlerSpec{dc.msgHandlerCtx} &&
	acc(&dc.hs.startReceivingChan, _) &&
	acc(dc.hs.startReceivingChan.RecvChannel(), _) &&
	dc.hs.startReceivingChan.RecvGivenPerm() == PredTrue!<!> &&
	dc.hs.startReceivingChan.RecvGotPerm() == StartReceivingChanInv!<dc, _!> &&
	acc(&dc.hs.responseChan, _) &&
	acc(dc.hs.responseChan.SendChannel(), _) &&
	dc.hs.responseChan.SendGivenPerm() == ResponseChanInv!<dc, _!> &&
	dc.hs.responseChan.SendGotPerm() == PredTrue!<!>
}

// permissions in `RecvRoutineMem` are already subtracted:
pred (dc *dataChannel) Mem() {
	dc != nil &&
	acc(&dc.dataChannelState) &&
	acc(&dc.hs.startReceivingChan, _) &&
	acc(&dc.hs.responseChan, _) &&
	(dc.dataChannelState != Erroneous ==>
		acc(&dc.dataStream) &&
		acc(&dc.hs.clientVersion) &&
		acc(&dc.hs.error) &&
		acc(&dc.hs.complete) &&
		acc(&dc.hs.skipped) &&
		acc(&dc.hs.handshakeStartTime) &&
		acc(&dc.hs.handshakeEndTime) &&
		acc(&dc.blockCipher) &&
		acc(&dc.encryptionEnabled) &&
		acc(&dc.separateOutputPayload) &&
		acc(&dc.state) &&
		acc(&dc.agentLTKeyARN) &&
		acc(&dc.logReaderId) &&
		acc(&dc.logLTPk)) &&
	(dc.dataChannelState >= Initialized ==>
		dc.dataStream.Mem()) &&
	acc(dc.hs.startReceivingChan.SendChannel(), _) &&
	dc.hs.startReceivingChan.SendGivenPerm() == StartReceivingChanInv!<dc, _!> &&
	dc.hs.startReceivingChan.SendGotPerm() == PredTrue!<!> &&
	acc(dc.hs.responseChan.RecvChannel(), _) &&
	dc.hs.responseChan.RecvGivenPerm() == PredTrue!<!> &&
	dc.hs.responseChan.RecvGotPerm() == ResponseChanInv!<dc, _!> &&
	(dc.dataChannelState == Initialized ==>
		!dc.hs.skipped) &&
	(dc.dataChannelState == HandshakeSkipped ==>
		dc.hs.skipped) &&
	(dc.dataChannelState >= BlockCipherInitialized ==>
		!dc.hs.skipped &&
		dc.blockCipher != nil && dc.blockCipher.Mem()) &&
	(dc.dataChannelState >= AgentSecretCreated && dc.dataChannelState < HandshakeCompleted ==>
		dc.logLTPk.Mem() &&
		dc.state.kmsService.Mem() &&
		bytes.SliceMem(dc.state.agentSecret))
}

pred (dc *dataChannel) MemTransfer(encryptionEnabled bool) {
	dc != nil &&
	acc(&dc.dataStream) &&
	acc(&dc.hs.clientVersion) &&
	acc(&dc.hs.startReceivingChan, _) &&
	acc(&dc.hs.responseChan, _) &&
	acc(&dc.hs.error) &&
	acc(&dc.hs.complete) &&
	acc(&dc.hs.skipped) &&
	acc(&dc.hs.handshakeStartTime) &&
	acc(&dc.hs.handshakeEndTime) &&
	acc(&dc.blockCipher) &&
	acc(&dc.encryptionEnabled) &&
	acc(&dc.separateOutputPayload) &&
	acc(&dc.state) &&
	acc(&dc.agentLTKeyARN) &&
	acc(&dc.logReaderId) &&
	acc(&dc.logLTPk) &&
	dc.dataStream.Mem() &&
	acc(dc.hs.startReceivingChan.SendChannel(), _) &&
	dc.hs.startReceivingChan.SendGivenPerm() == StartReceivingChanInv!<dc, _!> &&
	dc.hs.startReceivingChan.SendGotPerm() == PredTrue!<!> &&
	!dc.hs.skipped &&
	dc.blockCipher != nil && dc.blockCipher.Mem() &&
	(encryptionEnabled ==>
		dc.logLTPk.Mem() &&
		dc.state.kmsService.Mem() &&
		bytes.SliceMem(dc.state.agentSecret))
}

pred (dc *dataChannel) Inv() {
	dc.RecvRoutineMem()
}

pred StartReceivingChanInv(dc *dataChannel, msg MessageReceptionStatus) {
	(msg == ReceiveHandshakeResponeEncryptionEnabled ==> dc.MemTransfer(true)) &&
	(msg == ReceiveHandshakeResponeEncryptionDisabled ==> dc.MemTransfer(false)) &&
	(msg == ReceiveOtherResponse ==> acc(dc.Mem(), 1/2) &&
		dc.getState() == AgentSecretCreated &&
		unfolding acc(dc.Mem(), 1/2) in dc.hs.complete)
}

pred ResponseChanInv(dc *dataChannel, encryptionEnabled bool) {
	dc.MemTransfer(encryptionEnabled)
}
@*/

// NewDataChannel constructs datachannel objects.
// @ requires context.Mem() && cancelFlag.Mem()
// @ requires ctx != nil && ctx.Inv() && inputStreamMessageHandler implements StreamDataHandlerSpec{ctx}
// @ ensures  res.Mem() && typeOf(res) == *dataChannel
// @ ensures  err == nil ==> res.(* dataChannel).getState() == Initialized
// TODO: make `ctx` a ghost parameter as soon as Gobra supports ghost fields
func NewDataChannel(context contextPkg.T,
	channelId string,
	clientId string,
	inputStreamMessageHandler InputStreamMessageHandler,
	cancelFlag task.CancelFlag,
	/*@ ctx StreamDataHandlerContext @*/) (res IDataChannel, err error) {

	tmp /*@ @ @*/ := dataChannel{}
	dc := &tmp
	cl := // @ requires log != nil
		// @ preserves acc(log.Mem(), _) && tmp.RecvRoutineMem() && msg.Mem()
		func /*@ callHandler @*/ (log logger.T, msg *mgsContracts.AgentMessage) (err error) {
			err = tmp.processStreamDataMessage(log, msg)
			return
		}
	/*@
		proof cl implements datastream.StreamDataHandlerSpec{dc} {
	        unfold dc.Inv()
	        err = cl(log, msg) as callHandler
			fold dc.Inv()
	    }
	@*/

	dc.dataChannelState = Uninitialized
	dc.hs.startReceivingChan = make(chan MessageReceptionStatus)
	//@ dc.hs.startReceivingChan.Init(StartReceivingChanInv!<dc, _!>, PredTrue!<!>)
	dc.inputStreamMessageHandler = inputStreamMessageHandler
	//@ dc.msgHandlerCtx = ctx
	dc.hs.responseChan = make(chan bool)
	//@ dc.hs.responseChan.Init(ResponseChanInv!<dc, _!>, PredTrue!<!>)

	//@ fold dc.RecvRoutineMem()
	//@ fold dc.Mem()
	//@ fold dc.Inv()
	dataStream, err := datastream.NewDataStream(context,
		channelId,
		clientId,
		cl,
		cancelFlag,
		/*@ dc @*/)
	if err != nil {
		// we return a non-nil dc such that we can ensure `dc.Mem()`
		// independent of `err`. However, clients should check whether
		// `err` is nil.
		return dc, fmt.Errorf("failed to create data stream with error: %s", err)
	}

	dc.initialize(dataStream)

	return dc, nil
}

// initialize populates datachannel object.
// @ requires dc.Mem() && dc.getState() == Uninitialized && dataStream.Mem()
// @ ensures  dc.Mem() && dc.getState() == Initialized
func (dc *dataChannel) initialize(dataStream *datastream.DataStream) {
	// @ unfold dc.Mem()
	dc.dataChannelState = Initialized
	dc.dataStream = dataStream
	dc.encryptionEnabled = false
	dc.hs.error = nil
	dc.hs.complete = false
	dc.hs.skipped = false
	dc.hs.handshakeEndTime = time.Now()
	dc.hs.handshakeStartTime = time.Now()
	// @ fold dc.Mem()
}

// SendStreamDataMessage sends a data message in a form of AgentMessage for streaming.
// Requires that the handshake is either complete or skipped
// @ requires log != nil && noPerm < p && p <= writePerm
// @ requires acc(bytes.SliceMem(inputData), p)
// @ preserves dc.Mem()
// @ preserves acc(log.Mem(), _)
func (dc *dataChannel) SendStreamDataMessage(log logger.T, payloadType mgsContracts.PayloadType, inputData []byte /*@, ghost p perm @*/) (err error) {
	if dc.getState() < BlockCipherInitialized {
		return fmt.Errorf("DataChannel is in an invalid state %d", dc.getState())
	}

	if len(inputData) == 0 {
		log.Debugf("Ignoring empty stream data payload. PayloadType: %d", payloadType)
		return nil
	}

	return dc.sendData(log, payloadType, inputData /*@, p/2 @*/)
}

// @ requires log != nil && noPerm < p && p <= writePerm
// @ requires acc(dc.Mem(), p) && dc.getState() >= BlockCipherInitialized
// @ requires acc(bytes.SliceMem(inputData), p)
// @ preserves acc(log.Mem(), _)
// @ ensures acc(dc.Mem(), p) && dc.getState() == old(dc.getState())
func (dc *dataChannel) sendData(log logger.T, payloadType mgsContracts.PayloadType, inputData []byte /*@, ghost p perm @*/) (err error) {
	// @ oldState := dc.getState()
	// @ unfold acc(dc.Mem(), p/2)
	// If encryption has been enabled, encrypt the payload
	if dc.encryptionEnabled && (payloadType == mgsContracts.Output || payloadType == mgsContracts.StdErr || payloadType == mgsContracts.ExitCode || payloadType == mgsContracts.HandshakeComplete) {
		if inputData, err = dc.blockCipher.EncryptWithAESGCM(inputData /*@, p/2 @*/); err != nil {
			err = fmt.Errorf("error encrypting stream data message sequence %d, err: %v", dc.dataStream.GetStreamDataSequenceNumber( /*@ p/2 @*/ ), err)
			// @ fold acc(dc.Mem(), p/2)
			return
		}
	}

	dc.dataStream.Send(log, payloadType, inputData /*@, p/2 @*/)
	// @ fold acc(dc.Mem(), p/2)
	return nil
}

// TODO: treat this function as trusted / unrelated to the security protocol because it
// does not involve any cryptography. We might have to model in Tamarin that `GetChannelId()`
// can savely be sent to the network.
// SendAgentSessionStateMessage sends agent session state to MGS
// @ trusted
// @ requires log != nil
// @ preserves dc.Mem() && acc(log.Mem(), _)
// @ ensures dc.getState() == old(dc.getState())
func (dc *dataChannel) SendAgentSessionStateMessage(log logger.T, sessionStatus mgsContracts.SessionStatus) error {
	agentSessionStateContent := &mgsContracts.AgentSessionStateContent{
		SchemaVersion: schemaVersion,
		SessionState:  string(sessionStatus),
		SessionId:     dc.dataStream.GetChannelId(),
	}

	var agentSessionStateContentBytes []byte
	var err error
	if agentSessionStateContentBytes, err = json.Marshal(agentSessionStateContent); err != nil {
		log.Errorf("Cannot serialize AgentSessionState message err: %v", err)
		return err
	}

	log.Debugf("Send %s message with session status %s", mgsContracts.AgentSessionState, string(sessionStatus))
	if err := dc.dataStream.SendAgentMessage(log, mgsContracts.AgentSessionState, agentSessionStateContentBytes); err != nil {
		return err
	}
	return nil
}

// @ trusted
// @ preserves dc.RecvRoutineMem()
// @ ensures  err == nil ==> StartReceivingChanInv!<dc, _!>(res)
func (dc *dataChannel) tryReceiveMessageReceptionStatus(timeout time.Duration) (res MessageReceptionStatus, err error) {
	var ok bool
	select {
	case res, ok = <-dc.hs.startReceivingChan:
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
// @ preserves acc(dc.Mem(), p) && dc.getState() == AgentSecretCreated
// @ ensures  err == nil ==> ResponseChanInv!<dc, _!>(res)
func (dc *dataChannel) tryReceiveResponse(timeout time.Duration /*@, ghost p perm @*/) (res bool, err error) {
	var ok bool
	select {
	case res, ok = <-dc.hs.responseChan:
		if !ok {
			err = fmt.Errorf("Channel has been closed")
		}
	case <-time.After(timeout):
		err = fmt.Errorf("Timeout occurred waiting for receiving a message on a channel")
	}
	return
}

// @ trusted
// @ requires acc(responseChan.RecvChannel(), _)
// @ requires responseChan.RecvGivenPerm() == PredTrue!<!>
// @ requires responseChan.RecvGotPerm() == ResponseChanInv!<dc, _!>
// @ ensures  responseChan.RecvChannel()
// @ ensures  responseChan.RecvGivenPerm() == PredTrue!<!>
// @ ensures  responseChan.RecvGotPerm() == ResponseChanInv!<dc, _!>
// @ ensures  err == nil ==> ResponseChanInv!<dc, _!>(res)
func (dc *dataChannel) tryReceiveResponseAlt(responseChan chan bool, timeout time.Duration) (res bool, err error) {
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
preserves dc.RecvRoutineMem()
ensures  err == nil ==> StartReceivingChanInv!<dc, _!>(res)
func (dc *dataChannel) tryReceiveMessageReceptionStatusModel(timeout time.Duration) (res MessageReceptionStatus, err error) {
	if nonDeterministicChoice() {
		unfold dc.RecvRoutineMem()
		fold PredTrue!<!>()
		var ok bool
		res, ok = <-dc.hs.startReceivingChan
		fold dc.RecvRoutineMem()
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
preserves acc(dc.Mem(), p) && dc.getState() == AgentSecretCreated
ensures  err == nil ==> ResponseChanInv!<dc, _!>(res)
func (dc *dataChannel) tryReceiveResponseModel(timeout time.Duration, ghost p perm) (res bool, err error) {
	if nonDeterministicChoice() {
		unfold acc(dc.Mem(), p)
		fold PredTrue!<!>()
		var ok bool
		res, ok = <-dc.hs.responseChan
		fold acc(dc.Mem(), p)
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
preserves responseChan.RecvGotPerm() == ResponseChanInv!<dc, _!>
ensures  err == nil ==> ResponseChanInv!<dc, _!>(res)
func (dc *dataChannel) tryReceiveResponseModelAlt(responseChan chan bool, timeout time.Duration, ghost p perm) (res bool, err error) {
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
// @ preserves acc(log.Mem(), _) && dc.RecvRoutineMem() && streamDataMessage.Mem()
func (dc *dataChannel) processStreamDataMessage(log logger.T, streamDataMessage *mgsContracts.AgentMessage) (err error) {

	channelStatus, err := dc.tryReceiveMessageReceptionStatus(channelStatusTimeout)
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
				//@ unfold StartReceivingChanInv!<dc, _!>(ReceiveHandshakeResponeEncryptionEnabled)
				if err = dc.handleHandshakeResponse(log, streamDataMessage, true); err != nil {
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
				//@ unfold StartReceivingChanInv!<dc, _!>(ReceiveHandshakeResponeEncryptionDisabled)
				if err = dc.handleHandshakeResponse(log, streamDataMessage, false); err != nil {
					return fmt.Errorf("processing of HandshakeResponse message failed, %v", err)
				}
			}
		default:
			return fmt.Errorf("received message with unexpected payload type")
		}
	case ReceiveOtherResponse:
		//@ unfold StartReceivingChanInv!<dc, _!>(ReceiveOtherResponse)
		//@ unfold acc(dc.Mem(), 1/2)
		//@ unfold streamDataMessage.Mem()
		if dc.encryptionEnabled && streamDataMessage.PayloadType == uint32(mgsContracts.Output) {
			plaintext, err := dc.blockCipher.DecryptWithAESGCM(streamDataMessage.Payload /*@, perm(1/2) @*/)
			if err != nil {
				// send a message to the channel to prepare for next message reception:
				//@ fold acc(dc.Mem(), 1/2)
				dc.resendReceiveOtherResponse()
				err = fmt.Errorf("Error decrypting stream data message sequence %d, err: %v", streamDataMessage.SequenceNumber, err)
				//@ fold streamDataMessage.Mem()
				return err
			}
			streamDataMessage.Payload = plaintext
		}
		//@ fold streamDataMessage.Mem()

		// Ignore stream data message if handshake is neither skipped nor completed
		if !dc.hs.skipped && !dc.hs.complete {
			// this case should provably not occur as status `ReceiveOtherResponse`
			// is supposed to be sent on the `startReceivingChan` channel AFTER the
			// handshake has completed.
			// We can indeed proof the inexistence of this branch:
			// @ assert false
		}

		//@ fold acc(dc.Mem(), 1/2)
		//@ unfold dc.RecvRoutineMem()
		err = dc.inputStreamMessageHandler(log, streamDataMessage) /*@ as StreamDataHandlerSpec{dc.msgHandlerCtx} @*/
		//@ fold dc.RecvRoutineMem()
		if err != nil {
			dc.resendReceiveOtherResponse()
			return err
		}
		dc.resendReceiveOtherResponse()
	}

	return nil
}

// @ requires acc(dc.Mem(), 1/2) && dc.getState() == AgentSecretCreated && unfolding acc(dc.Mem(), 1/2) in dc.hs.complete
// @ preserves dc.RecvRoutineMem()
func (dc *dataChannel) resendReceiveOtherResponse() {
	//@ unfold acc(dc.Mem(), 1/2)
	//@ unfold dc.RecvRoutineMem()
	//@ fold acc(dc.Mem(), 1/2)
	//@ fold StartReceivingChanInv!<dc, _!>(ReceiveOtherResponse)
	dc.hs.startReceivingChan <- ReceiveOtherResponse
	//@ fold dc.RecvRoutineMem()
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

// handleHandshakeResponse is the handler for payload type HandshakeResponse
// @ requires log != nil && dc.MemTransfer(encryptionEnabled)
// @ preserves acc(log.Mem(), _) && dc.RecvRoutineMem()
// @ preserves streamDataMessage.Mem()
func (dc *dataChannel) handleHandshakeResponse(log logger.T, streamDataMessage *mgsContracts.AgentMessage, encryptionEnabled bool) error {
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

	actions := handshakeResponse.ProcessedClientActions
	//@ invariant dc.MemTransfer(encryptionEnabled)
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

				//@ unfold dc.MemTransfer(encryptionEnabled)
				agentId := dc.dataStream.GetInstanceId()
				//@ fold dc.MemTransfer(encryptionEnabled)
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

				//@ unfold dc.MemTransfer(encryptionEnabled)
				ok, err := dc.state.kmsService.Verify(resp.ClientLTKeyARN, clientSignPayloadBytes, sig /*@, perm(1/2) @*/)
				//@ fold dc.MemTransfer(encryptionEnabled)
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
				//@ unfold dc.MemTransfer(encryptionEnabled)
				ss, _ := elliptic.P384().ScalarMult(clientx, clienty, dc.state.agentSecret /*@, perm(1/2) @*/) // TODO: Double check it's fine to just use x
				dc.state.sharedSecret = ss.Bytes( /*@ perm(1/2) @*/ )

				// hash the shared secret to obtain the session identifier
				dc.state.sessionID = computeSHA384(dc.state.sharedSecret /*@, 1/2 @*/)

				log.Debugf("agent computed session ID: %v", base64.StdEncoding.EncodeToString(dc.state.sessionID /*@, perm(1/2) @*/))
				// decode the session ID
				var sessionIDBytes []byte
				sessionIDBytes, err = base64.StdEncoding.DecodeString(resp.SessionID)
				if err != nil {
					//@ fold dc.MemTransfer(encryptionEnabled)
					err = fmt.Errorf("failed to decode server session id: %v", err)
					log.Error(err)
					break
				}

				if !bytes.Equal(dc.state.sessionID, sessionIDBytes) {
					err = fmt.Errorf("session ID mismatch: session ID %s does not match client session ID %s", sessionIDBytes, dc.state.sessionID)
					//@ fold dc.MemTransfer(encryptionEnabled)
					log.Error(err)
					break
				}

				// use the shared secret to generate read and write keys
				dc.state.agentWriteKey, err = computeKdf(dc.state.sharedSecret, true /*@, 1/2 @*/)
				if err != nil {
					return err
				}
				dc.state.agentReadKey, err = computeKdf(dc.state.sharedSecret, false /*@, 1/2 @*/)
				if err != nil {
					return err
				}

				agentReadKey := dc.state.agentReadKey
				encodedAgentReadKey := base64.RawStdEncoding.EncodeToString(agentReadKey /*@, perm(1/2) @*/)
				agentWriteKey := dc.state.agentWriteKey
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

				//@ cryptoRand.GetReaderMem()
				encryptedSessionKeys, err := rsa.EncryptPKCS1v15(cryptoRand.Reader, dc.logLTPk, sessionKeysBytes /*@, perm(1/2) @*/)
				if err != nil {
					return fmt.Errorf("failed to encrypt session keys: %v", err)
				}
				encodedEncryptedSessionKeys := base64.StdEncoding.EncodeToString(encryptedSessionKeys /*@, perm(1/2) @*/)
				log.Infof("encrypted base-64-encoded session keys: %s", encodedEncryptedSessionKeys)

				// sign ciphertext containing session keys using KMS:
				signSessionKeysPayload := &mgsContracts.SignSessionKeysPayload{
					EncryptedSessionKeys: encodedEncryptedSessionKeys,
					ClientId:             dc.dataStream.GetClientId(),
				}

				//@ fold signSessionKeysPayload.Mem()
				signSessionKeysPayloadBytes, err := json.Marshal(signSessionKeysPayload /*@, perm(1/2) @*/)
				if err != nil {
					err = fmt.Errorf("failed to encode sign session keys payload: %v", err)
					log.Error(err)
					return err
				}

				sigSessionKeys, err := dc.state.kmsService.Sign(dc.agentLTKeyARN, signSessionKeysPayloadBytes /*@, perm(1/2) @*/)
				if err != nil {
					err = fmt.Errorf("failed to sign session keys payload: %v", err)
					log.Error(err)
					return err
				}

				encodedSigSessionKeys := base64.StdEncoding.EncodeToString(sigSessionKeys /*@, perm(1/2) @*/)

				// send ciphertext containing session keys and the corresponding signature to the log server:
				encryptedSessionKeysPayload := &mgsContracts.EncryptedSessionKeysPayload{
					AgentLTKeyARN:        dc.agentLTKeyARN,
					ClientId:             dc.dataStream.GetClientId(),
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

				dc.encryptionEnabled = true

				if err = dc.blockCipher.UpdateEncryptionKeys(log, dc.state.agentReadKey, dc.state.agentWriteKey /*@, perm(1/2) @*/); err != nil {
					//@ fold dc.MemTransfer(encryptionEnabled)
					err = fmt.Errorf("failed to update block cipher: %v", err)
					log.Error(err)
					break
				}
				//@ fold dc.MemTransfer(encryptionEnabled)
			// case mgsContracts.KMSEncryption:
			// 	err = dc.finalizeKMSEncryption(log, action.ActionResult)
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
			//@ unfold dc.MemTransfer(encryptionEnabled)
			dc.dataStream.CancelSession( /*@ perm(1/2) @*/ )
			// Set handshake error. Initiate handshake waits on handshake.responseChan and will return this error when channel returns.
			dc.hs.error = err
			//@ fold dc.MemTransfer(encryptionEnabled)
		}
	}
	//@ unfold dc.MemTransfer(encryptionEnabled)
	dc.hs.clientVersion = handshakeResponse.ClientVersion
	log.Infof("Client side session manager plugin version is: %s", handshakeResponse.ClientVersion)
	//@ fold dc.MemTransfer(encryptionEnabled)
	//@ fold ResponseChanInv!<dc, _!>(encryptionEnabled)
	//@ unfold dc.RecvRoutineMem()
	dc.hs.responseChan <- encryptionEnabled
	//@ fold dc.RecvRoutineMem()
	return nil
}

// SkipHandshake is used to skip handshake if the plugin decides it is not necessary
// @ requires log != nil
// @ preserves dc.Mem() && acc(log.Mem(), _)
// @ ensures err == nil ==> dc.getState() == HandshakeSkipped
func (dc *dataChannel) SkipHandshake(log logger.T) (err error) {
	if dc.getState() != Initialized {
		err = fmt.Errorf("DataChannel is in an invalid state %d", dc.getState())
		return
	}
	log.Info("Skipping handshake.")
	//@ unfold dc.Mem()
	dc.hs.skipped = true
	dc.dataChannelState = HandshakeSkipped
	//@ fold dc.Mem()
	return
}

// PerformHandshake performs handshake to share version string and encryption information with clients like cli/console
// Note that sessionplugin.go first calls `NewDataChannel` followed by at most 1 call to `PerformHandshake`.
// Hence, we can require in the specification that no other handshake is currently on-going for `dataChannel` without
// restricting the current client of `DataChannel`.
// @ requires log != nil
// @ preserves dc.Mem() && acc(log.Mem(), _)
// @ ensures err == nil ==> dc.getState() == HandshakeCompleted
func (dc *dataChannel) PerformHandshake(log logger.T,
	kmsKeyId string,
	encryptionEnabled bool,
	sessionTypeRequest mgsContracts.SessionTypeRequest) (err error) {

	if dc.getState() != Initialized {
		err = fmt.Errorf("DataChannel is in an invalid state %d", dc.getState())
		return
	}

	stdLog.Printf("PerformHandshake")

	//@ unfold dc.Mem()

	if encryptionEnabled {
		// if dc.blockCipher, err = newBlockCipher(dc.context, kmsKeyId); err != nil {
		// 	return fmt.Errorf("Initializing BlockCipher failed: %s", err)
		// }
		log.Info("Encryption enabled: initializing block cipher")
		// dc.blockCipher = &cryptolib.BlockCipherT{}
	}
	// initializing the block cipher independently of `encryptionEnabled` simplifies reasoning
	dc.blockCipher = &cryptolib.BlockCipherT{}
	//@ fold dc.blockCipher.Mem()

	dc.hs.handshakeStartTime = time.Now()
	dc.encryptionEnabled = encryptionEnabled
	dc.dataChannelState = BlockCipherInitialized
	//@ fold dc.Mem()

	log.Info("Initiating Handshake")
	stdLog.Printf("Initiating Handshake")
	handshakeRequestPayload, err :=
		dc.buildHandshakeRequestPayload(log, encryptionEnabled, sessionTypeRequest)
	if err != nil {
		return err
	}
	if err := dc.sendHandshakeRequest(log, handshakeRequestPayload); err != nil {
		return err
	}

	// notify Go routing handling received messages that it can process a message:
	//@ unfold dc.Mem()
	startReceivingChan := dc.hs.startReceivingChan
	responseChan := dc.hs.responseChan
	//@ fold dc.MemTransfer(encryptionEnabled)
	if encryptionEnabled {
		//@ fold StartReceivingChanInv!<dc, _!>(ReceiveHandshakeResponeEncryptionEnabled)
		startReceivingChan <- ReceiveHandshakeResponeEncryptionEnabled
	} else {
		//@ fold StartReceivingChanInv!<dc, _!>(ReceiveHandshakeResponeEncryptionDisabled)
		startReceivingChan <- ReceiveHandshakeResponeEncryptionDisabled
	}

	// Block until handshake response is received or handshake times out
	res, err := dc.tryReceiveResponseAlt(responseChan, handshakeTimeout)
	if err != nil {
		dc.dataChannelState = Erroneous
		//@ fold dc.Mem()
		// If handshake times out here this usually means that the client does not understand handshake or something
		// failed critically when processing handshake request.
		return errors.New("Handshake timed out. Please ensure that you have the latest version of the session manager plugin.")
	}
	// we send the flag `encryptionEnabled` back via the channel such that we are able to express the data channel's
	// state. This flag is expected to be identical to `encryptionEnabled`:
	if res != encryptionEnabled {
		dc.dataChannelState = Erroneous
		//@ fold dc.Mem()
		return errors.New("Unexpected result from processing handshake response")
	}
	//@ unfold ResponseChanInv!<dc, _!>(res)
	//@ unfold dc.MemTransfer(encryptionEnabled)
	err = dc.hs.error
	if err != nil {
		//@ fold dc.Mem()
		return err
	}
	stdLog.Printf("Handshake response received")

	dc.hs.handshakeEndTime = time.Now()
	//@ fold dc.Mem()
	handshakeCompletePayload, err := dc.buildHandshakeCompletePayload(log)
	if err != nil {
		return err
	}
	if err := dc.sendHandshakeComplete(log, handshakeCompletePayload); err != nil {
		return err
	}
	//@ unfold dc.Mem()
	dc.hs.complete = true
	dc.dataChannelState = HandshakeCompleted
	log.Info("Handshake successfully completed.")
	stdLog.Printf("Handshake successfully completed.")
	//@ fold dc.Mem()
	return
}

// buildHandshakeRequestPayload builds payload for HandshakeRequest
// @ requires log != nil && dc.Mem() && dc.getState() == BlockCipherInitialized
// @ preserves acc(log.Mem(), _)
// @ ensures  dc.Mem()
// @ ensures  err == nil ==> payload.Mem()
// @ ensures  err == nil && !encryptionRequested ==> dc.getState() == BlockCipherInitialized
// @ ensures  err == nil && encryptionRequested ==> dc.getState() == AgentSecretCreated
func (dc *dataChannel) buildHandshakeRequestPayload(log logger.T,
	encryptionRequested bool,
	request mgsContracts.SessionTypeRequest) (payload *mgsContracts.HandshakeRequestPayload, err error) {

	handshakeRequest := &mgsContracts.HandshakeRequestPayload{}
	handshakeRequest.AgentVersion = version.Version
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

		//@ unfold dc.Mem()
		dc.state.agentSecret = agentSecret

		// Base64 encode the public part and put it in the message
		agentShare := elliptic.MarshalCompressed(elliptic.P384(), x, y /*@, perm(1/2) @*/)
		compressedPublic := base64.StdEncoding.EncodeToString(agentShare /*@, perm(1/2) @*/)

		dc.state.kmsService, err = dc.dataStream.GetKMSService( /*@ perm(1/2) @*/ )
		if err != nil {
			//@ fold dc.Mem()
			err = fmt.Errorf("failed to initialize KMS service: %v", err)
			log.Error(err)
			return nil, err
		}

		// TODO: do this beforehand and set `dc.agentLTKeyARN` and `dc.logLTPk`
		metadata, err := dc.state.kmsService.CreateKeyAssymetric()
		if err != nil {
			//@ fold dc.Mem()
			err = fmt.Errorf("failed to create agent LTK: %v", err)
			log.Error(err)
			return nil, err
		}

		//@ unfold metadata.Mem()
		if metadata.Arn == nil {
			//@ fold dc.Mem()
			err = fmt.Errorf("asymmetric key ARN is nil, metadata: %+v", metadata)
			log.Error(err)
			return nil, err
		}
		dc.agentLTKeyARN = *metadata.Arn
		sk, err := rsa.GenerateKey(cryptoRand.Reader, 4096 /*@, perm(1/2) @*/)
		if err != nil {
			//@ fold dc.Mem()
			err = fmt.Errorf("failed to create log secret key: %v", err)
			log.Error(err)
			return nil, err
		}
		//@ unfold sk.Mem()
		dc.logLTPk = &sk.PublicKey
		// only now do we have all permissions required to satisfy the state transition:
		dc.dataChannelState = AgentSecretCreated

		signPayload := &mgsContracts.SignAgentSharePayload{
			AgentShare:  compressedPublic,
			ClientId:    dc.dataStream.GetClientId(),
			LogReaderId: dc.logReaderId,
		}

		//@ fold signPayload.Mem()
		signPayloadBytes, err := json.Marshal(signPayload /*@, perm(1/2) @*/)
		if err != nil {
			//@ fold dc.Mem()
			err = fmt.Errorf("failed to encode sign payload: %v", err)
			log.Error(err)
			return nil, err
		}

		sig, err := dc.state.kmsService.Sign(dc.agentLTKeyARN, signPayloadBytes /*@, perm(1/2) @*/)
		if err != nil {
			//@ fold dc.Mem()
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
			AgentLTKeyARN:  dc.agentLTKeyARN,
			LogReaderId:    dc.logReaderId,
		}
		//@ fold dc.Mem()

		log.Debugf("client generated SecureSessionRequest: %+v", req)

		secureSessionAction := mgsContracts.RequestedClientAction{
			ActionType:       mgsContracts.SecureSession,
			ActionParameters: req,
		}
		handshakeRequest.RequestedClientActions = []mgsContracts.RequestedClientAction{sessionTypeAction, secureSessionAction}
		//@ fold handshakeRequest.Mem()
	} else {
		handshakeRequest.RequestedClientActions = []mgsContracts.RequestedClientAction{sessionTypeAction}
		//@ fold handshakeRequest.Mem()
	}

	return handshakeRequest, nil
}

// buildHandshakeCompletePayload builds payload for HandshakeComplete
// @ requires log != nil && dc.Mem() && dc.getState() != Erroneous
// @ preserves acc(log.Mem(), _)
// @ ensures dc.Mem() && dc.getState() == old(dc.getState())
// @ ensures err == nil ==> payload.Mem()
func (dc *dataChannel) buildHandshakeCompletePayload(log logger.T) (payload *mgsContracts.HandshakeCompletePayload, err error) {
	handshakeComplete := &mgsContracts.HandshakeCompletePayload{}
	//@ unfold dc.Mem()
	handshakeComplete.HandshakeTimeToComplete =
		dc.hs.handshakeEndTime.Sub(dc.hs.handshakeStartTime)
	//@ fold dc.Mem()
	clientVersion, err := dc.GetClientVersion( /*@ perm(1/2) @*/ )
	if err != nil {
		return nil, err
	}
	//@ unfold dc.Mem()
	if dc.separateOutputPayload == true && versionutil.Compare(clientVersion, clientVersionWithoutOutputSeparation, true) <= 0 {
		handshakeComplete.CustomerMessage = "Please update session manager plugin version (minimum required version " +
			firstVersionWithOutputSeparationFeature +
			") for fully support of separate StdOut/StdErr output.\r\n"
	}

	if dc.encryptionEnabled {
		handshakeComplete.CustomerMessage += "This session is encrypted using AWS KMS."
	}
	//@ fold dc.Mem()
	//@ fold handshakeComplete.Mem()

	return handshakeComplete, nil
}

// sendHandshakeRequest sends handshake request
// @ requires log != nil && handshakeRequestPayload.Mem()
// @ requires dc.Mem() && dc.getState() >= BlockCipherInitialized
// @ preserves acc(log.Mem(), _)
// @ ensures dc.Mem() && dc.getState() == old(dc.getState())
func (dc *dataChannel) sendHandshakeRequest(log logger.T, handshakeRequestPayload *mgsContracts.HandshakeRequestPayload) (err error) {
	var handshakeRequestPayloadBytes []byte
	if handshakeRequestPayloadBytes, err = json.Marshal(handshakeRequestPayload /*@, perm(1/2) @*/); err != nil {
		return fmt.Errorf("Could not serialize HandshakeRequest message %v, err: %s", handshakeRequestPayload, err)
	}

	log.Debug("Sending Handshake Request.")
	log.Tracef("Sending HandshakeRequest message with content %v", handshakeRequestPayload)
	if err = dc.sendData(log, mgsContracts.HandshakeRequest, handshakeRequestPayloadBytes /*@, perm(1/2) @*/); err != nil {
		return fmt.Errorf("Failed sending of HandshakeRequest message, err: %s", err)
	}
	return nil
}

// sendHandshakeComplete sends handshake complete
// @ requires log != nil && handshakeCompletePayload.Mem()
// @ requires dc.Mem() && dc.getState() >= BlockCipherInitialized
// @ preserves acc(log.Mem(), _)
// @ ensures dc.Mem() && dc.getState() == old(dc.getState())
func (dc *dataChannel) sendHandshakeComplete(log logger.T, handshakeCompletePayload *mgsContracts.HandshakeCompletePayload) (err error) {
	var handshakeCompletePayloadBytes []byte
	if handshakeCompletePayloadBytes, err = json.Marshal(handshakeCompletePayload /*@, perm(1/2) @*/); err != nil {
		return fmt.Errorf("Could not serialize HandshakeComplete message %v, err: %s", handshakeCompletePayload, err)
	}

	log.Debug("Sending HandshakeComplete.")
	log.Tracef("Sending HandshakeComplete message with content %v", handshakeCompletePayload)
	if err = dc.sendData(log, mgsContracts.HandshakeComplete, handshakeCompletePayloadBytes /*@, perm(1/2) @*/); err != nil {
		return err
	}
	return nil
}

// GetClientVersion returns version of the client
// @ requires noPerm < p
// @ preserves acc(dc.Mem(), p)
func (dc *dataChannel) GetClientVersion( /*@ ghost p perm @*/ ) (version string, err error) {
	if dc.getState() == Erroneous {
		err = fmt.Errorf("DataChannel is in an invalid state %d", dc.getState())
		return
	}
	return /*@ unfolding acc(dc.Mem(), p) in @*/ dc.hs.clientVersion, nil
}

// GetInstanceId returns id of the target
// @ requires noPerm < p
// @ preserves acc(dc.Mem(), p)
func (dc *dataChannel) GetInstanceId( /*@ ghost p perm @*/ ) (instanceId string, err error) {
	if dc.getState() < Initialized {
		err = fmt.Errorf("DataChannel is in an invalid state %d", dc.getState())
		return
	}
	return /*@ unfolding acc(dc.Mem(), p) in @*/ dc.dataStream.GetInstanceId(), nil
}

// GetRegion returns aws region of the target
// @ requires noPerm < p
// @ preserves acc(dc.Mem(), p)
func (dc *dataChannel) GetRegion( /*@ ghost p perm @*/ ) (region string, err error) {
	if dc.getState() < Initialized {
		err = fmt.Errorf("DataChannel is in an invalid state %d", dc.getState())
		return
	}
	return /*@ unfolding acc(dc.Mem(), p) in @*/ dc.dataStream.GetRegion(), nil
}

// IsActive returns a boolean value indicating the datachannel is actively listening
// and communicating with service
// @ requires noPerm < p
// @ preserves acc(dc.Mem(), p)
func (dc *dataChannel) IsActive( /*@ ghost p perm @*/ ) (isActive bool, err error) {
	if dc.getState() < Initialized {
		err = fmt.Errorf("DataChannel is in an invalid state %d", dc.getState())
		return
	}
	return /*@ unfolding acc(dc.Mem(), p) in @*/ dc.dataStream.IsActive(), nil
}

// GetSeparateOutputPayload returns boolean value indicating separate
// stdout/stderr output for non-interactive session or not
// @ requires noPerm < p
// @ preserves acc(dc.Mem(), p)
func (dc *dataChannel) GetSeparateOutputPayload( /*@ ghost p perm @*/ ) (res bool, err error) {
	if dc.getState() == Erroneous {
		err = fmt.Errorf("DataChannel is in an invalid state %d", dc.getState())
		return
	}
	return /*@ unfolding acc(dc.Mem(), _) in @*/ dc.separateOutputPayload, nil
}

// SetSeparateOutputPayload set separateOutputPayload value
// @ preserves dc.Mem()
// @ ensures dc.getState() == old(dc.getState())
func (dc *dataChannel) SetSeparateOutputPayload(separateOutputPayload bool) (err error) {
	if dc.getState() == Erroneous {
		err = fmt.Errorf("DataChannel is in an invalid state %d", dc.getState())
		return
	}
	//@ unfold dc.Mem()
	dc.separateOutputPayload = separateOutputPayload
	//@ fold dc.Mem()
	return
}

// @ requires log != nil
// @ preserves dc.Mem() && acc(log.Mem(), _)
// @ ensures dc.getState() == old(dc.getState())
func (dc *dataChannel) PrepareToCloseChannel(log logger.T) (err error) {
	if dc.getState() < Initialized {
		err = fmt.Errorf("DataChannel is in an invalid state %d", dc.getState())
		return
	}
	//@ unfold dc.Mem()
	dc.dataStream.PrepareToCloseChannel(log)
	//@ fold dc.Mem()
	return
}

// @ requires log != nil
// @ preserves dc.Mem() && acc(log.Mem(), _)
// @ ensures dc.getState() == old(dc.getState())
func (dc *dataChannel) Close(log logger.T) (err error) {
	if dc.getState() < Initialized {
		err = fmt.Errorf("DataChannel is in an invalid state %d", dc.getState())
		return
	}
	//@ unfold dc.Mem()
	err = dc.dataStream.Close(log)
	//@ fold dc.Mem()
	return
}
