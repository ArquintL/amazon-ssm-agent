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
	"crypto/rsa"
	"time"
	//@ "bytes"
	//@ "sync"

	logger "github.com/aws/amazon-ssm-agent/agent/log"
	mgsContracts "github.com/aws/amazon-ssm-agent/agent/session/contracts"
	"github.com/aws/amazon-ssm-agent/agent/session/crypto"
	"github.com/aws/amazon-ssm-agent/agent/session/datachannel/cryptolib"
	"github.com/aws/amazon-ssm-agent/agent/session/datastream"
	//@ abs "github.com/aws/amazon-ssm-agent/agent/iospecs/abs"
	//@ by "github.com/aws/amazon-ssm-agent/agent/iospecs/bytes"
	//@ ft "github.com/aws/amazon-ssm-agent/agent/iospecs/fact"
	//@ "github.com/aws/amazon-ssm-agent/agent/iospecs/iospec"
	//@ pl "github.com/aws/amazon-ssm-agent/agent/iospecs/place"
	//@ pub "github.com/aws/amazon-ssm-agent/agent/iospecs/pub"
	//@ tm "github.com/aws/amazon-ssm-agent/agent/iospecs/term"
	//@ "github.com/aws/amazon-ssm-agent/agent/session/datachannel/iosanitization"
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

	// @ pred Mem()

	// @ preserves Mem()
	// @ preserves log != nil ==> acc(log.Mem(), _)
	// @ preserves inputData != nil ==> bytes.SliceMem(inputData)
	// @ ensures   err != nil ==> err.ErrorMem()
	SendStreamDataMessage(log logger.T, dataType mgsContracts.PayloadType, inputData []byte) (err error)

	// @ preserves Mem()
	// @ preserves log != nil ==> acc(log.Mem(), _)
	// @ ensures   err != nil ==> err.ErrorMem()
	SendAgentSessionStateMessage(log logger.T, sessionStatus mgsContracts.SessionStatus) (err error)

	// @ preserves Mem()
	// @ preserves log != nil ==> acc(log.Mem(), _)
	// @ ensures   err != nil ==> err.ErrorMem()
	SkipHandshake(log logger.T) (err error)

	// @ requires  encryptionEnabled == assumeEncryptionEnabledForVerification()
	// @ preserves Mem()
	// @ preserves log != nil ==> acc(log.Mem(), _)
	// @ preserves sessionTypeRequest.Mem()
	// @ ensures   err != nil ==> err.ErrorMem()
	PerformHandshake(log logger.T, kmsKeyId string, encryptionEnabled bool, sessionTypeRequest mgsContracts.SessionTypeRequest) (err error)

	// @ preserves Mem()
	// @ ensures   err != nil ==> err.ErrorMem()
	GetClientVersion() (version string, err error)

	// @ preserves Mem()
	// @ ensures   err != nil ==> err.ErrorMem()
	GetInstanceId() (instanceId string, err error)

	// @ preserves Mem()
	// @ ensures   err != nil ==> err.ErrorMem()
	GetRegion() (region string, err error)

	// @ preserves Mem()
	// @ ensures   err != nil ==> err.ErrorMem()
	IsActive() (isActive bool, err error)

	// @ preserves Mem()
	// @ ensures   err != nil ==> err.ErrorMem()
	GetSeparateOutputPayload() (res bool, err error)

	// @ preserves Mem()
	// @ ensures  err != nil ==> err.ErrorMem()
	SetSeparateOutputPayload(separateOutputPayload bool) (err error)

	// @ preserves Mem()
	// @ preserves log != nil ==> acc(log.Mem(), _)
	// @ ensures   err != nil ==> err.ErrorMem()
	PrepareToCloseChannel(log logger.T) (err error)

	// @ preserves Mem()
	// @ preserves log != nil ==> acc(log.Mem(), _)
	// @ ensures   err != nil ==> err.ErrorMem()
	Close(log logger.T) (err error)
}

type DataChannelState int

const (
	Erroneous                   DataChannelState = 0
	Uninitialized               DataChannelState = 1
	Initialized                 DataChannelState = 2
	HandshakeSkipped            DataChannelState = 3
	BlockCipherInitialized      DataChannelState = 4
	AgentSecretCreatedAndSigned DataChannelState = 5
	HandshakeRequestSent        DataChannelState = 6
	HandshakeResponseReceived   DataChannelState = 7
	HandshakeResponseVerified   DataChannelState = 8
	BlockCipherReady            DataChannelState = 9
	HandshakeCompleted          DataChannelState = 10
	IODistributed               DataChannelState = 11
)

type InputStreamMessageHandler = func(streamDataMessage *mgsContracts.AgentMessage /*@, ghost t pl.Place, ghost rid tm.Term, ghost agentMessageT tm.Term @*/) error

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
	// kmsService is the KMS service used to sign and verify the handshake keyshare
	kmsService *crypto.KMSService
	// Indicates whether encryption was enabled
	encryptionEnabled     bool
	separateOutputPayload bool
	secrets               agentHandshakeSecrets
	logReaderId           string
	logLTPk               *rsa.PublicKey

	instanceId string
	clientId   string

	//@ ghost io gpointer[ioSpecFields]
	// ghost lock to synchronize consuming I/O permissions for sending and receiving transport messages
	//@ ghost ioLock gpointer[sync.GhostMutex]
	//@ ghost ioLockDidLocalReceive bool
	//@ ghost ioLockCanRemoteSend bool
	//@ ghost ioLockDidRemoteReceive bool
	//@ ghost ioLockCanLocalSend bool
}

/*@
type ioSpecFields struct {
	ghost token pl.Place
	ghost rid tm.Term
	ghost absState mset[ft.Fact]
	ghost agentIdT tm.Term
	ghost kMSIdT tm.Term
	ghost clientIdT tm.Term
	ghost readerIdT tm.Term
	ghost logLTPkT tm.Term
	ghost agentShareT tm.Term
	ghost agentShareSignatureT tm.Term
	ghost inFactT tm.Term
	ghost sharedSecretT tm.Term
	ghost clientLtKeyIdT tm.Term
	ghost clientShareT tm.Term
	ghost clientShareSignatureT tm.Term
	ghost sigSessionKeysT tm.Term
	ghost localInFactT tm.Term
	ghost remoteInFactT tm.Term
	ghost localOutFactT tm.Term
	ghost remoteOutFactT tm.Term
}
@*/

// agentHandshakeSecrets represents the secrets used in the handshake.
type agentHandshakeSecrets struct {
	agentSecret   []byte
	sharedSecret  []byte
	sessionID     []byte
	agentWriteKey []byte
	agentReadKey  []byte
	// agentLTKeyARN is the ARN for the KMS long-term-key used to sign and verify the handshake
	agentLTKeyARN string
}

type MessageReceptionStatus int
type MessageReceptionPayload struct {
	status MessageReceptionStatus
	data   interface{}
}

type ResponseChanPayload struct {
	encryptionEnabled bool
	state             DataChannelState
}

const (
	ReceiveHandshakeResponeEncryptionEnabled  MessageReceptionStatus = 1
	ReceiveHandshakeResponeEncryptionDisabled MessageReceptionStatus = 2
	ReceiveOtherResponse                      MessageReceptionStatus = 3
)

type handshake struct {
	// Version of the client
	clientVersion string
	// Channel used to signal that a message is to be expected
	startReceivingChan chan MessageReceptionPayload
	// Channel used to signal when handshake response is received
	responseChan chan ResponseChanPayload
	error        error
	// Indicates handshake is complete (Handshake Complete message sent to client)
	complete bool
	// Indiciates if handshake has been skipped
	skipped            bool
	handshakeStartTime time.Time
	handshakeEndTime   time.Time
}

// @ decreases
// @ requires acc(dc.Mem(), _)
// @ pure
func (dc *dataChannel) getState() DataChannelState {
	return /*@ unfolding acc(dc.Mem(), _) in @*/ dc.dataChannelState
}

// @ decreases
// @ requires acc(dc.Mem(), _) && dc.getState() != Erroneous
// @ pure
func (dc *dataChannel) isHandshakeCompleted() bool {
	return /*@ unfolding acc(dc.Mem(), _) in unfolding acc(dc.MemInternal(dc.dataChannelState), _) in @*/ dc.hs.complete
}

// @ decreases
// @ requires acc(dc.Mem(), _) && dc.getState() != Erroneous
// @ pure
func (dc *dataChannel) getAgentLTKeyARN() string {
	return /*@ unfolding acc(dc.Mem(), _) in unfolding acc(dc.MemInternal(dc.dataChannelState), _) in @*/ dc.secrets.agentLTKeyARN
}

// @ decreases
// @ requires acc(dc.Mem(), _) && dc.getState() != Erroneous
// @ pure
func (dc *dataChannel) getLogReaderId() string {
	return /*@ unfolding acc(dc.Mem(), _) in unfolding acc(dc.MemInternal(dc.dataChannelState), _) in @*/ dc.logReaderId
}

/*@
pred (dc *dataChannel) Mem() {
	dc != nil &&
	acc(&dc.dataChannelState, 1/2) &&
	(dc.dataChannelState != IODistributed ==>
		acc(dc.MemChannelState(), 1/2)) &&
	acc(dc.MemInternal(dc.dataChannelState), dc.dataChannelState != IODistributed ? writePerm : perm(1/2))
}

// due to an incompleteness, we need this indirection
pred (dc *dataChannel) MemChannelState() {
	acc(&dc.dataChannelState)
}

pred (dc *dataChannel) MemInternal(state DataChannelState) {
	dc != nil &&
	acc(&dc.hs.startReceivingChan, _) &&
	acc(&dc.hs.responseChan, _) &&
	acc(dc.hs.startReceivingChan.SendChannel(), _) &&
	dc.hs.startReceivingChan.SendGivenPerm() == StartReceivingChanInv!<dc, _!> &&
	dc.hs.startReceivingChan.SendGotPerm() == PredTrue!<!> &&
	acc(dc.hs.responseChan.RecvChannel(), _) &&
	dc.hs.responseChan.RecvGivenPerm() == PredTrue!<!> &&
	dc.hs.responseChan.RecvGotPerm() == ResponseChanInv!<dc, _!> &&
	(state != Erroneous ==>
		acc(&dc.dataStream) &&
		acc(&dc.hs.clientVersion) &&
		acc(&dc.hs.error) && dc.hs.error == nil &&
		acc(&dc.hs.complete) &&
		acc(&dc.hs.skipped) &&
		acc(&dc.hs.handshakeStartTime) &&
		acc(&dc.hs.handshakeEndTime) &&
		acc(&dc.blockCipher) &&
		acc(&dc.kmsService) &&
		acc(&dc.encryptionEnabled) &&
		acc(&dc.separateOutputPayload) &&
		acc(&dc.secrets) &&
		acc(&dc.logReaderId) &&
		acc(&dc.logLTPk) &&
		acc(&dc.instanceId) &&
		acc(&dc.clientId) &&
		acc(&dc.ioLock) &&
		acc(&dc.io, 1/2)) &&
	(state != Erroneous && state < IODistributed ==>
		acc(&dc.ioLockDidLocalReceive) && acc(&dc.ioLockCanRemoteSend) &&
		acc(&dc.ioLockDidRemoteReceive) && acc(&dc.ioLockCanLocalSend) &&
		acc(&dc.io.localInFactT) && acc(&dc.io.remoteInFactT) &&
		acc(&dc.io.localOutFactT) && acc(&dc.io.remoteOutFactT)) &&
	(state >= Initialized ==>
		dc.io.IoSpecMemPartial() &&
		dc.dataStream.Mem() &&
		dc.kmsService.Mem() &&
		dc.logLTPk.Mem()) &&
	(state >= Initialized && state < IODistributed ==>
		acc(&dc.io, 1/2) &&
		dc.io.IoSpecMemMain() &&
		pl.token(dc.io.getToken()) &&
		iospec.P_Agent(dc.io.getToken(), dc.io.getRid(), dc.io.getAbsState()) &&
		tm.pubTerm(pub.pub_msg(dc.instanceId)) == dc.io.getAgentIdT() &&
		tm.pubTerm(pub.pub_msg(dc.clientId)) == dc.io.getClientIdT() &&
		tm.pubTerm(pub.pub_msg(dc.logReaderId)) == dc.io.getReaderIdT() &&
		by.gamma(dc.io.getLogLTPkT()) == dc.logLTPk.Abs()) &&
	(state == Initialized ==>
		!dc.hs.skipped) &&
	(state == HandshakeSkipped ==>
		dc.hs.skipped) &&
	(state >= BlockCipherInitialized ==>
		!dc.hs.skipped &&
		dc.encryptionEnabled == assumeEncryptionEnabledForVerification() &&
		dc.blockCipher != nil && dc.blockCipher.Mem()) &&
	(state >= AgentSecretCreatedAndSigned && state < HandshakeCompleted ==>
		bytes.SliceMem(dc.secrets.agentSecret) &&
		by.gamma(dc.io.getAgentShareT()) == abs.Abs(dc.secrets.agentSecret)) &&
	(state >= BlockCipherReady && dc.encryptionEnabled ==>
		dc.blockCipher.IsReady() &&
		dc.io.getSharedSecretT() == tm.exp(tm.exp(tm.pubTerm(pub.const_g_pub()), dc.io.getClientShareT()), dc.io.getAgentShareT()) &&
		dc.blockCipher.GetEncKeyT() == tm.kdf1(dc.io.getSharedSecretT()) &&
		dc.blockCipher.GetDecKeyT() == tm.kdf2(dc.io.getSharedSecretT())) &&
	// relate state to abstract state:
	(state == Initialized || state == BlockCipherInitialized ==>
		ft.Setup_Agent(dc.io.getRid(), dc.io.getAgentIdT(), dc.io.getKMSIdT(), dc.io.getClientIdT(), dc.io.getReaderIdT(), tm.pubTerm(pub.pub_msg(dc.secrets.agentLTKeyARN)), dc.io.getLogLTPkT()) in dc.io.getAbsState()) &&
	(state == AgentSecretCreatedAndSigned ==>
		ft.St_Agent_2(dc.io.getRid(), dc.io.getAgentIdT(), dc.io.getKMSIdT(), dc.io.getClientIdT(), dc.io.getReaderIdT(), tm.pubTerm(pub.pub_msg(dc.secrets.agentLTKeyARN)), dc.io.getLogLTPkT(), dc.io.getAgentShareT(), dc.io.getAgentShareSignatureT()) in dc.io.getAbsState()) &&
	(state == HandshakeRequestSent ==>
		ft.St_Agent_3(dc.io.getRid(), dc.io.getAgentIdT(), dc.io.getKMSIdT(), dc.io.getClientIdT(), dc.io.getReaderIdT(), tm.pubTerm(pub.pub_msg(dc.secrets.agentLTKeyARN)), dc.io.getLogLTPkT(), dc.io.getAgentShareT(), dc.io.getAgentShareSignatureT()) in dc.io.getAbsState()) &&
	(state == BlockCipherReady ==>
		ft.St_Agent_9(dc.io.getRid(), dc.io.getAgentIdT(), dc.io.getKMSIdT(), dc.io.getClientIdT(), dc.io.getReaderIdT(), tm.pubTerm(pub.pub_msg(dc.secrets.agentLTKeyARN)), dc.io.getLogLTPkT(), dc.io.getAgentShareT(), dc.io.getAgentShareSignatureT(), dc.io.getClientLtKeyIdT(), tm.exp(tm.pubTerm(pub.const_g_pub()), dc.io.getClientShareT()), dc.io.getClientShareSignatureT(), dc.io.getSigSessionKeysT()) in dc.io.getAbsState()) &&
	(state == HandshakeCompleted ==>
		ft.St_Agent_10(dc.io.getRid(), dc.io.getAgentIdT(), dc.io.getKMSIdT(), dc.io.getClientIdT(), dc.io.getReaderIdT(), tm.pubTerm(pub.pub_msg(dc.secrets.agentLTKeyARN)), dc.io.getLogLTPkT(), dc.io.getAgentShareT(), dc.io.getAgentShareSignatureT(), dc.io.getClientLtKeyIdT(), tm.exp(tm.pubTerm(pub.const_g_pub()), dc.io.getClientShareT()), dc.io.getClientShareSignatureT(), dc.io.getSigSessionKeysT()) in dc.io.getAbsState()) &&
	(state == IODistributed ==>
		// the idea is that the receiving thread does not get permission to Mem() but a reduced invariant:
		acc(&dc.ioLockDidLocalReceive) && acc(&dc.ioLockCanRemoteSend) &&
		acc(&dc.io.localInFactT) && acc(&dc.io.remoteOutFactT) &&
		acc(dc.ioLock.LockP()) && dc.ioLock.LockInv() == IoLockInv!<dc, dc.instanceId, dc.clientId, dc.secrets.agentLTKeyARN!>)
}

// `MemTransfer` is the predicate that is passed to the go routine handling the incoming message during
// the handshake.
pred (dc *dataChannel) MemTransfer(state DataChannelState, encryptionEnabled bool) {
	dc != nil &&
	acc(&dc.dataStream) &&
	acc(&dc.hs.clientVersion) &&
	acc(&dc.hs.startReceivingChan, _) &&
	acc(&dc.hs.responseChan, _) &&
	acc(&dc.hs.error) &&
	(dc.hs.error != nil ==> dc.hs.error.ErrorMem()) &&
	acc(&dc.hs.complete) &&
	acc(&dc.hs.skipped) &&
	acc(&dc.hs.handshakeStartTime) &&
	acc(&dc.hs.handshakeEndTime) &&
	acc(&dc.blockCipher) &&
	acc(&dc.kmsService) &&
	acc(&dc.encryptionEnabled) &&
	acc(&dc.separateOutputPayload) &&
	acc(&dc.secrets) &&
	acc(&dc.logReaderId) &&
	acc(&dc.logLTPk) &&
	acc(&dc.instanceId) &&
	acc(&dc.clientId) &&
	dc.dataStream.Mem() &&
	acc(dc.hs.startReceivingChan.SendChannel(), _) &&
	dc.hs.startReceivingChan.SendGivenPerm() == StartReceivingChanInv!<dc, _!> &&
	dc.hs.startReceivingChan.SendGotPerm() == PredTrue!<!> &&
	!dc.hs.skipped &&
	dc.encryptionEnabled == assumeEncryptionEnabledForVerification() &&
	dc.blockCipher != nil && dc.blockCipher.Mem() &&
	acc(&dc.io, 1/2) &&
	dc.io.IoSpecMemMain() &&
	dc.io.IoSpecMemPartial() &&
	(state != Erroneous ==>
		pl.token(dc.io.getToken()) &&
		iospec.P_Agent(dc.io.getToken(), dc.io.getRid(), dc.io.getAbsState())) &&
	tm.pubTerm(pub.pub_msg(dc.instanceId)) == dc.io.getAgentIdT() &&
	tm.pubTerm(pub.pub_msg(dc.clientId)) == dc.io.getClientIdT() &&
	tm.pubTerm(pub.pub_msg(dc.logReaderId)) == dc.io.getReaderIdT() &&
	by.gamma(dc.io.getLogLTPkT()) == dc.logLTPk.Abs() &&
	(encryptionEnabled ==>
		dc.logLTPk.Mem() &&
		dc.kmsService.Mem() &&
		bytes.SliceMem(dc.secrets.agentSecret) &&
		by.gamma(dc.io.getAgentShareT()) == abs.Abs(dc.secrets.agentSecret)) &&
	(state == HandshakeRequestSent ==>
		ft.St_Agent_3(dc.io.getRid(), dc.io.getAgentIdT(), dc.io.getKMSIdT(), dc.io.getClientIdT(), dc.io.getReaderIdT(), tm.pubTerm(pub.pub_msg(dc.secrets.agentLTKeyARN)), dc.io.getLogLTPkT(), dc.io.getAgentShareT(), dc.io.getAgentShareSignatureT()) in dc.io.getAbsState()) &&
	(state >= HandshakeResponseReceived ==>
		bytes.SliceMem(dc.secrets.sharedSecret) &&
		// TODO: we could technically remove `getSharedSecretT` as it only acts as an abbreviation:
		dc.io.getSharedSecretT() == tm.exp(tm.exp(tm.pubTerm(pub.const_g_pub()), dc.io.getClientShareT()), dc.io.getAgentShareT()) &&
		by.gamma(dc.io.getSharedSecretT()) == abs.Abs(dc.secrets.sharedSecret)) &&
	(state == HandshakeResponseVerified ==>
		ft.St_Agent_6(dc.io.getRid(), dc.io.getAgentIdT(), dc.io.getKMSIdT(), dc.io.getClientIdT(), dc.io.getReaderIdT(), tm.pubTerm(pub.pub_msg(dc.secrets.agentLTKeyARN)), dc.io.getLogLTPkT(), dc.io.getAgentShareT(), dc.io.getAgentShareSignatureT(), dc.io.getClientLtKeyIdT(), tm.exp(tm.pubTerm(pub.const_g_pub()), dc.io.getClientShareT()), dc.io.getClientShareSignatureT()) in dc.io.getAbsState()) &&
	(state == BlockCipherReady ==>
		(encryptionEnabled ==>
			dc.blockCipher.IsReady() &&
			dc.blockCipher.GetEncKeyT() == tm.kdf1(dc.io.getSharedSecretT()) &&
			dc.blockCipher.GetDecKeyT() == tm.kdf2(dc.io.getSharedSecretT())) &&
		ft.St_Agent_9(dc.io.getRid(), dc.io.getAgentIdT(), dc.io.getKMSIdT(), dc.io.getClientIdT(), dc.io.getReaderIdT(), tm.pubTerm(pub.pub_msg(dc.secrets.agentLTKeyARN)), dc.io.getLogLTPkT(), dc.io.getAgentShareT(), dc.io.getAgentShareSignatureT(), dc.io.getClientLtKeyIdT(), tm.exp(tm.pubTerm(pub.const_g_pub()), dc.io.getClientShareT()), dc.io.getClientShareSignatureT(), dc.io.getSigSessionKeysT()) in dc.io.getAbsState())
}

// `MemRecv` is the predicate on which the goroutine receiving transport messages operates on.
pred (dc *dataChannel) MemRecv() {
	dc != nil &&
	acc(&dc.dataChannelState, 1/2) &&
	dc.dataChannelState == IODistributed &&
	acc(&dc.ioLock, 1/2) &&
	acc(&dc.hs.startReceivingChan, _) &&
	acc(&dc.hs.responseChan, _) &&
	acc(dc.hs.startReceivingChan.SendChannel(), _) &&
	dc.hs.startReceivingChan.SendGivenPerm() == StartReceivingChanInv!<dc, _!> &&
	dc.hs.startReceivingChan.SendGotPerm() == PredTrue!<!> &&
	acc(&dc.dataStream, 1/2) &&
	acc(&dc.hs.clientVersion, 1/2) &&
	acc(&dc.hs.error, 1/2) &&
	acc(&dc.hs.complete, 1/2) &&
	acc(&dc.hs.skipped, 1/2) &&
	acc(&dc.hs.handshakeStartTime, 1/2) &&
	acc(&dc.hs.handshakeEndTime, 1/2) &&
	acc(&dc.encryptionEnabled, 1/2) &&
	dc.encryptionEnabled == assumeEncryptionEnabledForVerification() &&
	acc(&dc.blockCipher, 1/2) &&
	acc(dc.blockCipher.Mem(), 1/2) &&
	(dc.encryptionEnabled ==> dc.blockCipher.IsReady()) &&
	acc(&dc.separateOutputPayload, 1/2) &&
	acc(&dc.secrets, 1/2) &&
	acc(&dc.logReaderId, 1/2) &&
	acc(&dc.logLTPk, 1/2) &&
	acc(&dc.instanceId, 1/2) &&
	acc(&dc.clientId, 1/2) &&
	acc(dc.dataStream.Mem(), 1/2) &&
	acc(&dc.kmsService, 1/2) &&
	acc(dc.kmsService.Mem(), 1/2) &&
	acc(dc.logLTPk.Mem(), 1/2) &&
	acc(&dc.io, 1/4) &&
	acc(dc.io.IoSpecMemPartial(), 1/4) &&
	dc.io.getSharedSecretT() == tm.exp(tm.exp(tm.pubTerm(pub.const_g_pub()), dc.io.getClientShareT()), dc.io.getAgentShareT()) &&
	dc.blockCipher.GetEncKeyT() == tm.kdf1(dc.io.getSharedSecretT()) &&
	dc.blockCipher.GetDecKeyT() == tm.kdf2(dc.io.getSharedSecretT()) &&
	acc(&dc.ioLockCanLocalSend, 1/2) && acc(&dc.ioLockDidRemoteReceive, 1/2) &&
	acc(&dc.io.localOutFactT, 1/2) && acc(&dc.io.remoteInFactT, 1/2) &&
	acc(dc.ioLock.LockP(), 1/2) && dc.ioLock.LockInv() == IoLockInv!<dc, dc.instanceId, dc.clientId, dc.secrets.agentLTKeyARN!>
}

pred (dc *dataChannel) Inv() {
	dc.RecvRoutineMem()
}

pred (dc *dataChannel) RecvRoutineMem() {
	dc != nil &&
	acc(&dc.inputStreamMessageHandler) &&
	dc.inputStreamMessageHandler implements iosanitization.StreamDataHandlerSpec{} &&
	acc(&dc.hs.startReceivingChan, _) &&
	acc(dc.hs.startReceivingChan.RecvChannel(), _) &&
	dc.hs.startReceivingChan.RecvGivenPerm() == PredTrue!<!> &&
	dc.hs.startReceivingChan.RecvGotPerm() == StartReceivingChanInv!<dc, _!> &&
	acc(&dc.hs.responseChan, _) &&
	acc(dc.hs.responseChan.SendChannel(), _) &&
	dc.hs.responseChan.SendGivenPerm() == ResponseChanInv!<dc, _!> &&
	dc.hs.responseChan.SendGotPerm() == PredTrue!<!>
}

pred StartReceivingChanInv(dc *dataChannel, payload MessageReceptionPayload) {
	(payload.status == ReceiveHandshakeResponeEncryptionEnabled ||
		payload.status == ReceiveHandshakeResponeEncryptionDisabled ||
		payload.status == ReceiveOtherResponse) &&
	(payload.status == ReceiveHandshakeResponeEncryptionEnabled ==> dc.MemTransfer(HandshakeRequestSent, true)) &&
	(payload.status == ReceiveHandshakeResponeEncryptionDisabled ==> dc.MemTransfer(HandshakeRequestSent, false) && !assumeEncryptionEnabledForVerification()) &&
	(payload.status == ReceiveOtherResponse ==>
		dc.MemRecv() &&
		// TODO move the following conditions within MemRecv:
		unfolding dc.MemRecv() in dc.dataChannelState == IODistributed && dc.hs.complete)
}

pred ResponseChanInv(dc *dataChannel, payload ResponseChanPayload) {
	dc.MemTransfer(payload.state, payload.encryptionEnabled) &&
	unfolding dc.MemTransfer(payload.state, payload.encryptionEnabled) in
		(dc.hs.error == nil && payload.encryptionEnabled ==> payload.state == BlockCipherReady) &&
		(dc.hs.error != nil ==> payload.state == Erroneous)
}

pred IoLockInv(dc *dataChannel, instanceId, clientId, agentLTKeyARN string) {
	acc(&dc.io, 1/4) &&
	acc(dc.io.IoSpecMemPartial(), 1/4) &&
	acc(&dc.ioLockDidLocalReceive, 1/2) &&
	acc(&dc.ioLockCanRemoteSend, 1/2) &&
	acc(&dc.ioLockDidRemoteReceive, 1/2) &&
	acc(&dc.ioLockCanLocalSend, 1/2) &&
	acc(&dc.io.localInFactT, 1/2) &&
	acc(&dc.io.remoteInFactT, 1/2) &&
	acc(&dc.io.localOutFactT, 1/2) &&
	acc(&dc.io.remoteOutFactT, 1/2) &&
	dc.io.IoSpecMemMain() &&
	pl.token(dc.io.getToken()) &&
	iospec.P_Agent(dc.io.getToken(), dc.io.getRid(), dc.io.getAbsState()) &&
	tm.pubTerm(pub.pub_msg(instanceId)) == dc.io.getAgentIdT() &&
	tm.pubTerm(pub.pub_msg(clientId)) == dc.io.getClientIdT() &&
	ft.St_Agent_10(dc.io.getRid(), dc.io.getAgentIdT(), dc.io.getKMSIdT(), dc.io.getClientIdT(), dc.io.getReaderIdT(), tm.pubTerm(pub.pub_msg(agentLTKeyARN)), dc.io.getLogLTPkT(), dc.io.getAgentShareT(), dc.io.getAgentShareSignatureT(), dc.io.getClientLtKeyIdT(), tm.exp(tm.pubTerm(pub.const_g_pub()), dc.io.getClientShareT()), dc.io.getClientShareSignatureT(), dc.io.getSigSessionKeysT()) in dc.io.getAbsState() &&
	dc.io.getSharedSecretT() == tm.exp(tm.exp(tm.pubTerm(pub.const_g_pub()), dc.io.getClientShareT()), dc.io.getAgentShareT()) &&
	(((dc.ioLockDidLocalReceive ? mset[ft.Fact]{ ft.InFact_Agent(dc.io.getRid(), dc.io.localInFactT) } : mset[ft.Fact]{ }) union
		(dc.ioLockCanRemoteSend ? mset[ft.Fact]{ ft.OutFact_Agent(dc.io.getRid(), dc.io.remoteOutFactT) } : mset[ft.Fact]{ } ) union
		(dc.ioLockDidRemoteReceive ? mset[ft.Fact]{ ft.InFact_Agent(dc.io.getRid(), dc.io.remoteInFactT) } : mset[ft.Fact]{ } ) union
		(dc.ioLockCanLocalSend ? mset[ft.Fact]{ ft.OutFact_Agent(dc.io.getRid(), dc.io.localOutFactT) } : mset[ft.Fact]{ } )) subset dc.io.getAbsState())
}

pred (io gpointer[ioSpecFields]) IoSpecMemMain() {
	acc(&io.token) &&
	acc(&io.absState)
}

pred (io gpointer[ioSpecFields]) IoSpecMemPartial() {
	acc(&io.rid) &&
	acc(&io.agentIdT) &&
	acc(&io.kMSIdT) &&
	acc(&io.clientIdT) &&
	acc(&io.readerIdT) &&
	acc(&io.logLTPkT) &&
	acc(&io.agentShareT) &&
	acc(&io.agentShareSignatureT) &&
	acc(&io.inFactT) &&
	acc(&io.sharedSecretT) &&
	acc(&io.clientLtKeyIdT) &&
	acc(&io.clientShareT) &&
	acc(&io.clientShareSignatureT) &&
	acc(&io.sigSessionKeysT)
}

ghost
decreases
requires acc(io.IoSpecMemMain(), _)
pure func (io gpointer[ioSpecFields]) getToken() pl.Place {
	return unfolding acc(io.IoSpecMemMain(), _) in io.token
}

ghost
decreases
requires acc(io.IoSpecMemPartial(), _)
pure func (io gpointer[ioSpecFields]) getRid() tm.Term {
	return unfolding acc(io.IoSpecMemPartial(), _) in io.rid
}

ghost
decreases
requires acc(dc.Mem(), _) && dc.getState() >= Initialized && dc.getState() < IODistributed
pure func (dc *dataChannel) GetRid() tm.Term {
	return unfolding acc(dc.Mem(), _) in unfolding acc(dc.MemInternal(dc.dataChannelState), _) in dc.io.getRid()
}

ghost
decreases
requires acc(io.IoSpecMemMain(), _)
pure func (io gpointer[ioSpecFields]) getAbsState() mset[ft.Fact] {
	return unfolding acc(io.IoSpecMemMain(), _) in io.absState
}

ghost
decreases
requires acc(dc.Mem(), _) && dc.getState() >= Initialized && dc.getState() < IODistributed
pure func (dc *dataChannel) GetAbsState() mset[ft.Fact] {
	return unfolding acc(dc.Mem(), _) in unfolding acc(dc.MemInternal(dc.dataChannelState), _) in dc.io.getAbsState()
}

ghost
decreases
requires acc(io.IoSpecMemPartial(), _)
pure func (io gpointer[ioSpecFields]) getAgentIdT() tm.Term {
	return unfolding acc(io.IoSpecMemPartial(), _) in io.agentIdT
}

ghost
decreases
requires acc(io.IoSpecMemPartial(), _)
pure func (io gpointer[ioSpecFields]) getKMSIdT() tm.Term {
	return unfolding acc(io.IoSpecMemPartial(), _) in io.kMSIdT
}

ghost
decreases
requires acc(io.IoSpecMemPartial(), _)
pure func (io gpointer[ioSpecFields]) getClientIdT() tm.Term {
	return unfolding acc(io.IoSpecMemPartial(), _) in io.clientIdT
}

ghost
decreases
requires acc(io.IoSpecMemPartial(), _)
pure func (io gpointer[ioSpecFields]) getReaderIdT() tm.Term {
	return unfolding acc(io.IoSpecMemPartial(), _) in io.readerIdT
}

ghost
decreases
requires acc(io.IoSpecMemPartial(), _)
pure func (io gpointer[ioSpecFields]) getLogLTPkT() tm.Term {
	return unfolding acc(io.IoSpecMemPartial(), _) in io.logLTPkT
}

ghost
decreases
requires acc(io.IoSpecMemPartial(), _)
pure func (io gpointer[ioSpecFields]) getAgentShareT() tm.Term {
	return unfolding acc(io.IoSpecMemPartial(), _) in io.agentShareT
}

ghost
decreases
requires acc(dc.Mem(), _) && dc.getState() >= Initialized
pure func (dc *dataChannel) GetAgentShareT() tm.Term {
	return unfolding acc(dc.Mem(), _) in unfolding acc(dc.MemInternal(dc.dataChannelState), _) in dc.io.getAgentShareT()
}

ghost
decreases
requires acc(io.IoSpecMemPartial(), _)
pure func (io gpointer[ioSpecFields]) getAgentShareSignatureT() tm.Term {
	return unfolding acc(io.IoSpecMemPartial(), _) in io.agentShareSignatureT
}

ghost
decreases _
requires acc(dc.Mem(), _) && dc.getState() >= Initialized
pure func (dc *dataChannel) GetAgentShareSignatureT() tm.Term {
	return unfolding acc(dc.Mem(), _) in unfolding acc(dc.MemInternal(dc.dataChannelState), _) in dc.io.getAgentShareSignatureT()
}

ghost
decreases
requires acc(io.IoSpecMemPartial(), _)
pure func (io gpointer[ioSpecFields]) getInFactT() tm.Term {
	return unfolding acc(io.IoSpecMemPartial(), _) in io.inFactT
}

ghost
decreases
requires acc(dc.Mem(), _) && dc.getState() >= Initialized
pure func (dc *dataChannel) GetInFactT() tm.Term {
	return unfolding acc(dc.Mem(), _) in unfolding acc(dc.MemInternal(dc.dataChannelState), _) in dc.io.getInFactT()
}

ghost
decreases
requires acc(io.IoSpecMemPartial(), _)
pure func (io gpointer[ioSpecFields]) getSharedSecretT() tm.Term {
	return unfolding acc(io.IoSpecMemPartial(), _) in io.sharedSecretT
}

ghost
decreases
requires acc(io.IoSpecMemPartial(), _)
pure func (io gpointer[ioSpecFields]) getClientLtKeyIdT() tm.Term {
	return unfolding acc(io.IoSpecMemPartial(), _) in io.clientLtKeyIdT
}

ghost
decreases
requires acc(io.IoSpecMemPartial(), _)
pure func (io gpointer[ioSpecFields]) getClientShareT() tm.Term {
	return unfolding acc(io.IoSpecMemPartial(), _) in io.clientShareT
}

ghost
decreases
requires acc(io.IoSpecMemPartial(), _)
pure func (io gpointer[ioSpecFields]) getClientShareSignatureT() tm.Term {
	return unfolding acc(io.IoSpecMemPartial(), _) in io.clientShareSignatureT
}

ghost
decreases
requires acc(io.IoSpecMemPartial(), _)
pure func (io gpointer[ioSpecFields]) getSigSessionKeysT() tm.Term {
	return unfolding acc(io.IoSpecMemPartial(), _) in io.sigSessionKeysT
}

ghost
decreases
requires acc(dc.Mem(), _) && dc.getState() >= BlockCipherInitialized
pure func (dc *dataChannel) GetEncKeyT() tm.Term {
	return unfolding acc(dc.Mem(), _) in unfolding acc(dc.MemInternal(dc.dataChannelState), _) in dc.blockCipher.GetEncKeyT()
}

ghost
decreases
requires acc(dc.Mem(), _) && dc.getState() != Erroneous && dc.getState() <= IODistributed
pure func (dc *dataChannel) GetIoLockCanRemoteSend() bool {
	return unfolding acc(dc.Mem(), _) in unfolding acc(dc.MemInternal(dc.dataChannelState), _) in dc.ioLockCanRemoteSend
}

ghost
decreases
requires acc(dc.Mem(), _) && dc.getState() != Erroneous && dc.getState() <= IODistributed
pure func (dc *dataChannel) GetRemoteOutFactT() tm.Term {
	return unfolding acc(dc.Mem(), _) in unfolding acc(dc.MemInternal(dc.dataChannelState), _) in dc.io.remoteOutFactT
}

// while assuming that verification is enabled is not necessary to prove
// memory safety, we need this assumption for verifying refinement.
// Leaving this function abstract will consider both cases, i.e.,
// encryption being disabled or enabled.
ghost
decreases
pure func assumeEncryptionEnabledForVerification() bool {
	return true
}
@*/
