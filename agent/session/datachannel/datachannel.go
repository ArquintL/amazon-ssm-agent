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

// work arounds to make verification possible
// - magic wands for receiving messages via callbacks instead of by calling a particular receive method
// - ghost fields to simplify keeping track of abstract terms
// - ghost lock to enable concurrently sending and receiving messages by assuming atomicity of these operations

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
	"github.com/aws/aws-sdk-go/service/kms"
	"golang.org/x/crypto/hkdf"
	//@ "sync"
	//@ abs "github.com/aws/amazon-ssm-agent/agent/iospecs/abs"
	//@ arb "github.com/aws/amazon-ssm-agent/agent/iospecs/arb"
	//@ by "github.com/aws/amazon-ssm-agent/agent/iospecs/bytes"
	//@ cl "github.com/aws/amazon-ssm-agent/agent/iospecs/claim"
	//@ ft "github.com/aws/amazon-ssm-agent/agent/iospecs/fact"
	//@ "github.com/aws/amazon-ssm-agent/agent/iospecs/iospec"
	//@ "github.com/aws/amazon-ssm-agent/agent/iospecs/pattern"
	//@ pl "github.com/aws/amazon-ssm-agent/agent/iospecs/place"
	//@ pub "github.com/aws/amazon-ssm-agent/agent/iospecs/pub"
	//@ tm "github.com/aws/amazon-ssm-agent/agent/iospecs/term"
	//@ ut "github.com/aws/amazon-ssm-agent/agent/iospecs/util"
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

/*@
// since Gobra is struggling with generating a refinement proof of the interface
// if quantified permissions appear in specification, we wrap these permissions in
// the following two predicates:
pred SendStreamDataMessageWand(t pl.Place, rid tm.Term, inputData []byte, inputDataT tm.Term, p perm) {
	noPerm < p && p <= writePerm &&
	(pl.token(t) && iospec.e_InFact(t, rid)) --* (acc(bytes.SliceMem(inputData), p) && by.gamma(inputDataT) == abs.Abs(inputData) && inputDataT == old[#lhs](iospec.get_e_InFact_r1(t, rid)) && pl.token(old[#lhs](iospec.get_e_InFact_placeDst(t, rid))))
}

pred QuantifiedSendStreamDataMessageWand(inputData []byte, inputDataT tm.Term, p perm) {
	forall t pl.Place, rid tm.Term :: { SendStreamDataMessageWand(t, rid, inputData, inputDataT, p) } SendStreamDataMessageWand(t, rid, inputData, inputDataT, p)
}
@*/

type IDataChannel interface {

	//@ pred Mem()

	// @ requires log != nil
	// @ requires QuantifiedSendStreamDataMessageWand(inputData, inputDataT, p)
	// @ preserves Mem()
	// @ preserves acc(log.Mem(), _)
	SendStreamDataMessage(log logger.T, dataType mgsContracts.PayloadType, inputData []byte /*@, ghost p perm, ghost inputDataT tm.Term @*/) error

	// @ requires log != nil
	// @ preserves Mem() && acc(log.Mem(), _)
	SendAgentSessionStateMessage(log logger.T, sessionStatus mgsContracts.SessionStatus) error

	// @ requires log != nil
	// @ preserves Mem() && acc(log.Mem(), _)
	SkipHandshake(log logger.T) error

	// @ requires log != nil
	// @ requires encryptionEnabled == assumeEncryptionEnabledForVerification()
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
	IODistributed				DataChannelState = 11
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

	// TODO: mark the following fields as ghost as soon as Gobra supports ghost fields
	//@ msgHandlerCtx StreamDataHandlerContext
	//@ ioLock *sync.Mutex
	//@ ioLockDidLocalReceive bool
	//@ ioLockCanRemoteSend bool
	//@ ioLockDidRemoteReceive bool
	//@ ioLockCanLocalSend bool
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

type InputStreamMessageHandler = func(log logger.T, streamDataMessage *mgsContracts.AgentMessage /*@, ghost t pl.Place, ghost rid tm.Term, ghost agentMessageT tm.Term @*/) error

type MessageReceptionStatus int
type MessageReceptionPayload struct {
	status MessageReceptionStatus
	data   interface{}
}

type ResponseChanPayload struct {
	encryptionEnabled bool
	state DataChannelState
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

// @ requires acc(dc.Mem(), _)
// @ pure
func (dc *dataChannel) getState() DataChannelState {
	return /*@ unfolding acc(dc.Mem(), _) in @*/ dc.dataChannelState
}

/*@
type StreamDataHandlerContext interface {
	pred Inv()
}

ghost
requires ctx != nil && log != nil
requires agentMessage.Mem()
requires pl.token(t) && iospec.e_OutFact(t, rid, agentMessageT) && by.gamma(agentMessageT) == agentMessage.Abs()
preserves ctx.Inv() && acc(log.Mem(), _)
ensures err == nil ==> agentMessage.Mem()
ensures err != nil ==> err.ErrorMem()
ensures err == nil ==> pl.token(old(iospec.get_e_OutFact_placeDst(t, rid, agentMessageT))) 
ensures err != nil ==> pl.token(t) && iospec.e_OutFact(t, rid, agentMessageT) && iospec.get_e_OutFact_placeDst(t, rid, agentMessageT) == old(iospec.get_e_OutFact_placeDst(t, rid, agentMessageT))
func StreamDataHandlerSpec(ghost ctx StreamDataHandlerContext, log logger.T, agentMessage *mgsContracts.AgentMessage, ghost t pl.Place, ghost rid tm.Term, ghost agentMessageT tm.Term) (err error)

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

pred (dc *dataChannel) MemFields(state DataChannelState) {
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
	acc(&dc.logLTPk) &&
	acc(&dc.hs.startReceivingChan, _) &&
	acc(&dc.hs.responseChan, _) &&
	acc(&dc.ioLock) &&
	(state >= Initialized ==>
		dc.dataStream.Mem() &&
		dc.state.kmsService.Mem() &&
		dc.logLTPk.Mem())
}

pred (dc *dataChannel) MemOld() {
	dc != nil &&
	acc(&dc.dataChannelState, 1/2) &&
	acc(dc.MemInternal(dc.dataChannelState), 1/2) &&
	(dc.dataChannelState != IODistributed ==>
		acc(&dc.dataChannelState, 1/2) &&
		acc(dc.MemInternal(dc.dataChannelState), 1/2))
}

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
		acc(&dc.ioLock)) &&
	(state != Erroneous && state < IODistributed ==>
		acc(&dc.ioLockDidLocalReceive) && acc(&dc.ioLockCanRemoteSend) &&
		acc(&dc.ioLockDidRemoteReceive) && acc(&dc.ioLockCanLocalSend) &&
		dc.LocalInFactTMem() && dc.RemoteInFactTMem() &&
		dc.LocalOutFactTMem() && dc.RemoteOutFactTMem()) &&
	(state >= Initialized ==>
		dc.IoSpecMemPartial() &&
		dc.dataStream.Mem() &&
		dc.state.kmsService.Mem() &&
		dc.logLTPk.Mem()) &&
	(state >= Initialized && state < IODistributed ==>
		dc.IoSpecMemMain() &&
		pl.token(dc.getToken()) &&
		iospec.P_Agent(dc.getToken(), dc.getRid(), dc.getAbsState()) &&
		tm.pubTerm(pub.pub_msg(dc.dataStream.GetInstanceId())) == dc.getAgentIdT() &&
		tm.pubTerm(pub.pub_msg(dc.dataStream.GetClientId())) == dc.getClientIdT() &&
		tm.pubTerm(pub.pub_msg(dc.logReaderId)) == dc.getReaderIdT() &&
		by.gamma(dc.getLogLTPkT()) == dc.logLTPk.Abs()) &&
	(state == Initialized ==>
		!dc.hs.skipped) &&
	(state == HandshakeSkipped ==>
		dc.hs.skipped) &&
	(state >= BlockCipherInitialized ==>
		!dc.hs.skipped &&
		dc.encryptionEnabled == assumeEncryptionEnabledForVerification() &&
		dc.blockCipher != nil && dc.blockCipher.Mem()) &&
	(state >= AgentSecretCreatedAndSigned && state < HandshakeCompleted ==>
		bytes.SliceMem(dc.state.agentSecret) &&
		by.gamma(dc.getAgentShareT()) == abs.Abs(dc.state.agentSecret)) &&
	(state >= BlockCipherReady && dc.encryptionEnabled ==>
		dc.blockCipher.IsReady() &&
		dc.getSharedSecretT() == tm.exp(tm.exp(tm.pubTerm(pub.const_g_pub()), dc.getClientShareT()), dc.getAgentShareT()) &&
		dc.blockCipher.GetEncKeyT() == tm.kdf1(dc.getSharedSecretT()) &&
		dc.blockCipher.GetDecKeyT() == tm.kdf2(dc.getSharedSecretT())) &&
	// relate state to abstract state:
	(state == Initialized || state == BlockCipherInitialized ==>
		ft.Setup_Agent(dc.getRid(), dc.getAgentIdT(), dc.getKMSIdT(), dc.getClientIdT(), dc.getReaderIdT(), tm.pubTerm(pub.pub_msg(dc.agentLTKeyARN)), dc.getLogLTPkT()) in dc.getAbsState()) &&
	(state == AgentSecretCreatedAndSigned ==>
		ft.St_Agent_2(dc.getRid(), dc.getAgentIdT(), dc.getKMSIdT(), dc.getClientIdT(), dc.getReaderIdT(), tm.pubTerm(pub.pub_msg(dc.agentLTKeyARN)), dc.getLogLTPkT(), dc.getAgentShareT(), dc.getAgentShareSignatureT()) in dc.getAbsState()) &&
	(state == HandshakeRequestSent ==>
		ft.St_Agent_3(dc.getRid(), dc.getAgentIdT(), dc.getKMSIdT(), dc.getClientIdT(), dc.getReaderIdT(), tm.pubTerm(pub.pub_msg(dc.agentLTKeyARN)), dc.getLogLTPkT(), dc.getAgentShareT(), dc.getAgentShareSignatureT()) in dc.getAbsState()) &&
	(state == BlockCipherReady ==>
		ft.St_Agent_9(dc.getRid(), dc.getAgentIdT(), dc.getKMSIdT(), dc.getClientIdT(), dc.getReaderIdT(), tm.pubTerm(pub.pub_msg(dc.agentLTKeyARN)), dc.getLogLTPkT(), dc.getAgentShareT(), dc.getAgentShareSignatureT(), dc.getClientLtKeyIdT(), tm.exp(tm.pubTerm(pub.const_g_pub()), dc.getClientShareT()), dc.getClientShareSignatureT(), dc.getSigSessionKeysT()) in dc.getAbsState()) &&
	(state == HandshakeCompleted ==>
		ft.St_Agent_10(dc.getRid(), dc.getAgentIdT(), dc.getKMSIdT(), dc.getClientIdT(), dc.getReaderIdT(), tm.pubTerm(pub.pub_msg(dc.agentLTKeyARN)), dc.getLogLTPkT(), dc.getAgentShareT(), dc.getAgentShareSignatureT(), dc.getClientLtKeyIdT(), tm.exp(tm.pubTerm(pub.const_g_pub()), dc.getClientShareT()), dc.getClientShareSignatureT(), dc.getSigSessionKeysT()) in dc.getAbsState()) &&
	(state == IODistributed ==>
		// the idea is that the receiving thread does not get permission to Mem() but a reduced invariant:
		// acc(dc.LocalInFactTMem(), 1/2) && acc(dc.RemoteOutFactTMem(), 1/2) &&
		// acc(dc.IoSpecMemPartial(), 1/2) &&
		acc(&dc.ioLockDidLocalReceive) && acc(&dc.ioLockCanRemoteSend) &&
		dc.LocalInFactTMem() && dc.RemoteOutFactTMem() &&
		acc(dc.ioLock.LockP()) && dc.ioLock.LockInv() == IoLockInv!<dc, dc.dataStream.GetInstanceId(), dc.dataStream.GetClientId(), dc.agentLTKeyARN!>)
}

// permissions in `RecvRoutineMem` are already subtracted:
// pred (dc *dataChannel) Mem2() {
// 	dc != nil &&
// 	acc(&dc.dataChannelState, 1/2) &&
// 	(dc.dataChannelState != IODistributed ==>
// 		acc(&dc.dataChannelState, 1/2)) &&
// 	(dc.dataChannelState != Erroneous ==>
// 		acc(dc.MemFields(dc.dataChannelState), 1/2)) &&
// 	(dc.dataChannelState != Erroneous && dc.dataChannelState < IODistributed ==>
// 		acc(dc.MemFields(dc.dataChannelState), 1/2)) &&
// 	// (let p := (dc.dataChannelState != Erroneous && dc.dataChannelState < IODistributed) ? writePerm : (dc.dataChannelState != Erroneous ? 1/2 : noPerm) in
// 	//	acc(dc.MemFields(dc.dataChannelState), p)) &&
// 	(dc.dataChannelState >= Initialized && dc.dataChannelState < IODistributed ==>
// 		dc.IoSpecMem() &&
// 		pl.token(dc.getToken()) &&
// 		iospec.P_Agent(dc.getToken(), dc.getRid(), dc.getAbsState()) &&
// 		//tm.pubTerm(pub.pub_msg(dc.dataStream.GetInstanceId())) == dc.getAgentIdT() &&
// 		//tm.pubTerm(pub.pub_msg(dc.dataStream.GetClientId())) == dc.getClientIdT() &&
// 		//tm.pubTerm(pub.pub_msg(dc.logReaderId)) == dc.getReaderIdT() &&
// 		true/*by.gamma(dc.getLogLTPkT()) == dc.logLTPk.Abs()*/) &&
// 	acc(dc.hs.startReceivingChan.SendChannel(), _) &&
// 	dc.hs.startReceivingChan.SendGivenPerm() == StartReceivingChanInv!<dc, _!> &&
// 	dc.hs.startReceivingChan.SendGotPerm() == PredTrue!<!> &&
// 	acc(dc.hs.responseChan.RecvChannel(), _) &&
// 	dc.hs.responseChan.RecvGivenPerm() == PredTrue!<!> &&
// 	dc.hs.responseChan.RecvGotPerm() == ResponseChanInv!<dc, _!> &&
// 	(dc.dataChannelState == Initialized ==>
// 		!dc.hs.skipped) &&
// 	(dc.dataChannelState == HandshakeSkipped ==>
// 		dc.hs.skipped) &&
// 	(dc.dataChannelState >= BlockCipherInitialized ==>
// 		!dc.hs.skipped &&
// 		dc.encryptionEnabled == assumeEncryptionEnabledForVerification() &&
// 		dc.blockCipher != nil && dc.blockCipher.Mem()) &&
// 	(dc.dataChannelState >= AgentSecretCreatedAndSigned && dc.dataChannelState < HandshakeCompleted ==>
// 		bytes.SliceMem(dc.state.agentSecret) &&
// 		by.gamma(dc.getAgentShareT()) == abs.Abs(dc.state.agentSecret)) &&
// 	(dc.dataChannelState >= BlockCipherReady && dc.encryptionEnabled ==>
// 		dc.blockCipher.IsReady()) &&
// 	(dc.dataChannelState >= BlockCipherReady && dc.dataChannelState < IODistributed && dc.encryptionEnabled ==>
// 		dc.getSharedSecretT() == tm.exp(tm.exp(tm.pubTerm(pub.const_g_pub()), dc.getClientShareT()), dc.getAgentShareT()) &&
// 		dc.blockCipher.GetEncKeyT() == tm.kdf1(dc.getSharedSecretT())) &&
// 	// relate state to abstract state:
// 	(dc.dataChannelState == Initialized || dc.dataChannelState == BlockCipherInitialized ==>
// 		ft.Setup_Agent(dc.getRid(), dc.getAgentIdT(), dc.getKMSIdT(), dc.getClientIdT(), dc.getReaderIdT(), tm.pubTerm(pub.pub_msg(dc.agentLTKeyARN)), dc.getLogLTPkT()) in dc.getAbsState()) &&
// 	(dc.dataChannelState == AgentSecretCreatedAndSigned ==>
// 		ft.St_Agent_2(dc.getRid(), dc.getAgentIdT(), dc.getKMSIdT(), dc.getClientIdT(), dc.getReaderIdT(), tm.pubTerm(pub.pub_msg(dc.agentLTKeyARN)), dc.getLogLTPkT(), dc.getAgentShareT(), dc.getAgentShareSignatureT()) in dc.getAbsState()) &&
// 	(dc.dataChannelState == HandshakeRequestSent ==>
// 		ft.St_Agent_3(dc.getRid(), dc.getAgentIdT(), dc.getKMSIdT(), dc.getClientIdT(), dc.getReaderIdT(), tm.pubTerm(pub.pub_msg(dc.agentLTKeyARN)), dc.getLogLTPkT(), dc.getAgentShareT(), dc.getAgentShareSignatureT()) in dc.getAbsState()) &&
// 	(dc.dataChannelState == BlockCipherReady ==>
// 		ft.St_Agent_9(dc.getRid(), dc.getAgentIdT(), dc.getKMSIdT(), dc.getClientIdT(), dc.getReaderIdT(), tm.pubTerm(pub.pub_msg(dc.agentLTKeyARN)), dc.getLogLTPkT(), dc.getAgentShareT(), dc.getAgentShareSignatureT(), dc.getClientLtKeyIdT(), tm.exp(tm.pubTerm(pub.const_g_pub()), dc.getClientShareT()), dc.getClientShareSignatureT(), dc.getSigSessionKeysT()) in dc.getAbsState()) &&
// 	(dc.dataChannelState == HandshakeCompleted ==>
// 		ft.St_Agent_10(dc.getRid(), dc.getAgentIdT(), dc.getKMSIdT(), dc.getClientIdT(), dc.getReaderIdT(), tm.pubTerm(pub.pub_msg(dc.agentLTKeyARN)), dc.getLogLTPkT(), dc.getAgentShareT(), dc.getAgentShareSignatureT(), dc.getClientLtKeyIdT(), tm.exp(tm.pubTerm(pub.const_g_pub()), dc.getClientShareT()), dc.getClientShareSignatureT(), dc.getSigSessionKeysT()) in dc.getAbsState()) &&
// 	(dc.dataChannelState == IODistributed ==>
// 		// the idea is that the receiving thread does not get permission to Mem() but a reduced invariant:
// 		// acc(dc.LocalInFactTMem(), 1/2) && acc(dc.RemoteOutFactTMem(), 1/2) &&
// 		acc(dc.IoSpecMemPartial(), 1/4) &&
// 		acc(&dc.ioLockDidLocalReceive, 1/2) && acc(&dc.ioLockCanRemoteSend, 1/2) )// &&
// 		//acc(dc.ioLock.LockP(), 1/2) && dc.ioLock.LockInv() == IoLockInv!<dc, dc.dataStream.GetInstanceId(), dc.dataStream.GetClientId(), dc.agentLTKeyARN!>)
// }

// `MemRecv` is the predicate on which the goroutine receiving transport messages operates on.
// TODO move below `MemTransfer`
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
	// acc(dc.hs.responseChan.RecvChannel(), _) &&
	// dc.hs.responseChan.RecvGivenPerm() == PredTrue!<!> &&
	// dc.hs.responseChan.RecvGotPerm() == ResponseChanInv!<dc, _!> &&
	acc(&dc.dataStream, 1/2) &&
	acc(&dc.hs.clientVersion, 1/2) &&
	acc(&dc.hs.error, 1/2) &&
	acc(&dc.hs.complete, 1/2) &&
	acc(&dc.hs.skipped, 1/2) &&
	acc(&dc.hs.handshakeStartTime, 1/2) &&
	acc(&dc.hs.handshakeEndTime, 1/2) &&
	acc(&dc.encryptionEnabled, 1/2) &&
	acc(&dc.blockCipher, 1/2) &&
	acc(dc.blockCipher.Mem(), 1/2) &&
	(dc.encryptionEnabled ==> dc.blockCipher.IsReady()) &&
	acc(&dc.separateOutputPayload, 1/2) &&
	acc(&dc.state, 1/2) &&
	acc(&dc.agentLTKeyARN, 1/2) &&
	acc(&dc.logReaderId, 1/2) &&
	acc(&dc.logLTPk, 1/2) &&
	acc(dc.dataStream.Mem(), 1/2) &&
	acc(dc.state.kmsService.Mem(), 1/2) &&
	acc(dc.logLTPk.Mem(), 1/2) &&
	acc(dc.IoSpecMemPartial(), 1/4) &&
	dc.getSharedSecretT() == tm.exp(tm.exp(tm.pubTerm(pub.const_g_pub()), dc.getClientShareT()), dc.getAgentShareT()) &&
	dc.blockCipher.GetEncKeyT() == tm.kdf1(dc.getSharedSecretT()) &&
	dc.blockCipher.GetDecKeyT() == tm.kdf2(dc.getSharedSecretT()) &&
	acc(&dc.ioLockCanLocalSend, 1/2) && acc(&dc.ioLockDidRemoteReceive, 1/2) &&
	acc(dc.LocalOutFactTMem(), 1/2) && acc(dc.RemoteInFactTMem(), 1/2) &&
	acc(dc.ioLock.LockP(), 1/2) && dc.ioLock.LockInv() == IoLockInv!<dc, dc.dataStream.GetInstanceId(), dc.dataStream.GetClientId(), dc.agentLTKeyARN!>
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
	dc.encryptionEnabled == assumeEncryptionEnabledForVerification() &&
	dc.blockCipher != nil && dc.blockCipher.Mem() &&
	// dc.IoSpecMem() &&
	dc.IoSpecMemMain() &&
	dc.IoSpecMemPartial() &&
	(state != Erroneous ==>
		pl.token(dc.getToken()) &&
		iospec.P_Agent(dc.getToken(), dc.getRid(), dc.getAbsState())) &&
	tm.pubTerm(pub.pub_msg(dc.dataStream.GetInstanceId())) == dc.getAgentIdT() &&
	tm.pubTerm(pub.pub_msg(dc.dataStream.GetClientId())) == dc.getClientIdT() &&
	tm.pubTerm(pub.pub_msg(dc.logReaderId)) == dc.getReaderIdT() &&
	by.gamma(dc.getLogLTPkT()) == dc.logLTPk.Abs() &&
	(encryptionEnabled ==>
		dc.logLTPk.Mem() &&
		dc.state.kmsService.Mem() &&
		bytes.SliceMem(dc.state.agentSecret) &&
		by.gamma(dc.getAgentShareT()) == abs.Abs(dc.state.agentSecret)) &&
	(state == HandshakeRequestSent ==>
		ft.St_Agent_3(dc.getRid(), dc.getAgentIdT(), dc.getKMSIdT(), dc.getClientIdT(), dc.getReaderIdT(), tm.pubTerm(pub.pub_msg(dc.agentLTKeyARN)), dc.getLogLTPkT(), dc.getAgentShareT(), dc.getAgentShareSignatureT()) in dc.getAbsState()) &&
	(state >= HandshakeResponseReceived ==>
		bytes.SliceMem(dc.state.sharedSecret) &&
		// TODO: we could technically remove `getSharedSecretT` as it only acts as an abbreviation:
		dc.getSharedSecretT() == tm.exp(tm.exp(tm.pubTerm(pub.const_g_pub()), dc.getClientShareT()), dc.getAgentShareT()) &&
		by.gamma(dc.getSharedSecretT()) == abs.Abs(dc.state.sharedSecret)) &&
	(state == HandshakeResponseVerified ==>
		ft.St_Agent_6(dc.getRid(), dc.getAgentIdT(), dc.getKMSIdT(), dc.getClientIdT(), dc.getReaderIdT(), tm.pubTerm(pub.pub_msg(dc.agentLTKeyARN)), dc.getLogLTPkT(), dc.getAgentShareT(), dc.getAgentShareSignatureT(), dc.getClientLtKeyIdT(), tm.exp(tm.pubTerm(pub.const_g_pub()), dc.getClientShareT()), dc.getClientShareSignatureT()) in dc.getAbsState()) &&
	(state == BlockCipherReady ==>
		(encryptionEnabled ==>
			dc.blockCipher.IsReady() &&
			dc.blockCipher.GetEncKeyT() == tm.kdf1(dc.getSharedSecretT()) &&
			dc.blockCipher.GetDecKeyT() == tm.kdf2(dc.getSharedSecretT())) &&
		ft.St_Agent_9(dc.getRid(), dc.getAgentIdT(), dc.getKMSIdT(), dc.getClientIdT(), dc.getReaderIdT(), tm.pubTerm(pub.pub_msg(dc.agentLTKeyARN)), dc.getLogLTPkT(), dc.getAgentShareT(), dc.getAgentShareSignatureT(), dc.getClientLtKeyIdT(), tm.exp(tm.pubTerm(pub.const_g_pub()), dc.getClientShareT()), dc.getClientShareSignatureT(), dc.getSigSessionKeysT()) in dc.getAbsState())
}

pred (dc *dataChannel) Inv() {
	dc.RecvRoutineMem()
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
	// dc.IoSpecMem() &&
	acc(dc.IoSpecMemPartial(), 1/4) &&
	acc(&dc.ioLockDidLocalReceive, 1/2) &&
	acc(&dc.ioLockCanRemoteSend, 1/2) &&
	acc(&dc.ioLockDidRemoteReceive, 1/2) &&
	acc(&dc.ioLockCanLocalSend, 1/2) &&
	acc(dc.LocalInFactTMem(), 1/2) &&
	acc(dc.RemoteInFactTMem(), 1/2) &&
	acc(dc.LocalOutFactTMem(), 1/2) &&
	acc(dc.RemoteOutFactTMem(), 1/2) &&
	// dc.TokenMem() &&
	// dc.AbsStateMem() &&
	// pl.token(dc.getTokenInternal()) &&
	// iospec.P_Agent(dc.getTokenInternal(), dc.getRidPartial(), dc.getAbsStateInternal()) &&
	// unfolding acc(dc.IoSpecMemPartial(), 1/2) in
	// 	tm.pubTerm(pub.pub_msg(instanceId)) == dc.getAgentIdTInternal() &&
	// 	tm.pubTerm(pub.pub_msg(clientId)) == dc.getClientIdTInternal() &&
	// 	ft.St_Agent_10(dc.getRidInternal(), dc.getAgentIdTInternal(), dc.getKMSIdTInternal(), dc.getClientIdTInternal(), dc.getReaderIdTInternal(), tm.pubTerm(pub.pub_msg(agentLTKeyARN)), dc.getLogLTPkTInternal(), dc.getAgentShareTInternal(), dc.getAgentShareSignatureTInternal(), dc.getClientLtKeyIdTInternal(), tm.exp(tm.pubTerm(pub.const_g_pub()), dc.getClientShareTInternal()), dc.getClientShareSignatureTInternal(), dc.getSigSessionKeysTInternal()) in dc.getAbsStateInternal() &&
	// 	(dc.ioLockDidLocalReceive ==> ft.InFact_Agent(dc.getRidInternal(), dc.getLocalInFactTInternal()) in dc.getAbsStateInternal()) &&
	// 	(dc.ioLockCanRemoteSend ==> ft.OutFact_Agent(dc.getRidInternal(), dc.getRemoteOutFactTInternal()) in dc.getAbsStateInternal()) &&
	// 	(dc.ioLockDidRemoteReceive ==> ft.InFact_Agent(dc.getRidInternal(), dc.getRemoteInFactTInternal()) in dc.getAbsStateInternal()) &&
	// 	(dc.ioLockCanLocalSend ==> ft.OutFact_Agent(dc.getRidInternal(), dc.getLocalOutFactTInternal()) in dc.getAbsStateInternal())
	dc.IoSpecMemMain() &&
	pl.token(dc.getToken()) &&
	iospec.P_Agent(dc.getToken(), dc.getRid(), dc.getAbsState()) &&
	tm.pubTerm(pub.pub_msg(instanceId)) == dc.getAgentIdT() &&
	tm.pubTerm(pub.pub_msg(clientId)) == dc.getClientIdT() &&
	ft.St_Agent_10(dc.getRid(), dc.getAgentIdT(), dc.getKMSIdT(), dc.getClientIdT(), dc.getReaderIdT(), tm.pubTerm(pub.pub_msg(agentLTKeyARN)), dc.getLogLTPkT(), dc.getAgentShareT(), dc.getAgentShareSignatureT(), dc.getClientLtKeyIdT(), tm.exp(tm.pubTerm(pub.const_g_pub()), dc.getClientShareT()), dc.getClientShareSignatureT(), dc.getSigSessionKeysT()) in dc.getAbsState() &&
	dc.getSharedSecretT() == tm.exp(tm.exp(tm.pubTerm(pub.const_g_pub()), dc.getClientShareT()), dc.getAgentShareT()) &&
	(((dc.ioLockDidLocalReceive ? mset[ft.Fact]{ ft.InFact_Agent(dc.getRid(), dc.getLocalInFactTInternal()) } : mset[ft.Fact]{ }) union
		(dc.ioLockCanRemoteSend ? mset[ft.Fact]{ ft.OutFact_Agent(dc.getRid(), dc.getRemoteOutFactTInternal()) } : mset[ft.Fact]{ } ) union
		(dc.ioLockDidRemoteReceive ? mset[ft.Fact]{ ft.InFact_Agent(dc.getRid(), dc.getRemoteInFactTInternal()) } : mset[ft.Fact]{ } ) union
		(dc.ioLockCanLocalSend ? mset[ft.Fact]{ ft.OutFact_Agent(dc.getRid(), dc.getLocalOutFactTInternal()) } : mset[ft.Fact]{ } )) subset dc.getAbsState())
}

// conceptually, this predicate contains write permissions to
// ghost heap locations storing the parameters for the IO spec
pred (dc *dataChannel) IoSpecMem() {
	dc.TokenMem() &&
	dc.RidMem() &&
	dc.AbsStateMem() &&
	dc.AgentIdTMem() &&
	dc.KMSIdTMem() &&
	dc.ClientIdTMem() &&
	dc.ReaderIdTMem() &&
	dc.LogLTPkTMem() &&
	dc.AgentShareTMem() &&
	dc.AgentShareSignatureTMem() &&
	dc.InFactTMem() &&
	dc.SharedSecretTMem() &&
	dc.ClientLtKeyIdTMem() &&
	dc.ClientShareTMem() &&
	dc.ClientShareSignatureTMem() &&
	dc.SigSessionKeysTMem() &&
	dc.LocalInFactTMem() &&
	dc.RemoteInFactTMem() &&
	dc.LocalOutFactTMem() &&
	dc.RemoteOutFactTMem()
}

pred (dc *dataChannel) IoSpecMemMain() {
	dc.TokenMem() &&
	dc.AbsStateMem()
}

pred (dc *dataChannel) IoSpecMemPartial() {
	dc.RidMem() &&
	dc.AgentIdTMem() &&
	dc.KMSIdTMem() &&
	dc.ClientIdTMem() &&
	dc.ReaderIdTMem() &&
	dc.LogLTPkTMem() &&
	dc.AgentShareTMem() &&
	dc.AgentShareSignatureTMem() &&
	dc.InFactTMem() &&
	dc.SharedSecretTMem() &&
	dc.ClientLtKeyIdTMem() &&
	dc.ClientShareTMem() &&
	dc.ClientShareSignatureTMem() &&
	dc.SigSessionKeysTMem() // &&
	// dc.LocalInFactTMem() &&
	// dc.RemoteInFactTMem() &&
	// dc.LocalOutFactTMem() &&
	// dc.RemoteOutFactTMem()
}

pred (dc *dataChannel) TokenMem()

ghost
requires acc(dc.TokenMem(), _)
pure func (dc *dataChannel) getTokenInternal() pl.Place

ghost
requires acc(dc.IoSpecMemMain(), _)
pure func (dc *dataChannel) getToken() pl.Place {
	return unfolding acc(dc.IoSpecMemMain(), _) in dc.getTokenInternal()
}

ghost
requires acc(dc.Mem(), _) && dc.getState() >= Initialized && dc.getState() < IODistributed
pure func (dc *dataChannel) GetToken() pl.Place {
	return unfolding acc(dc.Mem(), _) in unfolding acc(dc.MemInternal(dc.dataChannelState), _) in dc.getToken()
}

ghost
preserves dc.TokenMem()
ensures dc.getTokenInternal() == token
func (dc *dataChannel) setToken(token pl.Place)

pred (dc *dataChannel) RidMem()

ghost
requires acc(dc.RidMem(), _)
pure func (dc *dataChannel) getRidInternal() tm.Term

ghost
requires acc(dc.IoSpecMemPartial(), _)
pure func (dc *dataChannel) getRid() tm.Term {
	return unfolding acc(dc.IoSpecMemPartial(), _) in dc.getRidInternal()
}

// ghost
// requires acc(dc.IoSpecMemPartial(), _)
// pure func (dc *dataChannel) getRidPartial() tm.Term {
// 	return unfolding acc(dc.IoSpecMemPartial(), _) in dc.getRidInternal()
// }

// ghost
// requires acc(dc.MemInternal(state), _) && state >= Initialized && state < IODistributed
// pure func (dc *dataChannel) GetRidInternal(state DataChannelState) tm.Term {
// 	return unfolding acc(dc.MemInternal(state), _) in dc.getRid()
// }

// ghost
// requires acc(dc.Mem(), _) && dc.getState() >= Initialized && dc.getState() < IODistributed
// pure func (dc *dataChannel) GetRid0() tm.Term {
// 	return unfolding acc(dc.Mem(), _) in dc.GetRidInternal(dc.dataChannelState)
// }

ghost
requires acc(dc.Mem(), _) && dc.getState() >= Initialized && dc.getState() < IODistributed
pure func (dc *dataChannel) GetRid() tm.Term {
	return unfolding acc(dc.Mem(), _) in unfolding acc(dc.MemInternal(dc.dataChannelState), _) in dc.getRid()
}

// ghost
// requires acc(dc.Mem(), _) && unfolding acc(dc.Mem(), _) in (dc.dataChannelState >= Initialized && dc.dataChannelState < IODistributed)
// pure func (dc *dataChannel) GetRid2() tm.Term {
// 	return unfolding acc(dc.Mem(), _) in dc.getRid()
// }

// ghost
// requires acc(dc.Mem(), _) && dc.getState() >= Initialized && dc.getState() < IODistributed
// func foo(dc *dataChannel) {
// 	assert dc.getState() >= Initialized && dc.getState() < IODistributed
// 	unfold acc(dc.Mem(), _)
// 	assert dc.dataChannelState >= Initialized && dc.dataChannelState < IODistributed
// }

ghost
preserves dc.RidMem()
ensures dc.getRidInternal() == rid
func (dc *dataChannel) setRid(rid tm.Term)

pred (dc *dataChannel) AbsStateMem()

ghost
requires acc(dc.AbsStateMem(), _)
pure func (dc *dataChannel) getAbsStateInternal() mset[ft.Fact]

ghost
requires acc(dc.IoSpecMemMain(), _)
pure func (dc *dataChannel) getAbsState() mset[ft.Fact] {
	return unfolding acc(dc.IoSpecMemMain(), _) in dc.getAbsStateInternal()
}

ghost
requires acc(dc.Mem(), _) && dc.getState() >= Initialized && dc.getState() < IODistributed
pure func (dc *dataChannel) GetAbsState() mset[ft.Fact] {
	return unfolding acc(dc.Mem(), _) in unfolding acc(dc.MemInternal(dc.dataChannelState), _) in dc.getAbsState()
}

ghost
preserves dc.AbsStateMem()
ensures dc.getAbsStateInternal() == state
func (dc *dataChannel) setAbsState(state mset[ft.Fact])

pred (dc *dataChannel) AgentIdTMem()

ghost
requires acc(dc.AgentIdTMem(), _)
pure func (dc *dataChannel) getAgentIdTInternal() tm.Term

ghost
requires acc(dc.IoSpecMemPartial(), _)
pure func (dc *dataChannel) getAgentIdT() tm.Term {
	return unfolding acc(dc.IoSpecMemPartial(), _) in dc.getAgentIdTInternal()
}

ghost
requires acc(dc.Mem(), _) && dc.getState() >= Initialized
pure func (dc *dataChannel) GetAgentIdT() tm.Term {
	return unfolding acc(dc.Mem(), _) in unfolding acc(dc.MemInternal(dc.dataChannelState), _) in dc.getAgentIdT()
}

ghost
preserves dc.AgentIdTMem()
ensures dc.getAgentIdTInternal() == agentIdT
func (dc *dataChannel) setAgentIdT(agentIdT tm.Term)

pred (dc *dataChannel) KMSIdTMem()

ghost
requires acc(dc.KMSIdTMem(), _)
pure func (dc *dataChannel) getKMSIdTInternal() tm.Term

ghost
requires acc(dc.IoSpecMemPartial(), _)
pure func (dc *dataChannel) getKMSIdT() tm.Term {
	return unfolding acc(dc.IoSpecMemPartial(), _) in dc.getKMSIdTInternal()
}

ghost
requires acc(dc.Mem(), _) && dc.getState() >= Initialized
pure func (dc *dataChannel) GetKMSIdT() tm.Term {
	return unfolding acc(dc.Mem(), _) in unfolding acc(dc.MemInternal(dc.dataChannelState), _) in dc.getKMSIdT()
}

ghost
preserves dc.KMSIdTMem()
ensures dc.getKMSIdTInternal() == kmsIdT
func (dc *dataChannel) setKMSIdT(kmsIdT tm.Term)

pred (dc *dataChannel) ClientIdTMem()

ghost
requires acc(dc.ClientIdTMem(), _)
pure func (dc *dataChannel) getClientIdTInternal() tm.Term

ghost
requires acc(dc.IoSpecMemPartial(), _)
pure func (dc *dataChannel) getClientIdT() tm.Term {
	return unfolding acc(dc.IoSpecMemPartial(), _) in dc.getClientIdTInternal()
}

ghost
requires acc(dc.Mem(), _) && dc.getState() >= Initialized
pure func (dc *dataChannel) GetClientIdT() tm.Term {
	return unfolding acc(dc.Mem(), _) in unfolding acc(dc.MemInternal(dc.dataChannelState), _) in dc.getClientIdT()
}

ghost
preserves dc.ClientIdTMem()
ensures dc.getClientIdTInternal() == clientIdT
func (dc *dataChannel) setClientIdT(clientIdT tm.Term)

pred (dc *dataChannel) ReaderIdTMem()

ghost
requires acc(dc.ReaderIdTMem(), _)
pure func (dc *dataChannel) getReaderIdTInternal() tm.Term

ghost
requires acc(dc.IoSpecMemPartial(), _)
pure func (dc *dataChannel) getReaderIdT() tm.Term {
	return unfolding acc(dc.IoSpecMemPartial(), _) in dc.getReaderIdTInternal()
}

ghost
requires acc(dc.Mem(), _) && dc.getState() >= Initialized
pure func (dc *dataChannel) GetReaderIdT() tm.Term {
	return unfolding acc(dc.Mem(), _) in unfolding acc(dc.MemInternal(dc.dataChannelState), _) in dc.getReaderIdT()
}

ghost
preserves dc.ReaderIdTMem()
ensures dc.getReaderIdTInternal() == readerIdT
func (dc *dataChannel) setReaderIdT(readerIdT tm.Term)

// ghost
// requires acc(IoSpecMem(sessionId), _)
// pure func getSendKeyT(sessionId string) tm.Term

pred (dc *dataChannel) LogLTPkTMem()

ghost
requires acc(dc.LogLTPkTMem(), _)
pure func (dc *dataChannel) getLogLTPkTInternal() tm.Term

ghost
requires acc(dc.IoSpecMemPartial(), _)
pure func (dc *dataChannel) getLogLTPkT() tm.Term {
	return unfolding acc(dc.IoSpecMemPartial(), _) in dc.getLogLTPkTInternal()
}

ghost
requires acc(dc.Mem(), _) && dc.getState() >= Initialized
pure func (dc *dataChannel) GetLogLTPkT() tm.Term {
	return unfolding acc(dc.Mem(), _) in unfolding acc(dc.MemInternal(dc.dataChannelState), _) in dc.getLogLTPkT()
}

ghost
preserves dc.LogLTPkTMem()
ensures dc.getLogLTPkTInternal() == logLTPkT
func (dc *dataChannel) setLogLTPkT(logLTPkT tm.Term)

pred (dc *dataChannel) AgentShareTMem()

ghost
requires acc(dc.AgentShareTMem(), _)
pure func (dc *dataChannel) getAgentShareTInternal() tm.Term

ghost
requires acc(dc.IoSpecMemPartial(), _)
pure func (dc *dataChannel) getAgentShareT() tm.Term {
	return unfolding acc(dc.IoSpecMemPartial(), _) in dc.getAgentShareTInternal()
}

ghost
requires acc(dc.Mem(), _) && dc.getState() >= Initialized
pure func (dc *dataChannel) GetAgentShareT() tm.Term {
	return unfolding acc(dc.Mem(), _) in unfolding acc(dc.MemInternal(dc.dataChannelState), _) in dc.getAgentShareT()
}

ghost
preserves dc.AgentShareTMem()
ensures dc.getAgentShareTInternal() == shareT
func (dc *dataChannel) setAgentShareT(shareT tm.Term)

pred (dc *dataChannel) AgentShareSignatureTMem()

ghost
requires acc(dc.AgentShareSignatureTMem(), _)
pure func (dc *dataChannel) getAgentShareSignatureTInternal() tm.Term

ghost
requires acc(dc.IoSpecMemPartial(), _)
pure func (dc *dataChannel) getAgentShareSignatureT() tm.Term {
	return unfolding acc(dc.IoSpecMemPartial(), _) in dc.getAgentShareSignatureTInternal()
}

ghost
requires acc(dc.Mem(), _) && dc.getState() >= Initialized
pure func (dc *dataChannel) GetAgentShareSignatureT() tm.Term {
	return unfolding acc(dc.Mem(), _) in unfolding acc(dc.MemInternal(dc.dataChannelState), _) in dc.getAgentShareSignatureT()
}

ghost
preserves dc.AgentShareSignatureTMem()
ensures dc.getAgentShareSignatureTInternal() == signatureT
func (dc *dataChannel) setAgentShareSignatureT(signatureT tm.Term)

pred (dc *dataChannel) InFactTMem()

ghost
requires acc(dc.InFactTMem(), _)
pure func (dc *dataChannel) getInFactTInternal() tm.Term

ghost
requires acc(dc.IoSpecMemPartial(), _)
pure func (dc *dataChannel) getInFactT() tm.Term {
	return unfolding acc(dc.IoSpecMemPartial(), _) in dc.getInFactTInternal()
}

ghost
requires acc(dc.Mem(), _) && dc.getState() >= Initialized
pure func (dc *dataChannel) GetInFactT() tm.Term {
	return unfolding acc(dc.Mem(), _) in unfolding acc(dc.MemInternal(dc.dataChannelState), _) in dc.getInFactT()
}

ghost
preserves dc.InFactTMem()
ensures dc.getInFactTInternal() == inFactT
func (dc *dataChannel) setInFactT(inFactT tm.Term)

pred (dc *dataChannel) SharedSecretTMem()

ghost
requires acc(dc.SharedSecretTMem(), _)
pure func (dc *dataChannel) getSharedSecretTInternal() tm.Term

ghost
requires acc(dc.IoSpecMemPartial(), _)
pure func (dc *dataChannel) getSharedSecretT() tm.Term {
	return unfolding acc(dc.IoSpecMemPartial(), _) in dc.getSharedSecretTInternal()
}

ghost
requires acc(dc.Mem(), _) && dc.getState() >= Initialized
pure func (dc *dataChannel) GetSharedSecretT() tm.Term {
	return unfolding acc(dc.Mem(), _) in unfolding acc(dc.MemInternal(dc.dataChannelState), _) in dc.getSharedSecretT()
}

ghost
preserves dc.SharedSecretTMem()
ensures dc.getSharedSecretTInternal() == sharedSecretT
func (dc *dataChannel) setSharedSecretT(sharedSecretT tm.Term)

pred (dc *dataChannel) ClientLtKeyIdTMem()

ghost
requires acc(dc.ClientLtKeyIdTMem(), _)
pure func (dc *dataChannel) getClientLtKeyIdTInternal() tm.Term

ghost
requires acc(dc.IoSpecMemPartial(), _)
pure func (dc *dataChannel) getClientLtKeyIdT() tm.Term {
	return unfolding acc(dc.IoSpecMemPartial(), _) in dc.getClientLtKeyIdTInternal()
}

ghost
requires acc(dc.Mem(), _) && dc.getState() >= Initialized
pure func (dc *dataChannel) GetClientLtKeyIdT() tm.Term {
	return unfolding acc(dc.Mem(), _) in unfolding acc(dc.MemInternal(dc.dataChannelState), _) in dc.getClientLtKeyIdT()
}

ghost
preserves dc.ClientLtKeyIdTMem()
ensures dc.getClientLtKeyIdTInternal() == clientLtKeyIdT
func (dc *dataChannel) setClientLtKeyIdT(clientLtKeyIdT tm.Term)

pred (dc *dataChannel) ClientShareTMem()

ghost
requires acc(dc.ClientShareTMem(), _)
pure func (dc *dataChannel) getClientShareTInternal() tm.Term

ghost
requires acc(dc.IoSpecMemPartial(), _)
pure func (dc *dataChannel) getClientShareT() tm.Term {
	return unfolding acc(dc.IoSpecMemPartial(), _) in dc.getClientShareTInternal()
}

ghost
requires acc(dc.Mem(), _) && dc.getState() >= Initialized
pure func (dc *dataChannel) GetClientShareT() tm.Term {
	return unfolding acc(dc.Mem(), _) in unfolding acc(dc.MemInternal(dc.dataChannelState), _) in dc.getClientShareT()
}

ghost
preserves dc.ClientShareTMem()
ensures dc.getClientShareTInternal() == clientShareT
func (dc *dataChannel) setClientShareT(clientShareT tm.Term)

pred (dc *dataChannel) ClientShareSignatureTMem()

ghost
requires acc(dc.ClientShareSignatureTMem(), _)
pure func (dc *dataChannel) getClientShareSignatureTInternal() tm.Term

ghost
requires acc(dc.IoSpecMemPartial(), _)
pure func (dc *dataChannel) getClientShareSignatureT() tm.Term {
	return unfolding acc(dc.IoSpecMemPartial(), _) in dc.getClientShareSignatureTInternal()
}

ghost
requires acc(dc.Mem(), _) && dc.getState() >= Initialized
pure func (dc *dataChannel) GetClientShareSignatureT() tm.Term {
	return unfolding acc(dc.Mem(), _) in unfolding acc(dc.MemInternal(dc.dataChannelState), _) in dc.getClientShareSignatureT()
}

ghost
preserves dc.ClientShareSignatureTMem()
ensures dc.getClientShareSignatureTInternal() == clientShareSignatureT
func (dc *dataChannel) setClientShareSignatureT(clientShareSignatureT tm.Term)

pred (dc *dataChannel) SigSessionKeysTMem()

ghost
requires acc(dc.SigSessionKeysTMem(), _)
pure func (dc *dataChannel) getSigSessionKeysTInternal() tm.Term

ghost
requires acc(dc.IoSpecMemPartial(), _)
pure func (dc *dataChannel) getSigSessionKeysT() tm.Term {
	return unfolding acc(dc.IoSpecMemPartial(), _) in dc.getSigSessionKeysTInternal()
}

ghost
requires acc(dc.Mem(), _) && dc.getState() >= Initialized
pure func (dc *dataChannel) GetSigSessionKeysT() tm.Term {
	return unfolding acc(dc.Mem(), _) in unfolding acc(dc.MemInternal(dc.dataChannelState), _) in dc.getSigSessionKeysT()
}

ghost
preserves dc.SigSessionKeysTMem()
ensures dc.getSigSessionKeysTInternal() == sigSessionKeysT
func (dc *dataChannel) setSigSessionKeysT(sigSessionKeysT tm.Term)

pred (dc *dataChannel) LocalInFactTMem()

ghost
requires acc(dc.LocalInFactTMem(), _)
pure func (dc *dataChannel) getLocalInFactTInternal() tm.Term

// ghost
// requires acc(dc.IoSpecMemPartial(), _)
// pure func (dc *dataChannel) getLocalInFactT() tm.Term {
// 	return unfolding acc(dc.IoSpecMemPartial(), _) in dc.getLocalInFactTInternal()
// }

ghost
preserves dc.LocalInFactTMem()
ensures dc.getLocalInFactTInternal() == inFactT
func (dc *dataChannel) setLocalInFactT(inFactT tm.Term)

pred (dc *dataChannel) RemoteInFactTMem()

ghost
requires acc(dc.RemoteInFactTMem(), _)
pure func (dc *dataChannel) getRemoteInFactTInternal() tm.Term

// ghost
// requires acc(dc.IoSpecMemPartial(), _)
// pure func (dc *dataChannel) getRemoteInFactT() tm.Term {
// 	return unfolding acc(dc.IoSpecMemPartial(), _) in dc.getRemoteInFactTInternal()
// }

ghost
preserves dc.RemoteInFactTMem()
ensures dc.getRemoteInFactTInternal() == inFactT
func (dc *dataChannel) setRemoteInFactT(inFactT tm.Term)

pred (dc *dataChannel) LocalOutFactTMem()

ghost
requires acc(dc.LocalOutFactTMem(), _)
pure func (dc *dataChannel) getLocalOutFactTInternal() tm.Term

// ghost
// requires acc(dc.IoSpecMemPartial(), _)
// pure func (dc *dataChannel) getLocalOutFactT() tm.Term {
// 	return unfolding acc(dc.IoSpecMemPartial(), _) in dc.getLocalOutFactTInternal()
// }

ghost
preserves dc.LocalOutFactTMem()
ensures dc.getLocalOutFactTInternal() == outFactT
func (dc *dataChannel) setLocalOutFactT(outFactT tm.Term)

pred (dc *dataChannel) RemoteOutFactTMem()

ghost
requires acc(dc.RemoteOutFactTMem(), _)
pure func (dc *dataChannel) getRemoteOutFactTInternal() tm.Term

// ghost
// requires acc(dc.IoSpecMemPartial(), _)
// pure func (dc *dataChannel) getRemoteOutFactT() tm.Term {
// 	return unfolding acc(dc.IoSpecMemPartial(), _) in dc.getRemoteOutFactTInternal()
// }

ghost
preserves dc.RemoteOutFactTMem()
ensures dc.getRemoteOutFactTInternal() == outFactT
func (dc *dataChannel) setRemoteOutFactT(outFactT tm.Term)

ghost
requires acc(dc.Mem(), _) && dc.getState() >= BlockCipherInitialized
pure func (dc *dataChannel) GetEncKeyT() tm.Term {
	return unfolding acc(dc.Mem(), _) in unfolding acc(dc.MemInternal(dc.dataChannelState), _) in dc.blockCipher.GetEncKeyT()
}

// while assuming that verification is enabled is not necessary to prove
// memory safety, we need this assumption for verifying refinement.
// Leaving this function abstract will consider both cases, i.e.,
// encryption being disabled or enabled.
ghost
pure func assumeEncryptionEnabledForVerification() bool {
	return true
}
@*/

// NewDataChannel constructs datachannel objects.
// @ requires context.Mem() && cancelFlag.Mem()
// @ requires ctx != nil && ctx.Inv() && inputStreamMessageHandler implements StreamDataHandlerSpec{ctx}
// @ requires pl.token(t0) && iospec.P_Agent(t0, rid, mset[ft.Fact]{})
// @ ensures  res.Mem() && typeOf(res) == *dataChannel
// @ ensures  err == nil ==> res.(* dataChannel).getState() == Initialized
// TODO: make `ctx` a ghost parameter as soon as Gobra supports ghost fields
func NewDataChannel(context contextPkg.T,
	channelId string,
	clientId string,
	logReaderId string,
	inputStreamMessageHandler InputStreamMessageHandler,
	cancelFlag task.CancelFlag,
	/*@ ctx StreamDataHandlerContext, t0 pl.Place, rid tm.Term @*/) (res IDataChannel, err error) {

	tmp /*@ @ @*/ := dataChannel{}
	dc := &tmp
	cl := // @ requires log != nil
		// @ requires datastream.QuantifiedStreamDataHandlerSpecWand(msg)
		// @ preserves acc(log.Mem(), _) && tmp.RecvRoutineMem()
		// @ ensures err == nil ==> msg.Mem()
		// @ ensures err != nil ==> err.ErrorMem()
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
	dc.hs.startReceivingChan = make(chan MessageReceptionPayload)
	//@ dc.hs.startReceivingChan.Init(StartReceivingChanInv!<dc, _!>, PredTrue!<!>)
	dc.inputStreamMessageHandler = inputStreamMessageHandler
	//@ dc.msgHandlerCtx = ctx
	dc.hs.responseChan = make(chan ResponseChanPayload)
	//@ dc.hs.responseChan.Init(ResponseChanInv!<dc, _!>, PredTrue!<!>)
	// we allocate some ghost heap space:
	//@ inhale dc.IoSpecMem()
	//@ unfold dc.IoSpecMem()
	// the following assertion is needed:
	//@ assert dc.TokenMem()
	//@ dc.setToken(t0)
	//@ dc.setRid(rid)
	//@ dc.setAbsState(mset[ft.Fact]{})
	// fold dc.IoSpecMem()
	//@ fold dc.IoSpecMemMain()
	//@ fold dc.IoSpecMemPartial()

	//@ fold dc.RecvRoutineMem()
	//@ fold acc(dc.MemChannelState(), 1/2)
	//@ fold dc.MemInternal(Uninitialized)
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
		return dc, fmtErrorf("failed to create data stream with error: %s", err /*@, perm(1/2) @*/)
	}

	err = dc.initialize(dataStream, logReaderId)
	if err != nil {
		return dc, err
	}

	return dc, nil
}

// initialize populates datachannel object.
// @ requires dc.Mem() && dc.getState() == Uninitialized && dataStream.Mem()
// @ requires dc.IoSpecMemMain() && dc.IoSpecMemPartial() && pl.token(dc.getToken()) && iospec.P_Agent(dc.getToken(), dc.getRid(), dc.getAbsState())
// @ ensures  dc.Mem()
// @ ensures  err == nil ==> dc.getState() == Initialized
func (dc *dataChannel) initialize(dataStream *datastream.DataStream, logReaderId string) (err error) {
	// @ unfold dc.Mem()
	// @ unfold dc.MemInternal(Uninitialized)
	dc.dataStream = dataStream
	dc.encryptionEnabled = false
	dc.hs.error = nil
	dc.hs.complete = false
	dc.hs.skipped = false
	dc.hs.handshakeEndTime = time.Now()
	dc.hs.handshakeStartTime = time.Now()
	dc.state.kmsService, err = dc.dataStream.GetKMSService( /*@ perm(1/2) @*/ )
	if err != nil {
		// @ fold dc.MemInternal(Uninitialized)
		// @ fold dc.Mem()
		return fmtErrorf("failed to initialize KMS service: %v", err /*@, perm(1/2) @*/)
	}

	// @ t0 := dc.getToken()
	// @ rid := dc.getRid()
	// @ s0 := dc.getAbsState()
	// @ unfold iospec.P_Agent(t0, rid, s0)
	// @ unfold iospec.phiRF_Agent_17(t0, rid, s0)
	// @ t1 := iospec.get_e_Setup_Agent_placeDst(t0, rid)
	// @ agentIdT := iospec.get_e_Setup_Agent_r1(t0, rid)
	// @ kmsIdT := iospec.get_e_Setup_Agent_r2(t0, rid)
	// @ clientIdT := iospec.get_e_Setup_Agent_r3(t0, rid)
	// @ readerIdT := iospec.get_e_Setup_Agent_r4(t0, rid)
	// @ logLTPkT := iospec.get_e_Setup_Agent_r6(t0, rid)
	// @ setupFact := ft.Setup_Agent(rid, agentIdT, kmsIdT, clientIdT, readerIdT, iospec.get_e_Setup_Agent_r5(t0, rid), logLTPkT)
	dc.agentLTKeyARN, dc.logLTPk, err = getInitialValues(dc.state.kmsService, dc.dataStream.GetInstanceId(), dc.dataStream.GetClientId(), logReaderId /*@, t0, rid @*/)
	if err != nil {
		// @ fold iospec.phiRF_Agent_17(t0, rid, s0)
		// @ fold iospec.P_Agent(t0, rid, s0)
		// @ fold dc.MemInternal(Uninitialized)
		// @ fold dc.Mem()
		return fmtErrorf("failed to initialize KMS service: %v", err /*@, perm(1/2) @*/)
	}

	// @ s1 := s0 union mset[ft.Fact]{ setupFact }
	// @ unfold dc.IoSpecMemMain()
	// @ unfold dc.IoSpecMemPartial()
	// @ dc.setToken(t1)
	// @ dc.setAbsState(s1)
	// @ dc.setAgentIdT(agentIdT)
	// @ dc.setKMSIdT(kmsIdT)
	// @ dc.setClientIdT(clientIdT)
	// @ dc.setReaderIdT(readerIdT)
	// @ dc.setLogLTPkT(logLTPkT)
	// @ fold dc.IoSpecMemPartial()
	// @ fold dc.IoSpecMemMain()
	dc.logReaderId = logReaderId
	// @ unfold acc(dc.MemChannelState(), 1/2)
	dc.dataChannelState = Initialized
	// @ fold acc(dc.MemChannelState(), 1/2)
	// @ fold dc.MemInternal(Initialized)
	// @ fold dc.Mem()
	return
}

// we assume that this function returns the initial values used by this agent session
// according to the `Agent_Init` Tamarin rule
// @ trusted
// @ preserves kmsService.Mem()
// @ requires pl.token(t) && iospec.e_Setup_Agent(t, rid)
// @ ensures  err == nil ==> logLTPk.Mem()
// @ ensures  err == nil ==> pl.token(old(iospec.get_e_Setup_Agent_placeDst(t, rid))) &&
// @	by.gamma(tm.pubTerm(pub.pub_msg(agentId))) == by.gamma(old(iospec.get_e_Setup_Agent_r1(t, rid))) &&
// @	by.gamma(tm.pubTerm(pub.pub_msg(clientId))) == by.gamma(old(iospec.get_e_Setup_Agent_r3(t, rid))) &&
// @	by.gamma(tm.pubTerm(pub.pub_msg(logReaderId))) == by.gamma(old(iospec.get_e_Setup_Agent_r4(t, rid))) &&
// @	by.gamma(tm.pubTerm(pub.pub_msg(agentLTKeyARN))) == by.gamma(old(iospec.get_e_Setup_Agent_r5(t, rid))) &&
// @	logLTPk.Abs() == by.gamma(old(iospec.get_e_Setup_Agent_r6(t, rid)))
// Patern axiom applies locally:
// @ ensures  by.gamma(old(iospec.get_e_Setup_Agent_r1(t, rid))) == by.gamma(tm.pubTerm(pub.pub_msg(agentId))) ==> old(iospec.get_e_Setup_Agent_r1(t, rid)) == tm.pubTerm(pub.pub_msg(agentId))
// @ ensures  by.gamma(old(iospec.get_e_Setup_Agent_r3(t, rid))) == by.gamma(tm.pubTerm(pub.pub_msg(clientId))) ==> old(iospec.get_e_Setup_Agent_r3(t, rid)) == tm.pubTerm(pub.pub_msg(clientId))
// @ ensures  by.gamma(old(iospec.get_e_Setup_Agent_r4(t, rid))) == by.gamma(tm.pubTerm(pub.pub_msg(logReaderId))) ==> old(iospec.get_e_Setup_Agent_r4(t, rid)) == tm.pubTerm(pub.pub_msg(logReaderId))
// @ ensures  by.gamma(old(iospec.get_e_Setup_Agent_r5(t, rid))) == by.gamma(tm.pubTerm(pub.pub_msg(agentLTKeyARN))) ==> old(iospec.get_e_Setup_Agent_r5(t, rid)) == tm.pubTerm(pub.pub_msg(agentLTKeyARN))
// @ ensures err != nil ==> err.ErrorMem()
// @ ensures err != nil ==> pl.token(t) && iospec.e_Setup_Agent(t, rid) &&
// @ 	iospec.get_e_Setup_Agent_placeDst(t, rid) == old(iospec.get_e_Setup_Agent_placeDst(t, rid)) &&
// @ 	iospec.get_e_Setup_Agent_r1(t, rid) == old(iospec.get_e_Setup_Agent_r1(t, rid)) &&
// @ 	iospec.get_e_Setup_Agent_r2(t, rid) == old(iospec.get_e_Setup_Agent_r2(t, rid)) &&
// @ 	iospec.get_e_Setup_Agent_r3(t, rid) == old(iospec.get_e_Setup_Agent_r3(t, rid)) &&
// @ 	iospec.get_e_Setup_Agent_r4(t, rid) == old(iospec.get_e_Setup_Agent_r4(t, rid)) &&
// @ 	iospec.get_e_Setup_Agent_r5(t, rid) == old(iospec.get_e_Setup_Agent_r5(t, rid)) &&
// @ 	iospec.get_e_Setup_Agent_r6(t, rid) == old(iospec.get_e_Setup_Agent_r6(t, rid))
func getInitialValues(kmsService *crypto.KMSService, agentId string, clientId string, logReaderId string /*@, ghost t pl.Place, ghost rid tm.Term @*/) (agentLTKeyARN string, logLTPk *rsa.PublicKey, err error) {
	metadata, err := kmsService.CreateKeyAssymetric()
	if err != nil {
		err = fmtErrorf("failed to create agent LTK: %v", err /*@, perm(1/1) @*/)
		return "", nil, err /*@, t @*/
	}

	//@ unfold metadata.Mem()
	if metadata.Arn == nil {
		err = fmtErrorfMetadata("asymmetric key ARN is nil, metadata: %+v", metadata /*@, perm(1/2) @*/)
		return "", nil, err /*@, t @*/
	}
	agentLTKeyARN = *metadata.Arn
	//@ cryptoRand.GetReaderMem()
	sk, err := rsa.GenerateKey(cryptoRand.Reader, 4096 /*@, perm(1/2) @*/)
	if err != nil {
		err = fmtErrorf("failed to create log secret key: %v", err /*@, perm(1/1) @*/)
		return "", nil, err /*@, t @*/
	}
	//@ unfold sk.Mem()
	logLTPk = &sk.PublicKey
	return
}

// SendStreamDataMessage sends a data message in a form of AgentMessage for streaming.
// Requires that the handshake is either complete or skipped
// @ requires log != nil
// @ requires QuantifiedSendStreamDataMessageWand(inputData, inputDataT, p)
// @ preserves dc.Mem()
// @ preserves acc(log.Mem(), _)
// @ ensures err != nil ==> err.ErrorMem()
func (dc *dataChannel) SendStreamDataMessage(log logger.T, payloadType mgsContracts.PayloadType, inputData []byte /*@, ghost p perm, ghost inputDataT tm.Term @*/) (err error) {
	if dc.getState() != IODistributed {
		return fmtErrorfState("DataChannel is in an invalid state %d", dc.getState())
	}

	if payloadType != mgsContracts.Output && payloadType != mgsContracts.StdErr && payloadType != mgsContracts.ExitCode {
		return fmtErrorfPayloadType("Rejecting stream data message with payload type %d as it would otherwise be sent in plaintext", payloadType)
	}

	//@ unfold dc.Mem()
	//@ unfold acc(dc.MemInternal(IODistributed), 1/2)
	//@ rid, AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, xT, SigX := dc.getRid(), dc.getAgentIdT(), dc.getKMSIdT(), dc.getClientIdT(), dc.getReaderIdT(), tm.pubTerm(pub.pub_msg(dc.agentLTKeyARN)), dc.getLogLTPkT(), dc.getAgentShareT(), dc.getAgentShareSignatureT()

	// ----- start local receive I/O operation -----
	//@ dc.ioLock.Lock()
	//@ unfold IoLockInv!<dc, dc.dataStream.GetInstanceId(), dc.dataStream.GetClientId(), dc.agentLTKeyARN!>()

	//@ t0 := dc.getToken()
	//@ s0 := dc.getAbsState()

	// receive `inputData` from environment:
	//@ unfold iospec.P_Agent(t0, rid, s0)
	//@ unfold iospec.phiRF_Agent_16(t0, rid, s0)
	//@ t1 := iospec.get_e_InFact_placeDst(t0, rid)
	//@ s1 := s0 union mset[ft.Fact]{ ft.InFact_Agent(rid, iospec.get_e_InFact_r1(t0, rid)) }
	//@ unfold QuantifiedSendStreamDataMessageWand(inputData, inputDataT, p)
	//@ unfold SendStreamDataMessageWand(t0, rid, inputData, inputDataT, p)
	//@ apply (pl.token(t0) && iospec.e_InFact(t0, rid)) --* (acc(bytes.SliceMem(inputData), p) && by.gamma(inputDataT) == abs.Abs(inputData) && inputDataT == old[#lhs](iospec.get_e_InFact_r1(t0, rid)) && pl.token(old[#lhs](iospec.get_e_InFact_placeDst(t0, rid))))

	//@ unfold dc.IoSpecMemMain()
	//@ dc.setToken(t1)
	//@ dc.setAbsState(s1)
	//@ dc.setLocalInFactT(inputDataT)
	//@ dc.ioLockDidLocalReceive = true
	//@ fold dc.IoSpecMemMain()

	//@ fold IoLockInv!<dc, dc.dataStream.GetInstanceId(), dc.dataStream.GetClientId(), dc.agentLTKeyARN!>()
	//@ dc.ioLock.Unlock()
	// ----- end local receive I/O operation -----

	// ----- start internal I/O operation -----
	//@ dc.ioLock.Lock()
	//@ unfold IoLockInv!<dc, dc.dataStream.GetInstanceId(), dc.dataStream.GetClientId(), dc.agentLTKeyARN!>()
	//@ t1 = dc.getToken()
	//@ s1 = dc.getAbsState()
	//@ sharedSecretT := dc.getSharedSecretT()
	//@ clientLtKeyIdT := dc.getClientLtKeyIdT()
	//@ clientSecretT := dc.getClientShareT()
	//@ sigYT := dc.getClientShareSignatureT()
	//@ sigSessionKeysT := dc.getSigSessionKeysT()	

	// obtain permission to send the ciphertext containing `inputData`:
	/*@
		l := mset[ft.Fact] {
			ft.St_Agent_10(rid, AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, xT, SigX, clientLtKeyIdT, tm.exp(tm.pubTerm(pub.const_g_pub()), clientSecretT), sigYT, sigSessionKeysT),
			ft.InFact_Agent(rid, inputDataT),
		}
		a := mset[cl.Claim] {
			cl.AgentSendLoop(rid, AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, xT, clientLtKeyIdT, tm.exp(tm.pubTerm(pub.const_g_pub()), clientSecretT)),
		}
		r := mset[ft.Fact] {
	    	ft.St_Agent_10(rid, AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, xT, SigX, clientLtKeyIdT, tm.exp(tm.pubTerm(pub.const_g_pub()), clientSecretT), sigYT, sigSessionKeysT),
	        ft.OutFact_Agent(rid, tm.pair(tm.pubTerm(pub.const_Message_pub()), tm.senc(inputDataT, tm.kdf1(sharedSecretT)))),
	        ft.OutFact_Agent(rid, tm.pair(tm.pubTerm(pub.const_Log_pub()), tm.pair(tm.pubTerm(pub.const_Message_pub()), tm.senc(inputDataT, tm.kdf1(sharedSecretT))))),
		}
	@*/
	//@ unfold iospec.P_Agent(t1, rid, s1)
	//@ unfold iospec.phiR_Agent_11(t1, rid, s1)
	//@ t2 := iospec.internBIO_e_Agent_SendMessages(t1, rid, AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, xT, SigX, clientLtKeyIdT, tm.exp(tm.pubTerm(pub.const_g_pub()), clientSecretT), sigYT, sigSessionKeysT, inputDataT, l, a, r)
	//@ s2 := ft.U(l, r, s1)

	//@ unfold dc.IoSpecMemMain()
	//@ dc.setToken(t2)
	//@ dc.setAbsState(s2)
	//@ dc.ioLockDidLocalReceive = false
	//@ dc.setRemoteOutFactT(tm.pair(tm.pubTerm(pub.const_Message_pub()), tm.senc(inputDataT, tm.kdf1(sharedSecretT))))
	//@ dc.ioLockCanRemoteSend = true
	//@ fold dc.IoSpecMemMain()

	//@ fold IoLockInv!<dc, dc.dataStream.GetInstanceId(), dc.dataStream.GetClientId(), dc.agentLTKeyARN!>()
	//@ dc.ioLock.Unlock()
	// ----- end internal I/O operation -----

	//@ fold acc(dc.MemInternal(IODistributed), 1/2)
	//@ fold dc.Mem()

	return dc.sendData(log, payloadType, inputData /*@, p/2, inputDataT, true, true @*/)
}

// @ requires log != nil && noPerm < p && p <= writePerm
// @ requires dc.Mem()
// @ requires requiresEncryption == (payloadType == mgsContracts.Output || payloadType == mgsContracts.StdErr || payloadType == mgsContracts.ExitCode || payloadType == mgsContracts.HandshakeComplete)
// @ requires dc.getState() >= (requiresEncryption ? BlockCipherReady : BlockCipherInitialized)
// @ requires requiresLock ==> dc.getState() == IODistributed && requiresEncryption
// @ requires requiresLock ==> unfolding acc(dc.Mem(), _) in unfolding acc(dc.MemInternal(IODistributed), _) in unfolding acc(dc.IoSpecMemPartial(), _) in dc.ioLockCanRemoteSend && dc.getRemoteOutFactTInternal() == tm.pair(mgsContracts.payloadTypeTerm(payloadType), tm.senc(inputDataT, dc.GetEncKeyT()))
// @ requires !requiresLock ==> dc.getState() < IODistributed
// @ requires !requiresLock ==> (requiresEncryption ?
// @ 	ft.OutFact_Agent(dc.GetRid(), tm.pair(mgsContracts.payloadTypeTerm(payloadType), tm.senc(inputDataT, dc.GetEncKeyT()))) # dc.GetAbsState() > 0 :
// @ 	ft.OutFact_Agent(dc.GetRid(), tm.pair(mgsContracts.payloadTypeTerm(payloadType), inputDataT)) # dc.GetAbsState() > 0)
// @ requires acc(bytes.SliceMem(inputData), p) && by.gamma(inputDataT) == abs.Abs(inputData)
// @ preserves acc(log.Mem(), _)
// @ ensures dc.Mem() && dc.getState() == old(dc.getState())
// @ ensures err != nil ==> err.ErrorMem()
func (dc *dataChannel) sendData(log logger.T, payloadType mgsContracts.PayloadType, inputData []byte /*@, ghost p perm, ghost inputDataT tm.Term, ghost requiresEncryption bool, ghost requiresLock bool @*/) (err error) {
	// @ ghost state := dc.getState()
	// @ unfold dc.Mem()
	// @ unfold acc(dc.MemInternal(state), 1/2)

	// If encryption has been enabled, encrypt the payload
	if dc.encryptionEnabled && (payloadType == mgsContracts.Output || payloadType == mgsContracts.StdErr || payloadType == mgsContracts.ExitCode || payloadType == mgsContracts.HandshakeComplete) {
		if inputData, err = dc.blockCipher.EncryptWithAESGCM(inputData /*@, p/4 @*/); err != nil {
			err = fmtErrorfInt64Err("error encrypting stream data message sequence %d, err: %v", dc.dataStream.GetStreamDataSequenceNumber( /*@ p/4 @*/ ), err /*@, perm(1/1) @*/)
			// @ fold acc(dc.MemInternal(state), 1/2)
			// @ fold dc.Mem()
			return
		}
		//@ inputDataT = tm.senc(inputDataT, dc.blockCipher.GetEncKeyT())
	}

	/*@
	// ----- start external send I/O operation -----
	ghost if requiresLock {
		dc.ioLock.Lock()
		unfold IoLockInv!<dc, dc.dataStream.GetInstanceId(), dc.dataStream.GetClientId(), dc.agentLTKeyARN!>()
	} else {
		unfold acc(dc.MemInternal(state), 1/2)
	}

	rid, AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, xT, SigX := dc.getRid(), dc.getAgentIdT(), dc.getKMSIdT(), dc.getClientIdT(), dc.getReaderIdT(), tm.pubTerm(pub.pub_msg(dc.agentLTKeyARN)), dc.getLogLTPkT(), dc.getAgentShareT(), dc.getAgentShareSignatureT()
	t0 := dc.getToken()
	s0 := dc.getAbsState()
	sharedSecretT := dc.getSharedSecretT()
	clientLtKeyIdT := dc.getClientLtKeyIdT()
	clientSecretT := dc.getClientShareT()
	sigYT := dc.getClientShareSignatureT()
	sigSessionKeysT := dc.getSigSessionKeysT()
	m := tm.pair(mgsContracts.payloadTypeTerm(payloadType), inputDataT)
	unfold iospec.P_Agent(t0, rid, s0)
	unfold iospec.phiRG_Agent_13(t0, rid, s0)
	@*/

	//@ ghost var t1 pl.Place
	err /*@, t1 @*/ = dc.dataStream.Send(log, payloadType, inputData /*@, p/4, t0, rid, inputDataT, m @*/)
	if err != nil {
		/*@
		fold iospec.phiRG_Agent_13(t0, rid, s0)
		fold iospec.P_Agent(t0, rid, s0)
		ghost if requiresLock {
			fold IoLockInv!<dc, dc.dataStream.GetInstanceId(), dc.dataStream.GetClientId(), dc.agentLTKeyARN!>()
			dc.ioLock.Unlock()
			fold acc(dc.MemInternal(state), 1/2)
		} else {
			fold dc.MemInternal(state)
		}
		fold dc.Mem()
		@*/
		return err
	}
	
	/*@
	unfold dc.IoSpecMemMain()
	dc.setToken(t1)
	s1 := s0 setminus mset[ft.Fact]{ ft.OutFact_Agent(rid, m) }
	dc.setAbsState(s1)
	fold dc.IoSpecMemMain()
	ghost if requiresLock {
		dc.ioLockCanRemoteSend = false
		fold IoLockInv!<dc, dc.dataStream.GetInstanceId(), dc.dataStream.GetClientId(), dc.agentLTKeyARN!>()
		dc.ioLock.Unlock()
		fold acc(dc.MemInternal(state), 1/2)
	} else {
		fold dc.MemInternal(state)
	}
	// ----- end external send I/O operation -----
	fold dc.Mem()
	@*/
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
// @ ensures err != nil ==> err.ErrorMem()
func (dc *dataChannel) SendAgentSessionStateMessage(log logger.T, sessionStatus mgsContracts.SessionStatus) (err error) {
	agentSessionStateContent := &mgsContracts.AgentSessionStateContent{
		SchemaVersion: schemaVersion,
		SessionState:  string(sessionStatus),
		SessionId:     dc.dataStream.GetChannelId(),
	}

	var agentSessionStateContentBytes []byte
	if agentSessionStateContentBytes, err = json.Marshal(agentSessionStateContent); err != nil {
		log.Errorf("Cannot serialize AgentSessionState message err: %v", err)
		return err
	}

	sessionStatusStr := string(sessionStatus)
	//@ fold sessionStatusStr.Mem()
	log.Debugf("Send %s message with session status %s", mgsContracts.AgentSessionState, sessionStatusStr)
	if err := dc.dataStream.SendAgentMessage(log, mgsContracts.AgentSessionState, agentSessionStateContentBytes); err != nil {
		return err
	}
	return nil
}

// @ trusted
// @ preserves dc.RecvRoutineMem()
// @ ensures  err == nil ==> StartReceivingChanInv!<dc, _!>(res)
// @ ensures  err != nil ==> err.ErrorMem()
func (dc *dataChannel) tryReceiveMessageReceptionStatus(timeout time.Duration) (res MessageReceptionPayload, err error) {
	var ok bool
	select {
	case res, ok = <-dc.hs.startReceivingChan:
		if !ok {
			err = fmtError("Channel has been closed")
		}
	case <-time.After(timeout):
		err = fmtError("Timeout occurred waiting for receiving a message on a channel")
	}
	return
}

// @ trusted
// @ requires noPerm < p
// @ preserves acc(dc.Mem(), p) && dc.getState() == AgentSecretCreatedAndSigned
// @ ensures  err == nil ==> ResponseChanInv!<dc, _!>(payload)
// @ ensures  err != nil ==> err.ErrorMem()
func (dc *dataChannel) tryReceiveResponse(timeout time.Duration /*@, ghost p perm @*/) (payload ResponseChanPayload, err error) {
	var ok bool
	select {
	case payload, ok = <-dc.hs.responseChan:
		if !ok {
			err = fmtError("Channel has been closed")
		}
	case <-time.After(timeout):
		err = fmtError("Timeout occurred waiting for receiving a message on a channel")
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
// @ ensures  err == nil ==> ResponseChanInv!<dc, _!>(payload)
// @ ensures  err != nil ==> err.ErrorMem()
func (dc *dataChannel) tryReceiveResponseAlt(responseChan chan ResponseChanPayload, timeout time.Duration) (payload ResponseChanPayload, err error) {
	var ok bool
	select {
	case payload, ok = <-responseChan:
		if !ok {
			err = fmtError("Channel has been closed")
		}
	case <-time.After(timeout):
		err = fmtError("Timeout occurred waiting for receiving a message on a channel")
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
ensures  err != nil ==> err.ErrorMem()
func (dc *dataChannel) tryReceiveMessageReceptionStatusModel(timeout time.Duration) (res MessageReceptionPayload, err error) {
	if nonDeterministicChoice() {
		unfold dc.RecvRoutineMem()
		fold PredTrue!<!>()
		var ok bool
		res, ok = <-dc.hs.startReceivingChan
		fold dc.RecvRoutineMem()
		if !ok {
			err = fmtError("Channel has been closed")
			return
		}
	} else {
		err = fmtError("Timeout occurred waiting for receiving a message on a channel")
	}
	return
}

// this models `tryReceiveResponse` as Gobra does not yet support the `select` statement
// we use this function to validate the spec of `tryReceiveResponse`
ghost
requires noPerm < p
preserves acc(dc.Mem(), p) && dc.getState() == AgentSecretCreatedAndSigned
ensures  err == nil ==> ResponseChanInv!<dc, _!>(payload)
ensures  err != nil ==> err.ErrorMem()
func (dc *dataChannel) tryReceiveResponseModel(timeout time.Duration, ghost p perm) (payload ResponseChanPayload, err error) {
	if nonDeterministicChoice() {
		unfold acc(dc.Mem(), p)
		unfold acc(dc.MemInternal(dc.dataChannelState), p)
		fold PredTrue!<!>()
		var ok bool
		payload, ok = <-dc.hs.responseChan
		fold acc(dc.MemInternal(dc.dataChannelState), p)
		fold acc(dc.Mem(), p)
		if !ok {
			err = fmtError("Channel has been closed")
			return
		}
	} else {
		err = fmtError("Timeout occurred waiting for receiving a message on a channel")
	}
	return
}

ghost
requires noPerm < p
preserves acc(responseChan.RecvChannel(), p)
preserves responseChan.RecvGivenPerm() == PredTrue!<!>
preserves responseChan.RecvGotPerm() == ResponseChanInv!<dc, _!>
ensures  err == nil ==> ResponseChanInv!<dc, _!>(payload)
ensures  err != nil ==> err.ErrorMem()
func (dc *dataChannel) tryReceiveResponseModelAlt(responseChan chan ResponseChanPayload, timeout time.Duration, ghost p perm) (payload ResponseChanPayload, err error) {
	if nonDeterministicChoice() {
		fold PredTrue!<!>()
		var ok bool
		payload, ok = <-responseChan
		if !ok {
			err = fmtError("Channel has been closed")
			return
		}
	} else {
		err = fmtError("Timeout occurred waiting for receiving a message on a channel")
	}
	return
}
@*/

/*@
// TODO remove (used to  justify magic wand for `processStreamDataMessage`)
trusted
requires pl.token(t) && iospec.e_InFact(t, rid)
ensures   ok ==> msg.Mem() // && by.gamma(term) == abs.Abs(packet)
ensures   ok ==> pl.token(t1) && t1 == old(iospec.get_e_InFact_placeDst(t, rid)) && term == old(iospec.get_e_InFact_r1(t, rid))
ensures  !ok ==> t1 == t && pl.token(t) && iospec.e_InFact(t, rid) && iospec.get_e_InFact_placeDst(t, rid) == old(iospec.get_e_InFact_placeDst(t, rid)) && iospec.get_e_InFact_r1(t, rid) == old(iospec.get_e_InFact_r1(t, rid))
func Receive(streamDataMessage *mgsContracts.AgentMessage, ghost t pl.Place, ghost rid tm.Term) (msg *mgsContracts.AgentMessage, ok bool, ghost term tm.Term, ghost t1 pl.Place) {
	msg = streamDataMessage
	return
}

// TODO remove (used to  justify magic wand for `processStreamDataMessage`)
func ReceiveWand(streamDataMessage *mgsContracts.AgentMessage, ghost t pl.Place, ghost rid tm.Term) (msg *mgsContracts.AgentMessage, ok bool, ghost term tm.Term, ghost t1 pl.Place) {
	package (pl.token(t) && iospec.e_InFact(t, rid)) --* (ok ==> msg.Mem() && pl.token(t1) && t1 == old[#lhs](iospec.get_e_InFact_placeDst(t, rid)) && term == old[#lhs](iospec.get_e_InFact_r1(t, rid))) {
		msg, ok, term, t1 = Receive(streamDataMessage, t, rid)
		assert ok ==> msg.Mem()
	}
}
@*/

// processStreamDataMessage gets called for all messages of type OutputStreamDataMessage
// @ requires log != nil
// @ requires datastream.QuantifiedStreamDataHandlerSpecWand(streamDataMessage)
// @ preserves acc(log.Mem(), _) && dc.RecvRoutineMem()
// @ ensures err == nil ==> streamDataMessage.Mem()
// @ ensures err != nil ==> err.ErrorMem()
func (dc *dataChannel) processStreamDataMessage(log logger.T, streamDataMessage *mgsContracts.AgentMessage) (err error) {

	payload, err := dc.tryReceiveMessageReceptionStatus(channelStatusTimeout)
	if err != nil {
		logInfo(log, "Timeout while receiving channel status")
		return err
	}

	//@ unfold StartReceivingChanInv!<dc, _!>(payload)
	switch payload.status {
	case ReceiveHandshakeResponeEncryptionEnabled:
		//@ unfold dc.MemTransfer(HandshakeRequestSent, true)
		//@ t0 := dc.getToken()
		//@ rid := dc.getRid()
		//@ s0 := dc.getAbsState()
		//@ unfold iospec.P_Agent(t0, rid, s0)
		//@ unfold iospec.phiRF_Agent_16(t0, rid, s0)
		//@ t1 := iospec.get_e_InFact_placeDst(t0, rid)
		//@ receivedMsgT := iospec.get_e_InFact_r1(t0, rid)
		//@ s1 := s0 union mset[ft.Fact]{ ft.InFact_Agent(rid, receivedMsgT) }
		//@ unfold datastream.QuantifiedStreamDataHandlerSpecWand(streamDataMessage)
		//@ unfold datastream.StreamDataHandlerSpecWand(t0, rid, streamDataMessage)
		//@ apply (pl.token(t0) && iospec.e_InFact(t0, rid)) --* (streamDataMessage.Mem() && by.gamma(old[#lhs](iospec.get_e_InFact_r1(t0, rid))) == streamDataMessage.Abs() && pl.token(old[#lhs](iospec.get_e_InFact_placeDst(t0, rid))))
		//@ unfold dc.IoSpecMemMain()
		//@ unfold dc.IoSpecMemPartial()
		//@ dc.setToken(t1)
		//@ dc.setAbsState(s1)
		//@ dc.setInFactT(receivedMsgT)
		//@ fold dc.IoSpecMemPartial()
		//@ fold dc.IoSpecMemMain()
		//@ assert by.gamma(receivedMsgT) == streamDataMessage.Abs()
		//@ fold dc.MemTransfer(HandshakeRequestSent, true)
		payloadType := /*@ unfolding streamDataMessage.Mem() in @*/ streamDataMessage.PayloadType
		switch mgsContracts.PayloadType(payloadType) {
		case mgsContracts.HandshakeResponse:
			{
				// PayloadType is HandshakeResponse so we call our own handler instead of the plugin handler
				if err = dc.handleHandshakeResponse(log, streamDataMessage, true); err != nil {
					return fmtErrorf("processing of HandshakeResponse message failed, %v", err /*@, perm(1/1) @*/)
				}
			}
		default:
			return fmtError("received message with unexpected payload type")
		}
		//@ assert streamDataMessage.Mem()
	case ReceiveHandshakeResponeEncryptionDisabled:
		// since we assume that encryption is enabled for proving refinement, we can derive here
		// a contradiction, i.e., this case corresponds to dead code if encryption is enabled:
		//@ assert false
		payloadType := /*@ unfolding streamDataMessage.Mem() in @*/ streamDataMessage.PayloadType
		switch mgsContracts.PayloadType(payloadType) {
		case mgsContracts.HandshakeResponse:
			{
				// PayloadType is HandshakeResponse so we call our own handler instead of the plugin handler
				if err = dc.handleHandshakeResponse(log, streamDataMessage, false); err != nil {
					return fmtErrorf("processing of HandshakeResponse message failed, %v", err /*@, perm(1/1) @*/)
				}
			}
		default:
			return fmtError("received message with unexpected payload type")
		}
	case ReceiveOtherResponse:
		//@ unfold dc.MemRecv()

		// ----- start remote receive I/O operation -----
		//@ dc.ioLock.Lock()
		//@ unfold IoLockInv!<dc, dc.dataStream.GetInstanceId(), dc.dataStream.GetClientId(), dc.agentLTKeyARN!>()
		
		//@ t0 := dc.getToken()
		//@ rid := dc.getRid()
		//@ s0 := dc.getAbsState()
		//@ unfold iospec.P_Agent(t0, rid, s0)
		//@ unfold iospec.phiRF_Agent_16(t0, rid, s0)
		//@ t1 := iospec.get_e_InFact_placeDst(t0, rid)
		//@ receivedMsgT := iospec.get_e_InFact_r1(t0, rid)
		//@ s1 := s0 union mset[ft.Fact]{ ft.InFact_Agent(rid, receivedMsgT) }
		//@ unfold datastream.QuantifiedStreamDataHandlerSpecWand(streamDataMessage)
		//@ unfold datastream.StreamDataHandlerSpecWand(t0, rid, streamDataMessage)
		//@ apply (pl.token(t0) && iospec.e_InFact(t0, rid)) --* (streamDataMessage.Mem() && by.gamma(old[#lhs](iospec.get_e_InFact_r1(t0, rid))) == streamDataMessage.Abs() && pl.token(old[#lhs](iospec.get_e_InFact_placeDst(t0, rid))))

		//@ unfold dc.IoSpecMemMain()
		//@ dc.setToken(t1)
		//@ dc.setAbsState(s1)
		//@ dc.setRemoteInFactT(receivedMsgT)
		//@ dc.ioLockDidRemoteReceive = true
		//@ fold dc.IoSpecMemMain()
		
		//@ fold IoLockInv!<dc, dc.dataStream.GetInstanceId(), dc.dataStream.GetClientId(), dc.agentLTKeyARN!>()
		//@ dc.ioLock.Unlock()
		// ----- end remote receive I/O operation -----

		//@ unfold streamDataMessage.Mem()
		if dc.encryptionEnabled && mgsContracts.PayloadType(streamDataMessage.PayloadType) == mgsContracts.Output {
			plaintext, err := dc.blockCipher.DecryptWithAESGCM(streamDataMessage.Payload /*@, perm(1/4) @*/)
			if err != nil {
				// send a message to the channel to prepare for next message reception:
				//@ fold dc.MemRecv()
				dc.resendReceiveOtherResponse()
				err = fmtErrorfInt64Err("Error decrypting stream data message sequence %d, err: %v", streamDataMessage.SequenceNumber, err /*@, perm(1/1) @*/)
				//@ fold streamDataMessage.Mem()
				return err
			}
			streamDataMessage.Payload = plaintext
		} else {
			assume false // TODO what should we do here?
		}
		//@ plaintextB := abs.Abs(streamDataMessage.Payload)
		//@ fold streamDataMessage.Mem()

		// Ignore stream data message if handshake is neither skipped nor completed
		if !dc.hs.skipped && !dc.hs.complete {
			// this case should provably not occur as status `ReceiveOtherResponse`
			// is supposed to be sent on the `startReceivingChan` channel AFTER the
			// handshake has completed.
			// While this branch existed in the original implementation, we can actually
			// prove that this branch cannot exist:
			// @ assert false
		}

		// ----- start internal I/O operation -----
		//@ dc.ioLock.Lock()
		//@ unfold IoLockInv!<dc, dc.dataStream.GetInstanceId(), dc.dataStream.GetClientId(), dc.agentLTKeyARN!>()
		//@ t1 = dc.getToken()
		//@ s1 = dc.getAbsState()
		//@ rid, AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, xT, SigX := dc.getRid(), dc.getAgentIdT(), dc.getKMSIdT(), dc.getClientIdT(), dc.getReaderIdT(), tm.pubTerm(pub.pub_msg(dc.agentLTKeyARN)), dc.getLogLTPkT(), dc.getAgentShareT(), dc.getAgentShareSignatureT()
		//@ sharedSecretT := dc.getSharedSecretT()
		//@ clientLtKeyIdT := dc.getClientLtKeyIdT()
		//@ clientSecretT := dc.getClientShareT()
		//@ sigYT := dc.getClientShareSignatureT()
		//@ sigSessionKeysT := dc.getSigSessionKeysT()
		// temporarily unfolding the block cipher's memory to learn the relation between the decryption term and its byte representation:
		//@ assert unfolding acc(dc.blockCipher.Mem(), _) in dc.blockCipher.GetDecKeyB() == by.gamma(dc.blockCipher.GetDecKeyT())
		//@ payloadT := pattern.patternRequirementTransportMessage(rid, AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, xT, SigX, clientLtKeyIdT, tm.exp(tm.pubTerm(pub.const_g_pub()), clientSecretT), sigYT, sigSessionKeysT, by.oneTerm(plaintextB), receivedMsgT, t1, s1)
		//@ outMsgT := tm.pair(tm.pubTerm(pub.const_Message_pub()), payloadT)
		// obtain permission to send the ciphertext containing `inputData`:
		/*@
		l := mset[ft.Fact] {
			ft.St_Agent_10(rid, AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, xT, SigX, clientLtKeyIdT, tm.exp(tm.pubTerm(pub.const_g_pub()), clientSecretT), sigYT, sigSessionKeysT),
			ft.InFact_Agent(rid, tm.pair(tm.pubTerm(pub.const_Message_pub()), tm.senc(payloadT, tm.kdf2(sharedSecretT)))),
		}
		a := mset[cl.Claim] {
			cl.AgentRecvLoop(rid, AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, xT, clientLtKeyIdT, tm.exp(tm.pubTerm(pub.const_g_pub()), clientSecretT)),
		}
		r := mset[ft.Fact] {
	    	ft.St_Agent_10(rid, AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, xT, SigX, clientLtKeyIdT, tm.exp(tm.pubTerm(pub.const_g_pub()), clientSecretT), sigYT, sigSessionKeysT),
			ft.OutFact_Agent(rid, tm.pair(tm.pubTerm(pub.const_Message_pub()), payloadT)),
		}
		@*/
		//@ unfold iospec.P_Agent(t1, rid, s1)
		//@ unfold iospec.phiR_Agent_10(t1, rid, s1)
		//@ t2 := iospec.internBIO_e_Agent_ReceiveMessages(t1, rid, AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, xT, SigX, clientLtKeyIdT, tm.exp(tm.pubTerm(pub.const_g_pub()), clientSecretT), sigYT, sigSessionKeysT, payloadT, l, a, r)
		//@ s2 := ft.U(l, r, s1)

		//@ unfold dc.IoSpecMemMain()
		//@ dc.setToken(t2)
		//@ dc.setAbsState(s2)
		//@ dc.ioLockDidRemoteReceive = false
		//@ dc.setLocalOutFactT(outMsgT)
		//@ dc.ioLockCanLocalSend = true
		//@ fold dc.IoSpecMemMain()

		//@ fold IoLockInv!<dc, dc.dataStream.GetInstanceId(), dc.dataStream.GetClientId(), dc.agentLTKeyARN!>()
		//@ dc.ioLock.Unlock()
		// ----- end internal I/O operation -----

		// ----- start internal send I/O operation -----
		//@ dc.ioLock.Lock()
		//@ unfold IoLockInv!<dc, dc.dataStream.GetInstanceId(), dc.dataStream.GetClientId(), dc.agentLTKeyARN!>()

		//@ t2 = dc.getToken()
		//@ s2 = dc.getAbsState()
		//@ unfold iospec.P_Agent(t2, rid, s2)
		//@ unfold iospec.phiRG_Agent_13(t2, rid, s2)
		//@ t3 := iospec.get_e_OutFact_placeDst(t2, rid, outMsgT)
		//@ s3 := s2 setminus mset[ft.Fact]{ ft.OutFact_Agent(rid, outMsgT) }

		//@ fold dc.MemRecv()
		//@ unfold dc.RecvRoutineMem()
		err = dc.inputStreamMessageHandler(log, streamDataMessage /*@, t2, rid, outMsgT @*/) /*@ as StreamDataHandlerSpec{dc.msgHandlerCtx} @*/
		//@ fold dc.RecvRoutineMem()

		if err != nil {
			//@ unfold acc(dc.MemRecv(), 1/2)
			//@ fold iospec.phiRG_Agent_13(t2, rid, s2)
			//@ fold iospec.P_Agent(t2, rid, s2)
			//@ fold IoLockInv!<dc, dc.dataStream.GetInstanceId(), dc.dataStream.GetClientId(), dc.agentLTKeyARN!>()
			//@ dc.ioLock.Unlock()
			//@ fold acc(dc.MemRecv(), 1/2)
			dc.resendReceiveOtherResponse()
			return err
		}

		//@ unfold dc.MemRecv()
		//@ unfold dc.IoSpecMemMain()
		//@ dc.setToken(t3)
		//@ dc.setAbsState(s3)
		//@ dc.ioLockCanLocalSend = false
		//@ fold dc.IoSpecMemMain()

		//@ fold IoLockInv!<dc, dc.dataStream.GetInstanceId(), dc.dataStream.GetClientId(), dc.agentLTKeyARN!>()
		//@ dc.ioLock.Unlock()
		// ----- end internal send I/O operation -----

		//@ fold dc.MemRecv()
		dc.resendReceiveOtherResponse()
	}

	return nil
}

// requires acc(dc.Mem(), 1/2) && dc.getState() == AgentSecretCreatedAndSigned && unfolding acc(dc.Mem(), _) in unfolding acc(dc.MemInternal(AgentSecretCreatedAndSigned), _) in dc.hs.complete
// @ requires dc.MemRecv() && unfolding acc(dc.MemRecv(), _) in dc.dataChannelState == IODistributed && dc.hs.complete
// @ preserves dc.RecvRoutineMem()
func (dc *dataChannel) resendReceiveOtherResponse() {
	//@ unfold acc(dc.MemRecv(), 1/2)
	//@ unfold dc.RecvRoutineMem()
	//@ fold acc(dc.MemRecv(), 1/2)
	payload := MessageReceptionPayload {
		status: ReceiveOtherResponse,
	}
	//@ fold StartReceivingChanInv!<dc, _!>(payload)
	dc.hs.startReceivingChan <- payload
	//@ fold dc.RecvRoutineMem()
}

// @ trusted
// @ pure
// @ requires acc(bytes.SliceMem(a), _) && acc(bytes.SliceMem(b), _)
// @ ensures res == (abs.Abs(a) == abs.Abs(b))
func equal(a, b []byte) (res bool) {
	return bytes.Equal(a, b)
}

// @ trusted
// @ requires noPerm < p
// @ preserves acc(bytes.SliceMem(input), p)
// @ ensures bytes.SliceMem(res) && abs.Abs(res) == by.hashB(abs.Abs(input))
func computeSHA384(input []byte /*@, ghost p perm @*/) (res []byte) {
	hash := sha512.New384()
	hash.Write(input)
	return hash.Sum(nil)
}

// @ trusted
// @ requires noPerm < p
// @ preserves acc(bytes.SliceMem(input), p)
// @ ensures err == nil ==> (bytes.SliceMem(res) &&
// @ 	(isKdf1 ? abs.Abs(res) == by.kdf1B(abs.Abs(input)) : abs.Abs(res) == by.kdf2B(abs.Abs(input))))
// @ ensures err != nil ==> err.ErrorMem()
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
// @ requires log != nil && dc.MemTransfer(HandshakeRequestSent, encryptionEnabled)
// @ requires streamDataMessage.Mem()
// @ requires unfolding streamDataMessage.Mem() in mgsContracts.PayloadType(streamDataMessage.PayloadType) == mgsContracts.HandshakeResponse
// @ requires unfolding dc.MemTransfer(HandshakeRequestSent, encryptionEnabled) in by.gamma(dc.getInFactT()) == streamDataMessage.Abs() && ft.InFact_Agent(dc.getRid(), dc.getInFactT()) in dc.getAbsState()
// @ preserves acc(log.Mem(), _) && dc.RecvRoutineMem()
// @ ensures  streamDataMessage.Mem()
// @ ensures  err != nil ==> err.ErrorMem()
func (dc *dataChannel) handleHandshakeResponse(log logger.T, streamDataMessage *mgsContracts.AgentMessage, encryptionEnabled bool) (err error) {
	logDebug(log, "Received Handshake Response.")
	//@ unfold streamDataMessage.Mem()
	handshakeResponse, err := unmarshalHandshakeResponse(streamDataMessage.Payload /*@, perm(1/2) @*/)
	//@ fold streamDataMessage.Mem()
	if err != nil {
		return fmtErrorf("Unmarshalling of HandshakeResponse message failed, %s", err /*@, perm(1/1) @*/)
	}

	//@ unfold acc(handshakeResponse.Mem(), 1/2)
	actions := handshakeResponse.ProcessedClientActions
	containsSecureSessionAction := false
	state := HandshakeRequestSent
	//@ fold acc(handshakeResponse.Mem(), 1/2)

	//@ invariant err == nil
	//@ invariant handshakeResponse.Mem()
	//@ invariant unfolding acc(handshakeResponse.Mem(), 1/2) in handshakeResponse.ProcessedClientActions === actions
	//@ invariant 0 <= i &&  i <= len(actions)
	//@ invariant dc.MemTransfer(state, encryptionEnabled)
	//@ invariant err == nil && !containsSecureSessionAction ==> state == HandshakeRequestSent
	//@ invariant err == nil && containsSecureSessionAction ==> state == BlockCipherReady
	//@ invariant err != nil ==> err.ErrorMem()
	//@ invariant acc(log.Mem(), _)
	//@ invariant acc(streamDataMessage.Mem(), 1/2)
	//@ invariant unfolding acc(streamDataMessage.Mem(), 1/2) in
	//@		mgsContracts.PayloadType(streamDataMessage.PayloadType) == mgsContracts.HandshakeResponse &&
	//@ 	abs.Abs(streamDataMessage.Payload) == handshakeResponse.Abs()
	//@ invariant i <= 1 ==> !containsSecureSessionAction
	//@ invariant !containsSecureSessionAction ==> unfolding dc.MemTransfer(state, encryptionEnabled) in by.gamma(dc.getInFactT()) == streamDataMessage.Abs() && ft.InFact_Agent(dc.getRid(), dc.getInFactT()) in dc.getAbsState()
	for i := 0; i < len(actions); i++ {
		//@ unfold acc(handshakeResponse.Mem(), 1/2)
		//@ unfold acc(actions[i].Mem(), 1/2)
		action := actions[i]
		if action.ActionStatus != mgsContracts.Success {
			err = fmtErrorfActionTypeActionStatusActionError("%s failed on client with status %v error: %s",
				action.ActionType, action.ActionStatus, action.Error)
			//@ fold acc(actions[i].Mem(), 1/2)
			//@ fold acc(handshakeResponse.Mem(), 1/2)
		} else {
			switch action.ActionType {
			case mgsContracts.SecureSession:
				//@ fold acc(actions[i].Mem(), 1/2)
				if i != 1 || len(actions) < 2 || /*@ unfolding acc(actions[0].Mem(), 1/2) in @*/ actions[0].ActionType != mgsContracts.SessionType {
					err = fmtError("unexpected actions in HandshakeResponse")
					//@ fold acc(handshakeResponse.Mem(), 1/2)
				} else {
					containsSecureSessionAction = true
					if !encryptionEnabled {
						err = fmtError("unexpected action type 'SecureSession' because encryption is disabled")
						//@ fold acc(handshakeResponse.Mem(), 1/2)
					} else {
						state, err = dc.processSecureSessionResponse(log, &actions[i])
						//@ fold acc(handshakeResponse.Mem(), 1/2)
					}
				}
			// case mgsContracts.KMSEncryption:
			// 	 err = dc.finalizeKMSEncryption(log, action.ActionResult)
			case mgsContracts.SessionType:
				//@ fold acc(actions[i].Mem(), 1/2)
				//@ fold acc(handshakeResponse.Mem(), 1/2)
			default:
				//@ fold acc(actions[i].Mem(), 1/2)
				//@ fold acc(handshakeResponse.Mem(), 1/2)
				logWarnfActionType(log, "Unknown handshake client action found, %s", action.ActionType)
			}
		}
		if err != nil {
			break
		}
	}

	if err == nil && encryptionEnabled && !containsSecureSessionAction {
		err = fmtError("No 'SecureSession' action found despite encryption being enabled")
	}
	if err != nil {
		logError(log, err /*@, perm(1/1) @*/)
		// Cancel the session because handshake FAILED
		//@ unfold dc.MemTransfer(state, encryptionEnabled)
		dc.dataStream.CancelSession( /*@ perm(1/2) @*/ )
		// Set handshake error. Initiate handshake waits on handshake.responseChan and will return this error when channel returns.
		dc.hs.error = err
		state = Erroneous
		//@ fold dc.MemTransfer(state, encryptionEnabled)
	} else {
		//@ unfold dc.MemTransfer(state, encryptionEnabled)
		// TODO: one could strengthen the invariants to prove that this
		// assignment is superfluous
		dc.hs.error = nil
		//@ fold dc.MemTransfer(state, encryptionEnabled)
	}

	//@ unfold dc.MemTransfer(state, encryptionEnabled)
	//@ unfold acc(handshakeResponse.Mem(), 1/2)
	dc.hs.clientVersion = handshakeResponse.ClientVersion
	logInfofString(log, "Client side session manager plugin version is: %s", handshakeResponse.ClientVersion)
	//@ fold acc(handshakeResponse.Mem(), 1/2)
	//@ fold dc.MemTransfer(state, encryptionEnabled)
	payload := ResponseChanPayload{ encryptionEnabled, state }
	//@ fold ResponseChanInv!<dc, _!>(payload)
	//@ unfold dc.RecvRoutineMem()
	dc.hs.responseChan <- payload
	//@ fold dc.RecvRoutineMem()
	return nil
}

// @ trusted
// @ requires noPerm < p
// @ preserves acc(bytes.SliceMem(payload), p)
// @ ensures  handshakeResponse.Mem()
// @ ensures  err == nil && abs.Abs(payload) == handshakeResponse.Abs()
// @ ensures  err != nil ==> err.ErrorMem()
func unmarshalHandshakeResponse(payload []byte /*@, p perm @*/) (handshakeResponse *mgsContracts.HandshakeResponsePayload, err error) {
	handshakeResponse = &mgsContracts.HandshakeResponsePayload{}
	//@ fold handshakeResponse.Mem()
	err = json.Unmarshal(payload, handshakeResponse /*@, p/2 @*/)
	return
}

// @ trusted
// @ requires noPerm < p
// @ preserves acc(bytes.SliceMem(payload), p)
// @ ensures  secureSessionResponse.Mem()
// @ ensures  err == nil && abs.Abs(payload) == secureSessionResponse.Abs()
// @ ensures  err != nil ==> err.ErrorMem()
func unmarshalSecureSessionResponse(payload []byte /*@, p perm @*/) (secureSessionResponse *mgsContracts.SecureSessionResponse, err error) {
	secureSessionResponse = &mgsContracts.SecureSessionResponse{}
	//@ fold secureSessionResponse.Mem()
	err = json.Unmarshal(payload, secureSessionResponse /*@, p/2 @*/)
	return
}

// @ requires log != nil
// @ requires dc.MemTransfer(HandshakeRequestSent, true) && acc(action.Mem(), 1/4) && action.IsSuccessfulSecureSession()
// @ requires unfolding dc.MemTransfer(HandshakeRequestSent, true) in by.gamma(dc.getInFactT()) == by.pairB(by.gamma(mgsContracts.payloadTypeTerm(mgsContracts.HandshakeResponse)), action.Abs()) && ft.InFact_Agent(dc.getRid(), dc.getInFactT()) in dc.getAbsState()
// @ preserves acc(log.Mem(), _) 
// @ ensures  dc.MemTransfer(state, true) && acc(action.Mem(), 1/4)
// @ ensures  err == nil ==> state == BlockCipherReady
// @ ensures  err != nil ==> err.ErrorMem()
func (dc *dataChannel) processSecureSessionResponse(log logger.T, action *mgsContracts.ProcessedClientAction) (state DataChannelState, err error) {
	state, err = dc.verifySecureSessionResponse(log, action)
	if err != nil {
		return
	}
	state, err = dc.completeSecureSessionResponseProcessing(log)
}

// @ requires log != nil
// @ requires dc.MemTransfer(HandshakeRequestSent, true) && acc(action.Mem(), 1/8) && action.IsSuccessfulSecureSession()
// @ requires unfolding dc.MemTransfer(HandshakeRequestSent, true) in by.gamma(dc.getInFactT()) == by.pairB(by.gamma(mgsContracts.payloadTypeTerm(mgsContracts.HandshakeResponse)), action.Abs()) && ft.InFact_Agent(dc.getRid(), dc.getInFactT()) in dc.getAbsState()
// @ preserves acc(log.Mem(), _)
// @ ensures  dc.MemTransfer(state, true) && acc(action.Mem(), 1/8)
// @ ensures  err == nil ==> state == HandshakeResponseVerified
// @ ensures  err != nil ==> err.ErrorMem()
func (dc *dataChannel) verifySecureSessionResponse(log logger.T, action *mgsContracts.ProcessedClientAction) (state DataChannelState, err error) {
	state = HandshakeRequestSent
	//@ unfold acc(action.Mem(), 1/8)
	resp, err := unmarshalSecureSessionResponse(action.ActionResult /*@, perm(1/16) @*/)
	//@ fold acc(action.Mem(), 1/8)
	if err != nil {
		err = fmtErrorf("failed to unmarshal action to SecureSessionResponse: %v", err /*@, perm(1/1) @*/)
		return
	}
	respAbs := resp.Abs()

	// decode the client share
	//@ unfold resp.Mem()
	//@ unfold dc.MemTransfer(state, true)
	sharedSecret, err /*@, clientSecretB @*/ := unmarshalAndCheckClientShare(resp.ClientShare, dc.state.agentSecret /*@, perm(1/2) @*/)
	if err != nil {
		//@ fold dc.MemTransfer(state, true)
		logError(log, err /*@, perm(1/1) @*/)
		return
	}

	dc.state.sharedSecret = sharedSecret

	// hash the shared secret to obtain the session identifier
	dc.state.sessionID = computeSHA384(sharedSecret /*@, 1/2 @*/)
	logDebugfString(log, "agent computed session ID: %v", base64.StdEncoding.EncodeToString(dc.state.sessionID /*@, perm(1/2) @*/))

	// decode the session ID
	sessionIDBytes, err := base64.StdEncoding.DecodeString(resp.SessionID)
	if err != nil {
		//@ fold dc.MemTransfer(state, true)
		err = fmtErrorf("failed to decode server session id: %v", err /*@, perm(1/1) @*/)
		logError(log, err /*@, perm(1/1) @*/)
		return
	}

	if !equal(dc.state.sessionID, sessionIDBytes) {
		err = fmtErrorfBytes2("session ID mismatch: session ID %s does not match client session ID %s", sessionIDBytes, dc.state.sessionID /*@, perm(1/1) @*/)
		//@ fold dc.MemTransfer(state, true)
		logError(log, err /*@, perm(1/1) @*/)
		return
	}

	//@ receivedMsgT := dc.getInFactT()
	//@ xT := dc.getAgentShareT()
	//@ sigYB := by.msgB(resp.Signature)
	//@ clientLtKeyIdB := by.msgB(resp.ClientLTKeyARN)
	//@ t0 := dc.getToken()
	//@ rid, AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, xT, SigX := dc.getRid(), dc.getAgentIdT(), dc.getKMSIdT(), dc.getClientIdT(), dc.getReaderIdT(), tm.pubTerm(pub.pub_msg(dc.agentLTKeyARN)), dc.getLogLTPkT(), dc.getAgentShareT(), dc.getAgentShareSignatureT()
	//@ s0 := dc.getAbsState()

	// retrieve the term representation of `clientSecretT`, `sigYT`, and `clientLtKeyIdT` by applying our term-uniqueness assumption of the received message:
	clientSecretT, sigYT, clientLtKeyIdT := pattern.patternRequirementSecSessResp(rid, AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, xT, SigX, by.oneTerm(clientSecretB), by.oneTerm(sigYB), by.oneTerm(clientLtKeyIdB), receivedMsgT, t0, s0)
	//@ sharedSecretT := tm.exp(tm.exp(tm.pubTerm(pub.const_g_pub()), clientSecretT), xT)
	//@ assert abs.Abs(sharedSecret) == by.gamma(sharedSecretT)

	/*@
		l := mset[ft.Fact] {
			ft.St_Agent_3(rid, AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, xT, SigX),
			ft.InFact_Agent(rid, tm.pair(tm.pubTerm(pub.const_SecureSessionResponse_pub()), tm.pair(tm.exp(tm.pubTerm(pub.const_g_pub()), clientSecretT), tm.pair(sigYT, tm.pair(clientLtKeyIdT, tm.hash(tm.exp(tm.exp(tm.pubTerm(pub.const_g_pub()), clientSecretT), xT))))))),
		}
		a := mset[cl.Claim] {
			cl.AgentSecureSessionResponse(ClientId, AgentId, tm.exp(tm.pubTerm(pub.const_g_pub()), clientSecretT), sigYT, clientLtKeyIdT, tm.hash(tm.exp(tm.exp(tm.pubTerm(pub.const_g_pub()), clientSecretT), xT))),
		}
		r := mset[ft.Fact] {
	    	ft.St_Agent_4(rid, AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, xT, SigX, clientLtKeyIdT, tm.exp(tm.pubTerm(pub.const_g_pub()), clientSecretT), sigYT),
		}
	@*/
	//@ unfold iospec.P_Agent(t0, rid, s0)
	//@ unfold iospec.phiR_Agent_3(t0, rid, s0)
	//@ t1 := iospec.internBIO_e_Agent_RecvSecureSessionResponse(t0, rid, AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, xT, SigX, clientSecretT, sigYT, clientLtKeyIdT, l, a, r)
	//@ s1 := ft.U(l, r, s0)
	//@ unfold dc.IoSpecMemMain()
	//@ unfold dc.IoSpecMemPartial()
	//@ dc.setToken(t1)
	//@ dc.setAbsState(s1)
	//@ dc.setSharedSecretT(sharedSecretT)
	//@ dc.setClientLtKeyIdT(clientLtKeyIdT)
	//@ dc.setClientShareT(clientSecretT)
	//@ dc.setClientShareSignatureT(sigYT)
	//@ fold dc.IoSpecMemPartial()
	//@ fold dc.IoSpecMemMain()
	state = HandshakeResponseReceived

	// verify client signature
	sig, err := base64.StdEncoding.DecodeString(resp.Signature)
	if err != nil {
		//@ fold dc.MemTransfer(state, true)
		err = fmtErrorf("failed to decode signature: %v", err /*@, perm(1/1) @*/)
		return
	}

	agentId := dc.dataStream.GetInstanceId()
	//@ fold dc.MemTransfer(state, true)
	
	clientSignPayloadBytes, err := getVerifyPayloadBytes(resp.ClientShare, agentId)
	if err != nil {
		err = fmtErrorf("failed to encode client sign payload: %v", err /*@, perm(1/1) @*/)
		logError(log, err /*@, perm(1/1) @*/)
		return
	}

	//@ unfold dc.MemTransfer(state, true)

	/*@
		verifyReqT := ut.tuple5(tm.pubTerm(pub.const_VerifyRequest_pub()), ClientId, clientLtKeyIdT, tm.pair(tm.exp(tm.pubTerm(pub.const_g_pub()), clientSecretT), AgentId), sigYT)
		l2 := mset[ft.Fact] {
			ft.St_Agent_4(rid, AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, xT, SigX, clientLtKeyIdT, tm.exp(tm.pubTerm(pub.const_g_pub()), clientSecretT), sigYT),
		}
		a2 := mset[cl.Claim] {}
		r2 := mset[ft.Fact] {
	    	ft.St_Agent_5(rid, AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, xT, SigX, clientLtKeyIdT, tm.exp(tm.pubTerm(pub.const_g_pub()), clientSecretT), sigYT),
			ft.Out_KMS_Agent(rid, AgentId, KMSId, rid, verifyReqT),
		}
	@*/
	//@ unfold iospec.P_Agent(t1, rid, s1)
	//@ unfold iospec.phiR_Agent_4(t1, rid, s1)
	//@ t2 := iospec.internBIO_e_Agent_SendVerifyRequest(t1, rid, AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, xT, SigX, clientLtKeyIdT, tm.exp(tm.pubTerm(pub.const_g_pub()), clientSecretT), sigYT, l2, a2, r2)
	//@ s2 := ft.U(l2, r2, s1)

	// unfold phiRG_Agent_12 to obtain e_Out_KMS permission
	//@ unfold iospec.P_Agent(t2, rid, s2)
	//@ unfold iospec.phiRG_Agent_12(t2, rid, s2)
	//@ t3 := iospec.get_e_Out_KMS_placeDst(t2, rid, AgentId, KMSId, rid, verifyReqT)
	//@ s3 := s2 setminus mset[ft.Fact] { ft.Out_KMS_Agent(rid, AgentId, KMSId, rid, verifyReqT) }

	// unfold phiRF_Agent_15 to obtain e_In_KMS permission since `Verify` performs a send and receive operation
	//@ unfold iospec.P_Agent(t3, rid, s3)
	//@ unfold iospec.phiRF_Agent_15(t3, rid, s3)
	//@ t4 := iospec.get_e_In_KMS_placeDst(t3, rid)

	//@ messageT := tm.pair(tm.exp(tm.pubTerm(pub.const_g_pub()), clientSecretT), AgentId)
	ok, err := dc.state.kmsService.Verify(resp.ClientLTKeyARN, clientSignPayloadBytes, sig /*@, perm(1/2), t2, rid, AgentId, KMSId, ClientId, clientLtKeyIdT, messageT, sigYT, verifyReqT @*/)
	if !ok {
		state = Erroneous
		//@ fold dc.MemTransfer(state, true)
		err = fmtError("failed to verify signature")
		return
	}
	if err != nil {
		state = Erroneous
		//@ fold dc.MemTransfer(state, true)
		err = fmtErrorf("failed to verify signature: %v", err /*@, perm(1/1) @*/)
		return
	}

	//@ s4 := s3 union mset[ft.Fact] { ft.In_KMS_Agent(rid, KMSId, AgentId, rid, tm.pubTerm(pub.const_VerifyResponse_pub())) }
	
	/*@
		l3 := mset[ft.Fact] {
			ft.St_Agent_5(rid, AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, xT, SigX, clientLtKeyIdT, tm.exp(tm.pubTerm(pub.const_g_pub()), clientSecretT), sigYT),
			ft.In_KMS_Agent(rid, KMSId, AgentId, rid, tm.pubTerm(pub.const_VerifyResponse_pub())),
		}
		a3 := mset[cl.Claim] {
			cl.SecretX(xT),
		}
		r3 := mset[ft.Fact] {
	    	ft.St_Agent_6(rid, AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, xT, SigX, clientLtKeyIdT, tm.exp(tm.pubTerm(pub.const_g_pub()), clientSecretT), sigYT),
		}
	@*/
	//@ unfold iospec.P_Agent(t4, rid, s4)
	//@ unfold iospec.phiR_Agent_5(t4, rid, s4)
	//@ t5 := iospec.internBIO_e_Agent_RecvVerifyResponse(t4, rid, AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, xT, SigX, clientLtKeyIdT, tm.exp(tm.pubTerm(pub.const_g_pub()), clientSecretT), sigYT, l3, a3, r3)
	//@ s5 := ft.U(l3, r3, s4)
	//@ unfold dc.IoSpecMemMain()
	//@ unfold dc.IoSpecMemPartial()
	//@ dc.setToken(t5)
	//@ dc.setAbsState(s5)
	//@ fold dc.IoSpecMemPartial()
	//@ fold dc.IoSpecMemMain()
	state = HandshakeResponseVerified
	//@ fold dc.MemTransfer(state, true)
	return
}

// @ requires log != nil
// @ requires dc.MemTransfer(HandshakeResponseVerified, true)
// @ preserves acc(log.Mem(), _) 
// @ ensures  dc.MemTransfer(state, true)
// @ ensures  err == nil ==> state == BlockCipherReady
// @ ensures  err != nil ==> err.ErrorMem()
func (dc *dataChannel) completeSecureSessionResponseProcessing(log logger.T) (state DataChannelState, err error) {
	state = HandshakeResponseVerified
	//@ unfold dc.MemTransfer(state, true)
	//@ rid, AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, xT, SigX := dc.getRid(), dc.getAgentIdT(), dc.getKMSIdT(), dc.getClientIdT(), dc.getReaderIdT(), tm.pubTerm(pub.pub_msg(dc.agentLTKeyARN)), dc.getLogLTPkT(), dc.getAgentShareT(), dc.getAgentShareSignatureT()
	//@ t0 := dc.getToken()
	//@ s0 := dc.getAbsState()
	sharedSecret := dc.state.sharedSecret
	//@ sharedSecretT := dc.getSharedSecretT()
	//@ clientLtKeyIdT := dc.getClientLtKeyIdT()
	//@ clientSecretT := dc.getClientShareT()
	//@ sigYT := dc.getClientShareSignatureT()

	// use the shared secret to generate read and write keys
	dc.state.agentWriteKey, err = computeKdf(sharedSecret, true /*@, 1/2 @*/)
	if err != nil {
		//@ fold dc.MemTransfer(state, true)
		return
	}
	dc.state.agentReadKey, err = computeKdf(sharedSecret, false /*@, 1/2 @*/)
	if err != nil {
		//@ fold dc.MemTransfer(state, true)
		return
	}

	agentReadKey := dc.state.agentReadKey
	agentWriteKey := dc.state.agentWriteKey
	logDebugfBytes(log, "agent read key: %s", agentReadKey /*@, perm(1/2) @*/)
	logDebugfBytes(log, "agent write key: %s", agentWriteKey /*@, perm(1/2) @*/)
	
	sessionKeysBytes, err := getSessionKeysPayload(agentWriteKey, agentReadKey /*@, perm(1/2) @*/)
	if err != nil {
		//@ fold dc.MemTransfer(state, true)
		err = fmtErrorf("failed to encode session keys: %v", err /*@, perm(1/1) @*/)
		logError(log, err /*@, perm(1/1) @*/)
		return
	}
	//@ sessionKeysBytesT := tm.pair(tm.kdf1(sharedSecretT), tm.kdf2(sharedSecretT))
	//@ assert abs.Abs(sessionKeysBytes) == by.gamma(sessionKeysBytesT)

	encodedEncryptedSessionKeys, err := encryptAndEncode(sessionKeysBytes, dc.logLTPk /*@, perm(1/2) @*/)
	if err != nil {
		//@ fold dc.MemTransfer(state, true)
		err = fmtErrorf("failed to encrypt session keys: %v", err /*@, perm(1/1) @*/)
		return
	}
	logInfofString(log, "encrypted base-64-encoded session keys: %s", encodedEncryptedSessionKeys)
	//@ encodedEncryptedSessionKeysT := tm.aenc(sessionKeysBytesT, dc.getLogLTPkT())
	//@ assert by.msgB(encodedEncryptedSessionKeys) == by.gamma(encodedEncryptedSessionKeysT)

	// sign ciphertext containing session keys using KMS:
	signSessionKeysPayloadBytes, err := getSignSessionKeysPayloadBytes(encodedEncryptedSessionKeys, dc.dataStream.GetClientId())
	if err != nil {
		//@ fold dc.MemTransfer(state, true)
		err = fmtErrorf("failed to encode sign session keys payload: %v", err /*@, perm(1/1) @*/)
		logError(log, err /*@, perm(1/1) @*/)
		return
	}
	//@ messageT := tm.pair(encodedEncryptedSessionKeysT, dc.getClientIdT())
	//@ assert abs.Abs(signSessionKeysPayloadBytes) == by.gamma(messageT)
	//@ m := ut.tuple3(tm.pubTerm(pub.const_SignRequest_pub()), tm.pubTerm(pub.pub_msg(dc.agentLTKeyARN)), messageT)
	// unfold phiR_Agent_6 to obtain Out_KMS_Agent fact
	//@ Y := tm.exp(tm.pubTerm(pub.const_g_pub()), clientSecretT)
	//@ assert m == tm.pair(tm.pubTerm(pub.const_SignRequest_pub()), tm.pair(AgentLtKeyId, tm.pair(tm.aenc(tm.pair(tm.kdf1(tm.exp(Y, xT)), tm.kdf2(tm.exp(Y, xT))), logPk), ClientId)))
	/*@
		l := mset[ft.Fact] {
			ft.St_Agent_6(rid, AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, xT, SigX, clientLtKeyIdT, tm.exp(tm.pubTerm(pub.const_g_pub()), clientSecretT), sigYT),
		}
		a := mset[cl.Claim] {}
		r := mset[ft.Fact] {
		    ft.St_Agent_7(rid, AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, xT, SigX, clientLtKeyIdT, tm.exp(tm.pubTerm(pub.const_g_pub()), clientSecretT), sigYT),
		    ft.Out_KMS_Agent(rid, AgentId, KMSId, rid, m),
		}
	@*/
	//@ unfold iospec.P_Agent(t0, rid, s0)
	//@ unfold iospec.phiR_Agent_6(t0, rid, s0)
	//@ t1 := iospec.internBIO_e_Agent_SendSessionKeySignRequest(t0, rid, AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, xT, SigX, clientLtKeyIdT, tm.exp(tm.pubTerm(pub.const_g_pub()), clientSecretT), sigYT, l, a, r)
	//@ s1 := ft.U(l, r, s0)

	// TODO: create a wrapper for `signAndEncode` that applies the following two IO transitions to remove code redundancy
	// unfold phiRG_Agent_12 to obtain e_Out_KMS permission
	//@ unfold iospec.P_Agent(t1, rid, s1)
	//@ unfold iospec.phiRG_Agent_12(t1, rid, s1)
	//@ t2 := iospec.get_e_Out_KMS_placeDst(t1, rid, AgentId, KMSId, rid, m)
	//@ s2 := s1 setminus mset[ft.Fact] { ft.Out_KMS_Agent(rid, AgentId, KMSId, rid, m) }

	// unfold phiRF_Agent_15 to obtain e_In_KMS permission since `signAndEncode` performs a send and receive operation
	//@ unfold iospec.P_Agent(t2, rid, s2)
	//@ unfold iospec.phiRF_Agent_15(t2, rid, s2)
	//@ t3 := iospec.get_e_In_KMS_placeDst(t2, rid)

	encodedSigSessionKeys, err /*@, sigSessionKeysT @*/ := signAndEncode(dc.state.kmsService, dc.agentLTKeyARN, signSessionKeysPayloadBytes /*@, perm(1/2), t1, rid, AgentId, KMSId, messageT, m @*/)
	if err != nil {
		state = Erroneous
		//@ fold dc.MemTransfer(state, true)
		err = fmtErrorf("failed to sign session keys payload: %v", err /*@, perm(1/1) @*/)
		logError(log, err /*@, perm(1/1) @*/)
		return
	}

	//@ s3 := s2 union mset[ft.Fact] { ft.In_KMS_Agent(rid, KMSId, AgentId, rid, tm.pair(tm.pubTerm(pub.const_SignResponse_pub()), sigSessionKeysT)) }
	/*@
		l2 := mset[ft.Fact] {
			ft.St_Agent_7(rid, AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, xT, SigX, clientLtKeyIdT, tm.exp(tm.pubTerm(pub.const_g_pub()), clientSecretT), sigYT),
			ft.In_KMS_Agent(rid, KMSId, AgentId, rid, tm.pair(tm.pubTerm(pub.const_SignResponse_pub()), sigSessionKeysT)),
		}
		a2 := mset[cl.Claim] {}
		r2 := mset[ft.Fact] {
		    ft.St_Agent_8(rid, AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, xT, SigX, clientLtKeyIdT, tm.exp(tm.pubTerm(pub.const_g_pub()), clientSecretT), sigYT, sigSessionKeysT),
		}
	@*/
	//@ unfold iospec.P_Agent(t3, rid, s3)
	//@ unfold iospec.phiR_Agent_7(t3, rid, s3)
	//@ t4 := iospec.internBIO_e_Agent_RecvSessionKeySignResponse(t3, rid, AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, xT, SigX, clientLtKeyIdT, tm.exp(tm.pubTerm(pub.const_g_pub()), clientSecretT), sigYT, sigSessionKeysT, l2, a2, r2)
	//@ s4 := ft.U(l2, r2, s3)

	/*@
		l3 := mset[ft.Fact] {
			ft.St_Agent_8(rid, AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, xT, SigX, clientLtKeyIdT, tm.exp(tm.pubTerm(pub.const_g_pub()), clientSecretT), sigYT, sigSessionKeysT),
		}
		a3 := mset[cl.Claim] {
			cl.AgentSendEncryptedSessionKey(xT),
		}
		r3 := mset[ft.Fact] {
		    ft.St_Agent_9(rid, AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, xT, SigX, clientLtKeyIdT, tm.exp(tm.pubTerm(pub.const_g_pub()), clientSecretT), sigYT, sigSessionKeysT),
			ft.OutFact_Agent(rid, tm.pair(tm.pubTerm(pub.const_EncryptedSessionKey_pub()), tm.pair(tm.aenc(tm.pair(tm.kdf1(sharedSecretT), tm.kdf2(sharedSecretT)), logPk), tm.pair(sigSessionKeysT, tm.pair(AgentId, tm.pair(AgentLtKeyId, ClientId)))))),
		}
	@*/
	//@ unfold iospec.P_Agent(t4, rid, s4)
	//@ unfold iospec.phiR_Agent_8(t4, rid, s4)
	//@ t5 := iospec.internBIO_e_Agent_SendEncryptedSessionKey(t4, rid, AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, xT, SigX, clientLtKeyIdT, tm.exp(tm.pubTerm(pub.const_g_pub()), clientSecretT), sigYT, sigSessionKeysT, l3, a3, r3)
	//@ s5 := ft.U(l3, r3, s4)

	// send ciphertext containing session keys and the corresponding signature to the log server:
	encodedEncryptedSessionKeysPayloadBytes, err := getEncryptedSessionKeysPayload(encodedEncryptedSessionKeys, encodedSigSessionKeys, dc.dataStream.GetInstanceId(), dc.agentLTKeyARN, dc.dataStream.GetClientId())
	if err != nil {
		state = Erroneous
		//@ fold dc.MemTransfer(state, true)
		err = fmtErrorf("failed to encode encrypted session keys payload: %v", err /*@, perm(1/1) @*/)
		logError(log, err /*@, perm(1/1) @*/)
		return
	}
	logInfofString(log, "encrypted session keys payload that should be sent to log server: %s", encodedEncryptedSessionKeysPayloadBytes)

	//@ encryptedSessionKeysPayloadT := ut.tuple5(encodedEncryptedSessionKeysT, sigSessionKeysT, AgentId, AgentLtKeyId, ClientId)
	//@ assert by.msgB(encodedEncryptedSessionKeysPayloadBytes) == by.gamma(encryptedSessionKeysPayloadT)

	// TODO: actually send `encodedEncryptedSessionKeysPayloadBytes` to the log server!
	// use `phiRG_Agent_13` and the `OutFact_Agent` fact in s5 to obtain the corresponding send permission
	//@ assert ft.OutFact_Agent(rid, tm.pair(tm.pubTerm(pub.const_EncryptedSessionKey_pub()), encryptedSessionKeysPayloadT)) in s5

	if err = dc.blockCipher.UpdateEncryptionKeys(log, dc.state.agentReadKey, dc.state.agentWriteKey /*@, perm(1/2), tm.kdf2(sharedSecretT), tm.kdf1(sharedSecretT) @*/); err != nil {
		state = Erroneous
		//@ fold dc.MemTransfer(state, true)
		err = fmtErrorf("failed to update block cipher: %v", err /*@, perm(1/1) @*/)
		logError(log, err /*@, perm(1/1) @*/)
		return
	}

	//@ unfold dc.IoSpecMemMain()
	//@ unfold dc.IoSpecMemPartial()
	//@ dc.setToken(t5)
	//@ dc.setAbsState(s5)
	//@ dc.setSigSessionKeysT(sigSessionKeysT)
	//@ fold dc.IoSpecMemPartial()
	//@ fold dc.IoSpecMemMain()
	state = BlockCipherReady
	dc.encryptionEnabled = true
	//@ fold dc.MemTransfer(state, true)
	return
}

// @ trusted
// @ requires noPerm < p && p <= writePerm
// @ preserves acc(bytes.SliceMem(agentSecret), p)
// @ ensures err == nil ==> bytes.SliceMem(sharedSecret)
// the following postcondition expresses that `IsOnCurve` guarantees that `clientShare` is a valid
// DH pubic key. Instead of existentially quantifying over the corresponding private key, we assume
// `privB` is the corresponding witness
// @ ensures err == nil ==> by.msgB(clientShare) == by.expB(by.generatorB(), privB)
// @ ensures err == nil ==> abs.Abs(sharedSecret) == by.expB(by.expB(by.generatorB(), privB), abs.Abs(agentSecret))
// @ ensures err != nil ==> err.ErrorMem()
func unmarshalAndCheckClientShare(clientShare string, agentSecret []byte /*@, p perm @*/) (sharedSecret []byte, err error /*@, privB by.Bytes @*/) {
	var clientShareBytes []byte
	clientShareBytes, err = base64.StdEncoding.DecodeString(clientShare)
	if err != nil {
		err = fmtErrorf("failed to decode server share: %v", err /*@, perm(1/1) @*/)
		return
	}

	x, y := elliptic.UnmarshalCompressed(elliptic.P384(), clientShareBytes /*@, perm(1/2) @*/)

	// check that the client share is on the curve
	if !elliptic.P384().IsOnCurve(x, y /*@, perm(1/2) @*/) {
		err = fmtError("client share is not on the curve")
		return
	}

	ss, _ := elliptic.P384().ScalarMult(x, y, agentSecret /*@, p/2 @*/) // TODO: Double check it's fine to just use x
	sharedSecret = ss.Bytes( /*@ perm(1/2) @*/ )
	return
}

// SkipHandshake is used to skip handshake if the plugin decides it is not necessary
// @ requires log != nil
// @ preserves dc.Mem() && acc(log.Mem(), _)
// @ ensures err == nil ==> dc.getState() == HandshakeSkipped
func (dc *dataChannel) SkipHandshake(log logger.T) (err error) {
	if dc.getState() != Initialized {
		err = fmtErrorfState("DataChannel is in an invalid state %d", dc.getState())
		return
	}
	logInfo(log, "Skipping handshake.")
	//@ unfold dc.Mem()
	//@ unfold dc.MemInternal(Initialized)
	dc.hs.skipped = true
	//@ unfold acc(dc.MemChannelState(), 1/2)
	dc.dataChannelState = HandshakeSkipped
	//@ fold acc(dc.MemChannelState(), 1/2)
	//@ fold dc.MemInternal(HandshakeSkipped)
	//@ fold dc.Mem()
	return
}

// PerformHandshake performs handshake to share version string and encryption information with clients like cli/console
// Note that sessionplugin.go first calls `NewDataChannel` followed by at most 1 call to `PerformHandshake`.
// Hence, we can require in the specification that no other handshake is currently on-going for `dataChannel` without
// restricting the current client of `DataChannel`.
// @ requires log != nil
// @ requires encryptionEnabled == assumeEncryptionEnabledForVerification()
// @ preserves dc.Mem() && acc(log.Mem(), _)
// @ ensures err == nil ==> dc.getState() == IODistributed
func (dc *dataChannel) PerformHandshake(log logger.T,
	kmsKeyId string,
	encryptionEnabled bool,
	sessionTypeRequest mgsContracts.SessionTypeRequest) (err error) {

	if dc.getState() != Initialized {
		err = fmtErrorfState("DataChannel is in an invalid state %d", dc.getState())
		return
	}

	logDebug(log, "PerformHandshake")

	//@ unfold dc.Mem()
	//@ unfold dc.MemInternal(Initialized)

	if encryptionEnabled {
		// if dc.blockCipher, err = newBlockCipher(dc.context, kmsKeyId); err != nil {
		// 	return fmtErrorf("Initializing BlockCipher failed: %s", err)
		// }
		logInfo(log, "Encryption enabled: initializing block cipher")
		// dc.blockCipher = &cryptolib.BlockCipherT{}
	}
	// initializing the block cipher independently of `encryptionEnabled` simplifies reasoning
	dc.blockCipher = &cryptolib.BlockCipherT{}
	// we inhale the permissions for the modeled ghost fields of this block cipher:
	//@ inhale dc.blockCipher.EncKeyTMem() && dc.blockCipher.DecKeyTMem()
	//@ fold dc.blockCipher.Mem()

	dc.hs.handshakeStartTime = time.Now()
	dc.encryptionEnabled = encryptionEnabled
	//@ unfold acc(dc.MemChannelState(), 1/2)
	dc.dataChannelState = BlockCipherInitialized
	//@ fold acc(dc.MemChannelState(), 1/2)
	//@ fold dc.MemInternal(BlockCipherInitialized)
	//@ fold dc.Mem()

	logInfo(log, "Initiating Handshake")
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
	//@ unfold dc.MemInternal(HandshakeRequestSent)
	startReceivingChan := dc.hs.startReceivingChan
	responseChan := dc.hs.responseChan
	//@ fold dc.MemTransfer(HandshakeRequestSent, encryptionEnabled)
	var payload MessageReceptionPayload
	if encryptionEnabled {
		payload = MessageReceptionPayload{
			status: ReceiveHandshakeResponeEncryptionEnabled,
		}
	} else {
		payload = MessageReceptionPayload{
			status: ReceiveHandshakeResponeEncryptionDisabled,
		}
	}
	//@ fold StartReceivingChanInv!<dc, _!>(payload)
	startReceivingChan <- payload

	// Block until handshake response is received or handshake times out
	res, err := dc.tryReceiveResponseAlt(responseChan, handshakeTimeout)
	if err != nil {
		//@ unfold acc(dc.MemChannelState(), 1/2)
		dc.dataChannelState = Erroneous
		//@ fold acc(dc.MemChannelState(), 1/2)
		//@ fold dc.MemInternal(Erroneous)
		//@ fold dc.Mem()
		// If handshake times out here this usually means that the client does not understand handshake or something
		// failed critically when processing handshake request.
		return errors.New("Handshake timed out. Please ensure that you have the latest version of the session manager plugin.")
	}
	// we send the flag `encryptionEnabled` back via the channel such that we are able to express the data channel's
	// state. This flag is expected to be identical to `encryptionEnabled`:
	if res.encryptionEnabled != encryptionEnabled {
		//@ unfold acc(dc.MemChannelState(), 1/2)
		dc.dataChannelState = Erroneous
		//@ fold acc(dc.MemChannelState(), 1/2)
		//@ fold dc.MemInternal(Erroneous)
		//@ fold dc.Mem()
		return errors.New("Unexpected result from processing handshake response")
	}
	//@ unfold ResponseChanInv!<dc, _!>(res)
	//@ unfold dc.MemTransfer(res.state, encryptionEnabled)
	err = dc.hs.error
	if err != nil {
		//@ unfold acc(dc.MemChannelState(), 1/2)
		dc.dataChannelState = Erroneous
		//@ fold acc(dc.MemChannelState(), 1/2)
		//@ fold dc.MemInternal(Erroneous)
		//@ fold dc.Mem()
		return err
	}
	logDebug(log, "Handshake response received")

	//@ assert res.state == BlockCipherReady
	//@ unfold acc(dc.MemChannelState(), 1/2)
	dc.dataChannelState = res.state
	//@ fold acc(dc.MemChannelState(), 1/2)
	dc.hs.handshakeEndTime = time.Now()
	//@ fold dc.MemInternal(res.state)
	//@ fold dc.Mem()
	handshakeCompletePayload, err := dc.buildHandshakeCompletePayload(log)
	if err != nil {
		return err
	}
	if err := dc.sendHandshakeComplete(log, handshakeCompletePayload); err != nil {
		return err
	}
	//@ unfold dc.Mem()
	//@ unfold dc.MemInternal(HandshakeCompleted)
	logInfo(log, "Handshake successfully completed.")

	//@ unfold acc(dc.MemChannelState(), 1/2)
	dc.dataChannelState = IODistributed
	// do not fold `MemChannelState` since we split the permission to `dataChannelState` for
	// the threads next.

	dc.ioLock = &sync.Mutex{}
	//@ dc.ioLockDidLocalReceive = false
	//@ dc.ioLockCanRemoteSend = false
	//@ dc.ioLockDidRemoteReceive = false
	//@ dc.ioLockCanLocalSend = false
	//@ fold IoLockInv!<dc, dc.dataStream.GetInstanceId(), dc.dataStream.GetClientId(), dc.agentLTKeyARN!>()
	//@ dc.ioLock.SetInv(IoLockInv!<dc, dc.dataStream.GetInstanceId(), dc.dataStream.GetClientId(), dc.agentLTKeyARN!>)

	payload = MessageReceptionPayload{
		status: ReceiveOtherResponse,
	}
	//@ fold dc.MemRecv()
	//@ fold StartReceivingChanInv!<dc, _!>(payload)
	startReceivingChan <- payload

	//@ fold acc(dc.MemInternal(IODistributed), 1/2)
	//@ fold dc.Mem()
	return
}

// @ trusted
// @ requires pl.token(t0) && iospec.e_FrFact(t0, rid)
// @ ensures  err == nil ==> bytes.SliceMem(priv)
// @ ensures  err == nil ==> pl.token(t1) && t1 == old(iospec.get_e_FrFact_placeDst(t0, rid))
// @ ensures  err == nil ==> abs.Abs(priv) == by.gamma(old(iospec.get_e_FrFact_r1(t0, rid)))
// @ ensures  err == nil ==> by.msgB(encodedPk) == by.expB(by.generatorB(), abs.Abs(priv))
// @ ensures  err != nil ==> err.ErrorMem()
// @ ensures  err != nil ==> t1 == t0 && pl.token(t0) && iospec.e_FrFact(t0, rid) &&
// @ 	iospec.get_e_FrFact_placeDst(t0, rid) == old(iospec.get_e_FrFact_placeDst(t0, rid)) &&
// @    iospec.get_e_FrFact_r1(t0, rid) == old(iospec.get_e_FrFact_r1(t0, rid))
func generateAndEncodeEllipticKey( /*@ ghost t0 pl.Place, ghost rid tm.Term @*/ ) (priv []byte, encodedPk string, err error /*@, ghost t1 pl.Place @*/) {
	//@ cryptoRand.GetReaderMem()
	priv, x, y, err /*@, t1 @*/ := elliptic.GenerateKey(elliptic.P384(), cryptoRand.Reader /*@, t0, rid @*/)
	if err != nil {
		return nil, "", err /*@, t0 @*/
	}

	// Base64 encode the public part and put it in the message
	agentShare := elliptic.MarshalCompressed(elliptic.P384(), x, y /*@, perm(1/2) @*/)
	encodedPk = base64.StdEncoding.EncodeToString(agentShare /*@, perm(1/2) @*/)
	return
}

// @ trusted
// @ ensures err == nil ==> bytes.SliceMem(signPayloadBytes)
// @ ensures err == nil ==> abs.Abs(signPayloadBytes) == by.tuple3B(by.msgB(compressedPublic), by.msgB(logReaderId), by.msgB(clientId))
// @ ensures err != nil ==> err.ErrorMem()
func getSignAgentSharePayloadBytes(compressedPublic string, clientId string, logReaderId string) (signPayloadBytes []byte, err error) {
	signPayload := &mgsContracts.SignAgentSharePayload{
		AgentShare:  compressedPublic,
		ClientId:    clientId,
		LogReaderId: logReaderId,
	}

	//@ fold signPayload.Mem()
	return json.Marshal(signPayload /*@, perm(1/2) @*/)
}

// @ trusted
// @ ensures err == nil ==> bytes.SliceMem(signPayloadBytes)
// @ ensures err == nil ==> abs.Abs(signPayloadBytes) == by.pairB(by.msgB(encryptedSessionKeys), by.msgB(clientId))
// @ ensures err != nil ==> err.ErrorMem()
func getSignSessionKeysPayloadBytes(encryptedSessionKeys string, clientId string) (signPayloadBytes []byte, err error) {
	signPayload := &mgsContracts.SignSessionKeysPayload{
		EncryptedSessionKeys: encryptedSessionKeys,
		ClientId:             clientId,
	}

	//@ fold signPayload.Mem()
	return json.Marshal(signPayload /*@, perm(1/2) @*/)
}

// @ trusted
// @ requires noPerm < p
// @ requires kmsService.Mem() && acc(bytes.SliceMem(message), p)
// @ requires m == tm.pair(tm.pubTerm(pub.const_SignRequest_pub()), tm.pair(tm.pubTerm(pub.pub_msg(keyId)), messageT))
// @ requires pl.token(t) && iospec.e_Out_KMS(t, rid, agentId, kmsId, rid, m) && by.gamma(messageT) == abs.Abs(message)
// @ requires let t1 := iospec.get_e_Out_KMS_placeDst(t, rid, agentId, kmsId, rid, m) in (
// @     iospec.e_In_KMS(t1, rid))
// @ ensures  kmsService.Mem() && acc(bytes.SliceMem(message), p)
// @ ensures  err == nil ==> by.gamma(signatureT) == by.msgB(signature)
// @ ensures  err != nil ==> err.ErrorMem()
// @ ensures  err == nil ==> let t1 := old(iospec.get_e_Out_KMS_placeDst(t, rid, agentId, kmsId, rid, m)) in (
// @     pl.token(old(iospec.get_e_In_KMS_placeDst(t1, rid))) &&
// @     kmsId == old(iospec.get_e_In_KMS_r1(t1, rid)) &&
// @     agentId == old(iospec.get_e_In_KMS_r2(t1, rid)) &&
// @     rid == old(iospec.get_e_In_KMS_r3(t1, rid)) &&
// @     tm.pair(tm.pubTerm(pub.const_SignResponse_pub()), signatureT) == old(iospec.get_e_In_KMS_r4(t1, rid)))
func signAndEncode(kmsService *crypto.KMSService, keyId string, message []byte /*@, ghost p perm, ghost t pl.Place, ghost rid tm.Term, ghost agentId tm.Term, ghost kmsId tm.Term, ghost messageT tm.Term, ghost m tm.Term @*/) (signature string, err error /*@, ghost signatureT tm.Term @*/) {
	var sig []byte
	sig, err /*@, signatureT @*/ = kmsService.Sign(keyId, message /*@, p, t, rid, agentId, kmsId, messageT, m @*/)
	if err != nil {
		return
	}
	signature = base64.StdEncoding.EncodeToString(sig /*@, perm(1/2)@*/)
	return
}

// @ trusted
// @ ensures err == nil ==> bytes.SliceMem(clientSignPayload)
// @ ensures err == nil ==> abs.Abs(clientSignPayload) == by.pairB(by.msgB(clientShare), by.msgB(agentId))
// @ ensures err != nil ==> err.ErrorMem()
func getVerifyPayloadBytes(clientShare string, agentId string) (clientSignPayload []byte, err error) {
	clientSignPayload := &mgsContracts.SignClientSharePayload{
		ClientShare: clientShare,
		AgentId:     agentId,
	}

	//@ fold clientSignPayload.Mem()
	return json.Marshal(clientSignPayload /*@, perm(1/2) @*/)
}

// @ trusted
// @ requires noPerm < p
// @ preserves acc(bytes.SliceMem(agentReadKey), p) && acc(bytes.SliceMem(agentWriteKey), p)
// @ ensures  err == nil ==> bytes.SliceMem(sessionKeysPayload) && abs.Abs(sessionKeysPayload) == by.pairB(abs.Abs(agentWriteKey), abs.Abs(agentReadKey))
// @ ensures  err != nil ==> err.ErrorMem()
func getSessionKeysPayload(agentWriteKey, agentReadKey []byte /*@, ghost p perm @*/) (sessionKeysPayload []byte, err error) {
	encodedAgentReadKey := base64.RawStdEncoding.EncodeToString(agentReadKey /*@, p/2 @*/)
	encodedAgentWriteKey := base64.RawStdEncoding.EncodeToString(agentWriteKey /*@, p/2 @*/)

	sessionKeys := &mgsContracts.SessionKeys{
		AgentWriteKey: encodedAgentWriteKey,
		AgentReadKey:  encodedAgentReadKey,
	}
	//@ fold sessionKeys.Mem()
	return json.Marshal(sessionKeys /*@, perm(1/2) @*/)
}

// @ trusted
// @ ensures  err == nil ==> by.msgB(encryptedSessionKeysPayload) == by.tuple5B(by.msgB(encodedEncryptedSessionKeys), by.msgB(encodedSigSessionKeys), by.msgB(agentId), by.msgB(agentLTKeyARN), by.msgB(clientId))
// @ ensures  err != nil ==> err.ErrorMem()
func getEncryptedSessionKeysPayload(encodedEncryptedSessionKeys, encodedSigSessionKeys, agentId, agentLTKeyARN, clientId string) (encryptedSessionKeysPayload string, err error) {
	payload := &mgsContracts.EncryptedSessionKeysPayload{
		EncryptedSessionKeys: encodedEncryptedSessionKeys,
		Signature:            encodedSigSessionKeys,
		AgentId:              agentId,
		AgentLTKeyARN:        agentLTKeyARN,
		ClientId:             clientId,
	}
	//@ fold payload.Mem()
	encryptedSessionKeysPayloadBytes, err := json.Marshal(payload /*@, perm(1/2) @*/)
	if err != nil {
		return
	}
	
	encryptedSessionKeysPayload = base64.StdEncoding.EncodeToString(encryptedSessionKeysPayloadBytes /*@, perm(1/2) @*/)
	return
}

// @ trusted
// @ requires noPerm < p
// @ preserves acc(bytes.SliceMem(payload), p) && acc(pk.Mem(), p)
// @ ensures  err == nil ==> by.msgB(encodedCiphertext) == by.aencB(abs.Abs(payload), pk.Abs())
// @ ensures  err != nil ==> err.ErrorMem()
func encryptAndEncode(payload []byte, pk *rsa.PublicKey /*@, ghost p perm @*/) (encodedCiphertext string, err error) {
	//@ cryptoRand.GetReaderMem()
	ciphertext, err := rsa.EncryptPKCS1v15(cryptoRand.Reader, pk, payload /*@, p > writePerm ? perm(1/1) : p/2 @*/)
	if err != nil {
		err = fmtErrorf("failed to encrypt session keys: %v", err /*@, perm(1/1) @*/)
		return
	}
	encodedCiphertext := base64.StdEncoding.EncodeToString(ciphertext /*@, perm(1/2) @*/)
	return
}

// @ trusted
// @ requires noPerm < p
// @ requires acc(handshakeRequestPayload.Mem(), p)
// @ requires handshakeRequestPayload.ContainsSecureSessionAction(secActionB)
// @ ensures  acc(handshakeRequestPayload.Mem(), p)
// @ ensures  handshakeRequestPayload.ContainsSecureSessionAction(secActionB)
// @ ensures  err == nil ==> bytes.SliceMem(handshakeRequestPayloadBytes)
// @ ensures  err == nil ==> abs.Abs(handshakeRequestPayloadBytes) == secActionB
// @ ensures  err != nil ==> err.ErrorMem()
func marshalHandshakeRequest(handshakeRequestPayload *mgsContracts.HandshakeRequestPayload /*@, ghost p perm, ghost secActionB by.Bytes @*/) (handshakeRequestPayloadBytes []byte, err error) {
	return json.Marshal(handshakeRequestPayload /*@, p/2 @*/)
}


// buildHandshakeRequestPayload builds payload for HandshakeRequest
// @ requires log != nil && dc.Mem() && dc.getState() == BlockCipherInitialized
// @ preserves acc(log.Mem(), _)
// @ ensures  dc.Mem()
// @ ensures  err == nil ==> payload.Mem()
// @ ensures  err == nil && !encryptionRequested ==> dc.getState() == BlockCipherInitialized
// @ ensures  err == nil && encryptionRequested ==> dc.getState() == AgentSecretCreatedAndSigned
// @ ensures  err == nil && encryptionRequested ==> unfolding acc(dc.Mem(), _) in unfolding acc(dc.MemInternal(AgentSecretCreatedAndSigned), _) in (
// @	payload.ContainsSecureSessionAction(by.tuple4B(by.expB(by.generatorB(), by.gamma(dc.getAgentShareT())), by.gamma(dc.getAgentShareSignatureT()), by.msgB(dc.agentLTKeyARN), by.msgB(dc.logReaderId))))
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
		//@ unfold dc.Mem()
		//@ unfold dc.MemInternal(BlockCipherInitialized)
		//@ t0 := dc.getToken()
		//@ rid := dc.getRid()
		//@ s0 := dc.getAbsState()
		//@ unfold iospec.P_Agent(t0, rid, s0)
		//@ unfold iospec.phiRF_Agent_14(t0, rid, s0)
		//@ agentSecretT := iospec.get_e_FrFact_r1(t0, rid)
		agentSecret, compressedPublic, err /*@, t1 @*/ := generateAndEncodeEllipticKey( /*@ t0, rid @*/ )
		if err != nil {
			//@ fold iospec.phiRF_Agent_14(t0, rid, s0)
			//@ fold iospec.P_Agent(t0, rid, s0)
			//@ fold dc.MemInternal(BlockCipherInitialized)
			//@ fold dc.Mem()
			logErrorf(log, "failed to generate client secret: %v", err /*@, perm(1/2) @*/)
			return nil, err
		}
		//@ s1 := s0 union mset[ft.Fact]{ ft.FrFact_Agent(rid, agentSecretT) }
		//@ unfold dc.IoSpecMemMain()
		//@ dc.setToken(t1)
		//@ dc.setAbsState(s1)
		//@ fold dc.IoSpecMemMain()

		dc.state.agentSecret = agentSecret

		clientId := dc.dataStream.GetClientId()
		signPayloadBytes, err := getSignAgentSharePayloadBytes(compressedPublic, clientId, dc.logReaderId)
		if err != nil {
			//@ fold dc.MemInternal(BlockCipherInitialized)
			//@ fold dc.Mem()
			err = fmtErrorf("failed to encode sign payload: %v", err /*@, perm(1/2) @*/)
			logError(log, err /*@, perm(1/2) @*/)
			return nil, err
		}
		//@ signPayloadT := tm.pair(tm.exp(tm.pubTerm(pub.const_g_pub()), agentSecretT), tm.pair(tm.pubTerm(pub.pub_msg(dc.logReaderId)), tm.pubTerm(pub.pub_msg(clientId))))

		// unfold phiR_Agent_0 to obtain Out_KMS_Agent fact
		/*@
			agentIdT := dc.getAgentIdT()
			kmsIdT := dc.getKMSIdT()
			clientIdT := dc.getClientIdT()
			readerIdT := dc.getReaderIdT()
			agentLtKeyIdT := tm.pubTerm(pub.pub_msg(dc.agentLTKeyARN))
			logPkT := dc.getLogLTPkT()
			m := tm.pair(tm.pubTerm(pub.const_SignRequest_pub()), tm.pair(agentLtKeyIdT, signPayloadT))
			l := mset[ft.Fact] {
				ft.Setup_Agent(rid, agentIdT, kmsIdT, clientIdT, readerIdT, agentLtKeyIdT, logPkT),
				ft.FrFact_Agent(rid, agentSecretT),
			}
			a := mset[cl.Claim] {
				cl.AgentStarted(),
			}
			r := mset[ft.Fact] {
		    	ft.St_Agent_1(rid, agentIdT, kmsIdT, clientIdT, readerIdT, agentLtKeyIdT, logPkT, agentSecretT),
		        ft.Out_KMS_Agent(rid, agentIdT, kmsIdT, rid, m),
			}
			@*/
		//@ unfold iospec.P_Agent(t1, rid, s1)
		//@ unfold iospec.phiR_Agent_0(t1, rid, s1)
		//@ t2 := iospec.internBIO_e_Agent_SendSignRequest(t1, rid, agentIdT, kmsIdT, clientIdT, readerIdT, agentLtKeyIdT, logPkT, agentSecretT, l, a, r)
		//@ s2 := ft.U(l, r, s1)

		// unfold phiRG_Agent_12 to obtain e_Out_KMS permission
		//@ unfold iospec.P_Agent(t2, rid, s2)
		//@ unfold iospec.phiRG_Agent_12(t2, rid, s2)
		//@ t3 := iospec.get_e_Out_KMS_placeDst(t2, rid, agentIdT, kmsIdT, rid, m)
		//@ s3 := s2 setminus mset[ft.Fact] { ft.Out_KMS_Agent(rid, agentIdT, kmsIdT, rid, m) }

		// unfold phiRF_Agent_15 to obtain e_In_KMS permission since `signAndEncode` performs a send and receive operation
		//@ unfold iospec.P_Agent(t3, rid, s3)
		//@ unfold iospec.phiRF_Agent_15(t3, rid, s3)
		//@ t4 := iospec.get_e_In_KMS_placeDst(t3, rid)

		sig, err /*@, signatureT @*/ := signAndEncode(dc.state.kmsService, dc.agentLTKeyARN, signPayloadBytes /*@, perm(1/2), t2, rid, agentIdT, kmsIdT, signPayloadT, m @*/)
		if err != nil {
			// since we have already performed `internBIO_e_Agent_SendSignRequest` and potentially partially `signAndEncode`,
			// there is no way we can get back into a regular state that would allow re-execution of this function by, e.g.,
			// folding I/O predicates. This is in accordance to the Tamarin model, which also does not foresee a participant
			// instance to retry certain steps
			//@ unfold acc(dc.MemChannelState(), 1/2)
			dc.dataChannelState = Erroneous
			//@ fold acc(dc.MemChannelState(), 1/2)
			//@ fold dc.MemInternal(Erroneous)
			//@ fold dc.Mem()
			err = fmtErrorf("failed to sign agent sign payload: %v", err /*@, perm(1/2) @*/)
			logError(log, err /*@, perm(1/2) @*/)
			return nil, err
		}

		//@ s4 := s3 union mset[ft.Fact] { ft.In_KMS_Agent(rid, kmsIdT, agentIdT, rid, tm.pair(tm.pubTerm(pub.const_SignResponse_pub()), signatureT)) }

		// unfold phiR_Agent_1 to transition to St_Agent_2
		/*@
			l2 := mset[ft.Fact] {
				ft.St_Agent_1(rid, agentIdT, kmsIdT, clientIdT, readerIdT, agentLtKeyIdT, logPkT, agentSecretT),
				ft.In_KMS_Agent(rid, kmsIdT, agentIdT, rid, tm.pair(tm.pubTerm(pub.const_SignResponse_pub()), signatureT)),
			}
			a2 := mset[cl.Claim] {
				cl.AgentSignResponse(kmsIdT, agentIdT, rid, tm.pair(tm.pubTerm(pub.const_SignResponse_pub()), signatureT)),
			}
			r2 := mset[ft.Fact] {
		    	ft.St_Agent_2(rid, agentIdT, kmsIdT, clientIdT, readerIdT, agentLtKeyIdT, logPkT, agentSecretT, signatureT),
			}
			@*/
		//@ unfold iospec.P_Agent(t4, rid, s4)
		//@ unfold iospec.phiR_Agent_1(t4, rid, s4)
		//@ t5 := iospec.internBIO_e_Agent_RecvSignResponse(t4, rid, agentIdT, kmsIdT, clientIdT, readerIdT, agentLtKeyIdT, logPkT, agentSecretT, signatureT, l2, a2, r2)
		//@ s5 := ft.U(l2, r2, s4)

		//@ unfold dc.IoSpecMemMain()
		//@ unfold dc.IoSpecMemPartial()
		//@ dc.setToken(t5)
		//@ dc.setAbsState(s5)
		//@ dc.setAgentShareT(agentSecretT)
		//@ dc.setAgentShareSignatureT(signatureT)
		//@ fold dc.IoSpecMemPartial()
		//@ fold dc.IoSpecMemMain()
		//@ unfold acc(dc.MemChannelState(), 1/2)
		dc.dataChannelState = AgentSecretCreatedAndSigned
		//@ fold acc(dc.MemChannelState(), 1/2)

		logDebugfString(log, "agent signed sign payload: %x", sig)

		req := &mgsContracts.SecureSessionRequest{
			Version:        1,
			ShareAlgorithm: "P384",
			AgentShare:     compressedPublic,
			Signature:      sig,
			AgentLTKeyARN:  dc.agentLTKeyARN,
			LogReaderId:    dc.logReaderId,
		}
		//@ fold acc(req.Mem(), 1/2)
		//@ fold dc.MemInternal(AgentSecretCreatedAndSigned)
		//@ fold dc.Mem()

		logDebugfSecureSessionRequest(log, "client generated SecureSessionRequest: %+v", req /*@, perm(1/2) @*/)

		secureSessionAction := mgsContracts.RequestedClientAction{
			ActionType:       mgsContracts.SecureSession,
			ActionParameters: *req,
		}
		handshakeRequest.RequestedClientActions = []mgsContracts.RequestedClientAction{sessionTypeAction, secureSessionAction}
		//@ fold handshakeRequest.RequestedClientActions[0].Mem()
		//@ fold handshakeRequest.RequestedClientActions[1].Mem()
		//@ fold handshakeRequest.Mem()
	} else {
		handshakeRequest.RequestedClientActions = []mgsContracts.RequestedClientAction{sessionTypeAction}
		//@ fold handshakeRequest.RequestedClientActions[0].Mem()
		//@ fold handshakeRequest.Mem()
	}

	return handshakeRequest, nil
}

// sendHandshakeRequest sends handshake request
// @ requires log != nil && handshakeRequestPayload.Mem()
// @ requires dc.Mem() && dc.getState() >= BlockCipherInitialized
// @ requires unfolding acc(dc.Mem(), _) in unfolding acc(dc.MemInternal(dc.dataChannelState), _) in dc.encryptionEnabled ==>
// @	dc.dataChannelState == AgentSecretCreatedAndSigned &&
// @	handshakeRequestPayload.ContainsSecureSessionAction(by.tuple4B(by.expB(by.generatorB(), by.gamma(dc.getAgentShareT())), by.gamma(dc.getAgentShareSignatureT()), by.msgB(dc.agentLTKeyARN), by.msgB(dc.logReaderId)))
// @ preserves acc(log.Mem(), _)
// @ ensures dc.Mem()
// @ ensures err == nil ==> dc.getState() == HandshakeRequestSent
func (dc *dataChannel) sendHandshakeRequest(log logger.T, handshakeRequestPayload *mgsContracts.HandshakeRequestPayload) (err error) {
	//@ secActionB := unfolding acc(dc.Mem(), _) in unfolding acc(dc.MemInternal(dc.dataChannelState), _) in by.tuple4B(by.expB(by.generatorB(), by.gamma(dc.getAgentShareT())), by.gamma(dc.getAgentShareSignatureT()), by.msgB(dc.agentLTKeyARN), by.msgB(dc.logReaderId))
	var handshakeRequestPayloadBytes []byte
	if handshakeRequestPayloadBytes, err = marshalHandshakeRequest(handshakeRequestPayload /*@, perm(1/2), secActionB @*/); err != nil {
		return fmtErrorfHandshakeRequestErr("Could not serialize HandshakeRequest message %v, err: %s", handshakeRequestPayload, err /*@, perm(1/2) @*/)
	}

	logDebug(log, "Sending Handshake Request.")
	logTracefHandshakeRequestPayload(log, "Sending HandshakeRequest message with content %v", handshakeRequestPayload /*@, perm(1/2) @*/)

	//@ unfold dc.Mem()
	//@ state := dc.dataChannelState
	//@ unfold dc.MemInternal(state)
	//@ secActionT := tm.pair(tm.exp(tm.pubTerm(pub.const_g_pub()), dc.getAgentShareT()), tm.pair(dc.getAgentShareSignatureT(), tm.pair(tm.pubTerm(pub.pub_msg(dc.agentLTKeyARN)), tm.pubTerm(pub.pub_msg(dc.logReaderId)))))
	//@ t0 := dc.getToken()
	//@ rid := dc.getRid()
	//@ s0 := dc.getAbsState()
	/*@
	agentIdT := dc.getAgentIdT()
	kmsIdT := dc.getKMSIdT()
	clientIdT := dc.getClientIdT()
	readerIdT := dc.getReaderIdT()
	agentLtKeyIdT := tm.pubTerm(pub.pub_msg(dc.agentLTKeyARN))
	logPkT := dc.getLogLTPkT()
	agentSecretT := dc.getAgentShareT()
	signatureT := dc.getAgentShareSignatureT()
	l := mset[ft.Fact] {
		ft.St_Agent_2(rid, agentIdT, kmsIdT, clientIdT, readerIdT, agentLtKeyIdT, logPkT, agentSecretT, signatureT),
	}
	a := mset[cl.Claim] {
		cl.AgentSecureSessionRequest(agentIdT, clientIdT, tm.exp(tm.pubTerm(pub.const_g_pub()), agentSecretT), signatureT, agentLtKeyIdT),
	}
	r := mset[ft.Fact] {
		ft.St_Agent_3(rid, agentIdT, kmsIdT, clientIdT, readerIdT, agentLtKeyIdT, logPkT, agentSecretT, signatureT),
	    ft.OutFact_Agent(rid, tm.pair(tm.pubTerm(pub.const_SecureSessionRequest_pub()), tm.pair(tm.exp(tm.pubTerm(pub.const_g_pub()), agentSecretT), tm.pair(signatureT, tm.pair(agentLtKeyIdT, readerIdT))))),
	    ft.OutFact_Agent(rid, tm.pair(tm.pubTerm(pub.const_Log_pub()), tm.pair(tm.pubTerm(pub.const_SecureSessionRequest_pub()), tm.pair(tm.exp(tm.pubTerm(pub.const_g_pub()), agentSecretT), tm.pair(signatureT, tm.pair(agentLtKeyIdT, readerIdT)))))),
	}
	@*/
	//@ unfold iospec.P_Agent(t0, rid, s0)
	//@ unfold iospec.phiR_Agent_2(t0, rid, s0)
	//@ t1 := iospec.internBIO_e_Agent_SendSecureSessionRequest(t0, rid, agentIdT, kmsIdT, clientIdT, readerIdT, agentLtKeyIdT, logPkT, agentSecretT, signatureT, l, a, r)
	//@ s1 := ft.U(l, r, s0)
	//@ unfold dc.IoSpecMemMain()
	//@ dc.setToken(t1)
	//@ dc.setAbsState(s1)
	//@ fold dc.IoSpecMemMain()
	//@ unfold acc(dc.MemChannelState(), 1/2)
	dc.dataChannelState = HandshakeRequestSent
	//@ fold acc(dc.MemChannelState(), 1/2)
	//@ fold dc.MemInternal(HandshakeRequestSent)
	//@ fold dc.Mem()

	if err = dc.sendData(log, mgsContracts.HandshakeRequest, handshakeRequestPayloadBytes /*@, perm(1/2), secActionT, false, false @*/); err != nil {
		return fmtErrorf("Failed sending of HandshakeRequest message, err: %s", err /*@, perm(1/2) @*/)
	}
	return nil
}

// buildHandshakeCompletePayload builds payload for HandshakeComplete
// @ requires log != nil && dc.Mem() && dc.getState() >= Initialized
// @ requires unfolding acc(dc.Mem(), _) in unfolding acc(dc.MemInternal(dc.dataChannelState), _) in dc.encryptionEnabled ==> dc.dataChannelState == BlockCipherReady
// @ preserves acc(log.Mem(), _)
// @ ensures dc.Mem() && dc.getState() == old(dc.getState())
// @ ensures err == nil ==> payload.Mem() && payload.Abs() == by.gamma(tm.pair(tm.pubTerm(pub.const_HandshakeCompletePayload_pub()), dc.GetInFactT()))
// @ ensures err == nil ==> ft.InFact_Agent(dc.GetRid(), dc.GetInFactT()) in dc.GetAbsState()
// @ ensures err != nil ==> err.ErrorMem()
func (dc *dataChannel) buildHandshakeCompletePayload(log logger.T) (payload *mgsContracts.HandshakeCompletePayload, err error) {
	clientVersion, err := dc.GetClientVersion( /*@ perm(1/2) @*/ )
	if err != nil {
		return
	}

	//@ unfold dc.Mem()
	//@ state := dc.dataChannelState
	//@ unfold dc.MemInternal(state)
	//@ t0 := dc.getToken()
	//@ rid := dc.getRid()
	//@ s0 := dc.getAbsState()
	//@ unfold iospec.P_Agent(t0, rid, s0)
	//@ unfold iospec.phiRF_Agent_16(t0, rid, s0)
	//@ t1 := iospec.get_e_InFact_placeDst(t0, rid)

	duration := dc.hs.handshakeEndTime.Sub(dc.hs.handshakeStartTime)
	customerMessage, err /*@, payloadT @*/ := getHandshakeCompletePayload(duration, dc.separateOutputPayload, dc.encryptionEnabled, clientVersion /*@, t0, rid @*/)
	if err != nil {
		//@ fold iospec.phiRF_Agent_16(t0, rid, s0)
		//@ fold iospec.P_Agent(t0, rid, s0)
		//@ fold dc.MemInternal(state)
		//@ fold dc.Mem()
		return
	}
	//@ s1 := s0 union mset[ft.Fact]{ ft.InFact_Agent(rid, payloadT) }
	//@ unfold dc.IoSpecMemMain()
	//@ unfold dc.IoSpecMemPartial()
	//@ dc.setToken(t1)
	//@ dc.setAbsState(s1)
	//@ dc.setInFactT(payloadT)
	//@ fold dc.IoSpecMemPartial()
	//@ fold dc.IoSpecMemMain()
	//@ fold dc.MemInternal(state)
	//@ fold dc.Mem()

	payload = &mgsContracts.HandshakeCompletePayload{
		HandshakeTimeToComplete: duration,
		CustomerMessage: customerMessage,
	}
	//@ fold payload.Mem()
	return
}

// sendHandshakeComplete sends handshake complete
// @ requires log != nil && handshakeCompletePayload.Mem()
// @ requires dc.Mem() && dc.getState() == BlockCipherReady
// @ requires handshakeCompletePayload.Abs() == by.gamma(tm.pair(tm.pubTerm(pub.const_HandshakeCompletePayload_pub()), dc.GetInFactT()))
// @ requires ft.InFact_Agent(dc.GetRid(), dc.GetInFactT()) in dc.GetAbsState()
// @ preserves acc(log.Mem(), _)
// @ ensures dc.Mem()
// @ ensures err == nil ==> dc.getState() == HandshakeCompleted && unfolding acc(dc.Mem(), _) in unfolding acc(dc.MemInternal(HandshakeCompleted), _) in dc.hs.complete
// @ ensures err != nil ==> err.ErrorMem()
func (dc *dataChannel) sendHandshakeComplete(log logger.T, handshakeCompletePayload *mgsContracts.HandshakeCompletePayload) (err error) {
	handshakeCompletePayloadBytes, err := marshalHandshakeComplete(handshakeCompletePayload /*@, perm(1/2) @*/)
	if err != nil {
		return fmtErrorfHandshakeCompleteErr("Could not serialize HandshakeComplete message %v, err: %s", handshakeCompletePayload, err /*@, perm(1/1) @*/)
	}
	assert abs.Abs(handshakeCompletePayloadBytes) == handshakeCompletePayload.Abs()

	logDebug(log, "Sending HandshakeComplete.")
	logTracefHandshakeCompletePayload(log, "Sending HandshakeComplete message with content %v", handshakeCompletePayload /*@, perm(1/2) @*/)
	//@ payloadT := dc.GetInFactT()
	//@ inputDataT := tm.pair(tm.pubTerm(pub.const_HandshakeCompletePayload_pub()), payloadT)

	//@ unfold dc.Mem()
	//@ unfold dc.MemInternal(BlockCipherReady)
	//@ rid, AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, xT, SigX := dc.getRid(), dc.getAgentIdT(), dc.getKMSIdT(), dc.getClientIdT(), dc.getReaderIdT(), tm.pubTerm(pub.pub_msg(dc.agentLTKeyARN)), dc.getLogLTPkT(), dc.getAgentShareT(), dc.getAgentShareSignatureT()
	//@ t0 := dc.getToken()
	//@ s0 := dc.getAbsState()
	//@ sharedSecretT := dc.getSharedSecretT()
	//@ clientLtKeyIdT := dc.getClientLtKeyIdT()
	//@ clientSecretT := dc.getClientShareT()
	//@ sigYT := dc.getClientShareSignatureT()
	//@ sigSessionKeysT := dc.getSigSessionKeysT()
	/*@
		l := mset[ft.Fact] {
			ft.St_Agent_9(rid, AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, xT, SigX, clientLtKeyIdT, tm.exp(tm.pubTerm(pub.const_g_pub()), clientSecretT), sigYT, sigSessionKeysT),
			ft.InFact_Agent(rid, payloadT),
		}
		a := mset[cl.Claim] {
			cl.Agent_Finish(AgentId),
			cl.Secret(tm.pair(tm.kdf1(sharedSecretT), tm.kdf2(sharedSecretT))),
			cl.Commit(tm.pubTerm(pub.const_Agent_pub()), tm.pubTerm(pub.const_Client_pub()), ut.tuple4(AgentId, ClientId, tm.kdf1(sharedSecretT), tm.kdf2(sharedSecretT))),
			cl.Running(tm.pubTerm(pub.const_Agent_pub()), tm.pubTerm(pub.const_Client_pub()), ut.tuple4(AgentId, ClientId, tm.kdf1(sharedSecretT), tm.kdf2(sharedSecretT))),
			cl.HonestReader(ReaderId),
			cl.HonestKmsOwner(AgentId),
			cl.HonestKmsOwner(ClientId),
			cl.AgentHandshakeCompleted(rid, AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, xT, clientLtKeyIdT, tm.exp(tm.pubTerm(pub.const_g_pub()), clientSecretT)),
		}
		r := mset[ft.Fact] {
		    ft.St_Agent_10(rid, AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, xT, SigX, clientLtKeyIdT, tm.exp(tm.pubTerm(pub.const_g_pub()), clientSecretT), sigYT, sigSessionKeysT),
			ft.OutFact_Agent(rid, tm.pair(tm.pubTerm(pub.const_HandshakeComplete_pub()), tm.senc(tm.pair(tm.pubTerm(pub.const_HandshakeCompletePayload_pub()), payloadT), tm.kdf1(sharedSecretT)))),
			ft.OutFact_Agent(rid, ut.tuple3(tm.pubTerm(pub.const_Log_pub()), tm.pubTerm(pub.const_HandshakeComplete_pub()), tm.senc(tm.pair(tm.pubTerm(pub.const_HandshakeCompletePayload_pub()), payloadT), tm.kdf1(sharedSecretT)))),
		}
	@*/
	//@ unfold iospec.P_Agent(t0, rid, s0)
	//@ unfold iospec.phiR_Agent_9(t0, rid, s0)
	//@ t1 := iospec.internBIO_e_Agent_SendHandshakeComplete(t0, rid, AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, xT, SigX, clientLtKeyIdT, tm.exp(tm.pubTerm(pub.const_g_pub()), clientSecretT), sigYT, sigSessionKeysT, payloadT, l, a, r)
	//@ s1 := ft.U(l, r, s0)
	//@ unfold dc.IoSpecMemMain()
	//@ dc.setToken(t1)
	//@ dc.setAbsState(s1)
	//@ fold dc.IoSpecMemMain()
	//@ unfold acc(dc.MemChannelState(), 1/2)
	dc.dataChannelState = HandshakeCompleted
	//@ fold acc(dc.MemChannelState(), 1/2)
	//@ fold dc.MemInternal(HandshakeCompleted)
	//@ fold dc.Mem()

	if err = dc.sendData(log, mgsContracts.HandshakeComplete, handshakeCompletePayloadBytes /*@, perm(1/2), inputDataT, true, false @*/); err != nil {
		return err
	}

	//@ unfold dc.Mem()
	//@ unfold dc.MemInternal(HandshakeCompleted)
	dc.hs.complete = true
	//@ fold dc.MemInternal(HandshakeCompleted)
	//@ fold dc.Mem()

	return nil
}

// We model is function as receiving the payload with the corresponding term representation from the
// environment because we model in Tamarin that the payload is under full adversarial control.
// Conceptually, we receive an arbitrary payload from the environment and check whether it's equal to
// the tuple of duration and customer message (on the byte-level). Otherwise, we reject the message and
// return an error.
// @ trusted
// @ requires pl.token(t) && iospec.e_InFact(t, rid)
// @ ensures  err == nil ==> pl.token(old(iospec.get_e_InFact_placeDst(t, rid))) &&
// @	payloadT == old(iospec.get_e_InFact_r1(t, rid))
// @ ensures err == nil ==> by.gamma(payloadT) == by.pairB(by.durationB(handshakeDuration), by.msgB(customerMessage))
// @ ensures err != nil ==> err.ErrorMem()
// @ ensures err != nil ==> pl.token(t) && iospec.e_InFact(t, rid) &&
// @ 	iospec.get_e_InFact_placeDst(t, rid) == old(iospec.get_e_InFact_placeDst(t, rid)) &&
// @ 	iospec.get_e_InFact_r1(t, rid) == old(iospec.get_e_InFact_r1(t, rid))
func getHandshakeCompletePayload(handshakeDuration time.Duration, separateOutputPayload, encryptionEnabled bool, clientVersion string /*@, ghost t pl.Place, ghost rid tm.Term @*/) (customerMessage string, err error /*@, ghost payloadT tm.Term @*/) {
	customerMessage = ""
	if separateOutputPayload == true && versionutil.Compare(clientVersion, clientVersionWithoutOutputSeparation, true) <= 0 {
		customerMessage += "Please update session manager plugin version (minimum required version " +
			firstVersionWithOutputSeparationFeature +
			") for fully support of separate StdOut/StdErr output.\r\n"
	}

	if encryptionEnabled {
		customerMessage += "This session is encrypted using AWS KMS."
	}

	return
}

// @ trusted
// @ requires noPerm < p
// @ requires acc(handshakeCompletePayload.Mem(), p)
// @ ensures  acc(handshakeCompletePayload.Mem(), p)
// @ ensures  err == nil ==> bytes.SliceMem(handshakeCompletePayloadBytes)
// @ ensures  err == nil ==> abs.Abs(handshakeCompletePayloadBytes) == handshakeCompletePayload.Abs()
// @ ensures  err != nil ==> err.ErrorMem()
func marshalHandshakeComplete(handshakeCompletePayload *mgsContracts.HandshakeCompletePayload /*@, ghost p perm @*/) (handshakeCompletePayloadBytes []byte, err error) {
	return json.Marshal(handshakeCompletePayload /*@, p/2 @*/)
}

// GetClientVersion returns version of the client
// @ requires noPerm < p
// @ preserves acc(dc.Mem(), p)
// @ ensures err != nil ==> err.ErrorMem()
func (dc *dataChannel) GetClientVersion( /*@ ghost p perm @*/ ) (version string, err error) {
	if dc.getState() == Erroneous {
		err = fmtErrorfState("DataChannel is in an invalid state %d", dc.getState())
		return
	}
	return /*@ unfolding acc(dc.Mem(), p) in unfolding acc(dc.MemInternal(dc.dataChannelState), p/2) in @*/ dc.hs.clientVersion, nil
}

// GetInstanceId returns id of the target
// @ requires noPerm < p
// @ preserves acc(dc.Mem(), p)
func (dc *dataChannel) GetInstanceId( /*@ ghost p perm @*/ ) (instanceId string, err error) {
	if dc.getState() < Initialized {
		err = fmtErrorfState("DataChannel is in an invalid state %d", dc.getState())
		return
	}
	return /*@ unfolding acc(dc.Mem(), p) in unfolding acc(dc.MemInternal(dc.dataChannelState), p/2) in @*/ dc.dataStream.GetInstanceId(), nil
}

// GetRegion returns aws region of the target
// @ requires noPerm < p
// @ preserves acc(dc.Mem(), p)
func (dc *dataChannel) GetRegion( /*@ ghost p perm @*/ ) (region string, err error) {
	if dc.getState() < Initialized {
		err = fmtErrorfState("DataChannel is in an invalid state %d", dc.getState())
		return
	}
	return /*@ unfolding acc(dc.Mem(), p) in unfolding acc(dc.MemInternal(dc.dataChannelState), p/2) in @*/ dc.dataStream.GetRegion(), nil
}

// IsActive returns a boolean value indicating the datachannel is actively listening
// and communicating with service
// @ requires noPerm < p
// @ preserves acc(dc.Mem(), p)
func (dc *dataChannel) IsActive( /*@ ghost p perm @*/ ) (isActive bool, err error) {
	if dc.getState() < Initialized {
		err = fmtErrorfState("DataChannel is in an invalid state %d", dc.getState())
		return
	}
	return /*@ unfolding acc(dc.Mem(), p) in unfolding acc(dc.MemInternal(dc.dataChannelState), p/2) in @*/ dc.dataStream.IsActive(), nil
}

// GetSeparateOutputPayload returns boolean value indicating separate
// stdout/stderr output for non-interactive session or not
// @ requires noPerm < p
// @ preserves acc(dc.Mem(), p)
func (dc *dataChannel) GetSeparateOutputPayload( /*@ ghost p perm @*/ ) (res bool, err error) {
	if dc.getState() == Erroneous {
		err = fmtErrorfState("DataChannel is in an invalid state %d", dc.getState())
		return
	}
	return /*@ unfolding acc(dc.Mem(), _) in unfolding acc(dc.MemInternal(dc.dataChannelState), _) in @*/ dc.separateOutputPayload, nil
}

// SetSeparateOutputPayload set separateOutputPayload value
// @ preserves dc.Mem()
// @ ensures dc.getState() == old(dc.getState())
func (dc *dataChannel) SetSeparateOutputPayload(separateOutputPayload bool) (err error) {
	if dc.getState() == Erroneous || dc.getState() == IODistributed {
		err = fmtErrorfState("DataChannel is in an invalid state %d", dc.getState())
		return
	}
	//@ unfold dc.Mem()
	//@ state := dc.dataChannelState
	//@ unfold dc.MemInternal(state)
	dc.separateOutputPayload = separateOutputPayload
	//@ fold dc.MemInternal(state)
	//@ fold dc.Mem()
	return
}

// @ requires log != nil
// @ preserves dc.Mem() && acc(log.Mem(), _)
// @ ensures dc.getState() == old(dc.getState())
func (dc *dataChannel) PrepareToCloseChannel(log logger.T) (err error) {
	if dc.getState() < Initialized {
		err = fmtErrorfState("DataChannel is in an invalid state %d", dc.getState())
		return
	}
	//@ unfold dc.Mem()
	//@ state := dc.dataChannelState
	//@ unfold acc(dc.MemInternal(state), 1/4)
	dc.dataStream.PrepareToCloseChannel(log /*@, perm(1/8) @*/)
	//@ fold acc(dc.MemInternal(state), 1/4)
	//@ fold dc.Mem()
	return
}

// @ requires log != nil
// @ preserves dc.Mem() && acc(log.Mem(), _)
// @ ensures dc.getState() == old(dc.getState())
func (dc *dataChannel) Close(log logger.T) (err error) {
	if dc.getState() < Initialized {
		err = fmtErrorfState("DataChannel is in an invalid state %d", dc.getState())
		return
	}
	//@ unfold dc.Mem()
	//@ state := dc.dataChannelState
	//@ unfold acc(dc.MemInternal(state), 1/4)
	err = dc.dataStream.Close(log /*@, perm(1/8) @*/)
	//@ fold acc(dc.MemInternal(state), 1/4)
	//@ fold dc.Mem()
	return
}

// @ trusted
// @ requires acc(log.Mem(), _) && noPerm < p
// @ preserves acc(param.Mem(), p)
func logTracefHandshakeRequestPayload(log logger.T, formatStr string, param *mgsContracts.HandshakeRequestPayload /*@, ghost p perm @*/) {
	log.Tracef(formatStr, param)
}

// @ trusted
// @ requires acc(log.Mem(), _) && noPerm < p
// @ preserves acc(param.Mem(), p)
func logTracefHandshakeCompletePayload(log logger.T, formatStr string, param *mgsContracts.HandshakeCompletePayload /*@, ghost p perm @*/) {
	log.Tracef(formatStr, param)
}

// @ trusted
// @ requires acc(log.Mem(), _)
func logDebug(log logger.T, str string) {
	log.Debug(str)
}

// @ trusted
// @ requires acc(log.Mem(), _)
func logDebugfPayloadType(log logger.T, formatStr string, param mgsContracts.PayloadType) {
	log.Debugf(formatStr, param)
}

// @ trusted
// @ requires acc(log.Mem(), _)
func logDebugfString(log logger.T, formatStr string, param string) {
	log.Debugf(formatStr, param)
}

// @ requires noPerm < p
// @ requires acc(log.Mem(), _) && acc(bytes.SliceMem(param), p)
// @ ensures  acc(bytes.SliceMem(param), p)
func logDebugfBytes(log logger.T, formatStr string, param []byte /*@, ghost p perm @*/) {
	strParam := base64.RawStdEncoding.EncodeToString(param /*@, perm(p/2) @*/)
	logDebugfString(log, formatStr, strParam)
}

// @ trusted
// @ requires acc(log.Mem(), _) && noPerm < p
// @ preserves acc(param.Mem(), p)
func logDebugfSecureSessionRequest(log logger.T, formatStr string, param *mgsContracts.SecureSessionRequest /*@, ghost p perm @*/) {
	log.Debugf(formatStr, param)
}

// @ trusted
// @ requires acc(log.Mem(), _)
func logInfo(log logger.T, str string) {
	log.Info(str)
}

// @ trusted
// @ requires acc(log.Mem(), _)
func logInfofString(log logger.T, formatStr string, param string) {
	log.Infof(formatStr, param)
}

// @ trusted
// @ requires acc(log.Mem(), _)
func logWarnfActionType(log logger.T, formatStr string, param mgsContracts.ActionType) {
	log.Warnf(formatStr, param)
}

// @ trusted
// @ requires acc(log.Mem(), _) && noPerm < p
// @ preserves acc(param.ErrorMem(), p)
func logError(log logger.T, param error /*@, ghost p perm @*/) {
	log.Error(param)
}

// @ trusted
// @ requires acc(log.Mem(), _) && noPerm < p
// @ preserves acc(param.ErrorMem(), p)
func logErrorf(log logger.T, formatStr string, param error /*@, ghost p perm @*/) {
	log.Errorf(formatStr, param)
}

// @ trusted
// @ requires noPerm < p && acc(param.ErrorMem(), p)
// @ ensures err != nil && acc(err.ErrorMem(), p)
func fmtErrorf(format string, param error /*@, ghost p perm @*/) (err error) {
	return fmt.Errorf(format, param)
}

// @ trusted
// @ ensures err != nil && err.ErrorMem()
func fmtError(str string) (err error) {
	return fmt.Errorf(str)
}

// @ trusted
// @ ensures err != nil && err.ErrorMem()
func fmtErrorfState(format string, param DataChannelState) (err error) {
	return fmt.Errorf(format, param)
}

// @ trusted
// @ ensures err != nil && err.ErrorMem()
func fmtErrorfPayloadType(format string, param mgsContracts.PayloadType) (err error) {
	return fmt.Errorf(format, param)
}

// @ trusted
// @ requires noPerm < p && acc(param2.ErrorMem(), p)
// @ ensures err != nil && acc(err.ErrorMem(), p)
func fmtErrorfInt64Err(format string, param1 int64, param2 error /*@, ghost p perm @*/) (err error) {
	return fmt.Errorf(format, param1, param2)
}

// @ trusted
// @ ensures err != nil && err.ErrorMem()
func fmtErrorfActionTypeActionStatusActionError(format string, param1 mgsContracts.ActionType, param2 mgsContracts.ActionStatus, param3 string) (err error) {
	return fmt.Errorf(format, param1, param2, param3)
}

// @ trusted
// @ requires noPerm < p && acc(bytes.SliceMem(param1), p) && acc(bytes.SliceMem(param2), p)
// @ ensures err != nil && acc(err.ErrorMem(), p)
func fmtErrorfBytes2(format string, param1 []byte, param2 []byte /*@, ghost p perm @*/) (err error) {
	return fmt.Errorf(format, param1, param2)
}

// @ trusted
// @ requires noPerm < p && acc(param.Mem(), p)
// @ ensures err != nil && acc(err.ErrorMem(), p)
func fmtErrorfMetadata(format string, param *kms.KeyMetadata /*@, ghost p perm @*/) (err error) {
	return fmt.Errorf(format, param)
}

// @ trusted
// @ requires noPerm < p && acc(param1.Mem(), p) && acc(param2.ErrorMem(), p)
// @ ensures err != nil && acc(err.ErrorMem(), p)
func fmtErrorfHandshakeRequestErr(format string, param1 *mgsContracts.HandshakeRequestPayload, param2 error /*@, ghost p perm @*/) (err error) {
	return fmt.Errorf(format, param1, param2)
}

// @ trusted
// @ requires noPerm < p && acc(param1.Mem(), p) && acc(param2.ErrorMem(), p)
// @ ensures err != nil && acc(err.ErrorMem(), p)
func fmtErrorfHandshakeCompleteErr(format string, param1 *mgsContracts.HandshakeCompletePayload, param2 error /*@, ghost p perm @*/) (err error) {
	return fmt.Errorf(format, param1, param2)
}
