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
	//@ abs "github.com/aws/amazon-ssm-agent/agent/iospecs/abs"
	//@ arb "github.com/aws/amazon-ssm-agent/agent/iospecs/arb"
	//@ by "github.com/aws/amazon-ssm-agent/agent/iospecs/bytes"
	//@ cl "github.com/aws/amazon-ssm-agent/agent/iospecs/claim"
	//@ ft "github.com/aws/amazon-ssm-agent/agent/iospecs/fact"
	//@ "github.com/aws/amazon-ssm-agent/agent/iospecs/iospec"
	//@ pl "github.com/aws/amazon-ssm-agent/agent/iospecs/place"
	//@ pub "github.com/aws/amazon-ssm-agent/agent/iospecs/pub"
	//@ tm "github.com/aws/amazon-ssm-agent/agent/iospecs/term"
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

	//@ requires log != nil
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

// instruct Gobra to prove that DataChannel is a behavioral subtype of IDataChannel:
/* TODO remove impl proof but leave implements clause
(* dataChannel) implements IDataChannel {
	(dc *dataChannel) SendStreamDataMessage(log logger.T, dataType mgsContracts.PayloadType, inputData []byte, ghost p perm, ghost inputDataT tm.Term) error {
		// assert (forall t pl.Place, rid tm.Term :: (pl.token(t) && iospec.e_InFact(t, rid)) --* (acc(bytes.SliceMem(inputData), p) && by.gamma(inputDataT) == abs.Abs(inputData) && pl.token(old[#lhs](iospec.get_e_InFact_placeDst(t, rid)))))
		unfold SendStreamDataMessageWand(t, rid, inputData, inputDataT, p)
		return dc.SendStreamDataMessage(log, dataType, inputData, p, inputDataT)
	}
}
*/

type DataChannelState int

const (
	Erroneous                   DataChannelState = 0
	Uninitialized               DataChannelState = 1
	Initialized                 DataChannelState = 2
	HandshakeSkipped            DataChannelState = 3
	BlockCipherInitialized      DataChannelState = 4
	AgentSecretCreatedAndSigned DataChannelState = 5
	HandshakeRequestSent        DataChannelState = 6
	BlockCipherReady            DataChannelState = 7
	HandshakeCompleted          DataChannelState = 8
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
type MessageReceptionPayload struct {
	status MessageReceptionStatus
	data   interface{}
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
	responseChan chan bool
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
preserves ctx.Inv() && acc(log.Mem(), _)
ensures err != nil ==> err.ErrorMem()
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
		dc.dataStream.Mem() &&
		dc.state.kmsService.Mem() &&
		dc.logLTPk.Mem() &&
		dc.IoSpecMem() &&
		pl.token(dc.getToken()) &&
		iospec.P_Agent(dc.getToken(), dc.getRid(), dc.getAbsState()) &&
		tm.pubTerm(pub.pub_msg(dc.dataStream.GetClientId())) == dc.getClientIdT() &&
		tm.pubTerm(pub.pub_msg(dc.logReaderId)) == dc.getReaderIdT()) &&
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
		dc.encryptionEnabled == assumeEncryptionEnabledForVerification() &&
		dc.blockCipher != nil && dc.blockCipher.Mem()) &&
	(dc.dataChannelState >= AgentSecretCreatedAndSigned && dc.dataChannelState < HandshakeCompleted ==>
		bytes.SliceMem(dc.state.agentSecret)) &&
	(dc.dataChannelState >= BlockCipherReady ==>
		(dc.encryptionEnabled ==> dc.blockCipher.IsReady())) &&
	(dc.dataChannelState >= HandshakeCompleted ==>
		exists AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, x, SigX, ClientLtKeyId, Y, SigY, SigSessionKey tm.Term :: ft.St_Agent_10(dc.getRid(), AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, x, SigX, ClientLtKeyId, Y, SigY, SigSessionKey) in dc.getAbsState() && tm.kdf1(tm.exp(Y, x)) == dc.blockCipher.GetEncKeyT()) &&
	// relate state to abstract state:
	(dc.dataChannelState == Initialized || dc.dataChannelState == BlockCipherInitialized ==>
		ft.Setup_Agent(dc.getRid(), dc.getAgentIdT(), dc.getKMSIdT(), dc.getClientIdT(), dc.getReaderIdT(), tm.pubTerm(pub.pub_msg(dc.agentLTKeyARN)), dc.getLogLTPkT()) in dc.getAbsState()) &&
	(dc.dataChannelState == AgentSecretCreatedAndSigned ==>
		ft.St_Agent_2(dc.getRid(), dc.getAgentIdT(), dc.getKMSIdT(), dc.getClientIdT(), dc.getReaderIdT(), tm.pubTerm(pub.pub_msg(dc.agentLTKeyARN)), dc.getLogLTPkT(), dc.getAgentShareT(), dc.getAgentShareSignatureT()) in dc.getAbsState()) &&
	(dc.dataChannelState == HandshakeRequestSent ==>
		ft.St_Agent_3(dc.getRid(), dc.getAgentIdT(), dc.getKMSIdT(), dc.getClientIdT(), dc.getReaderIdT(), tm.pubTerm(pub.pub_msg(dc.agentLTKeyARN)), dc.getLogLTPkT(), dc.getAgentShareT(), dc.getAgentShareSignatureT()) in dc.getAbsState())
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
	dc.encryptionEnabled == assumeEncryptionEnabledForVerification() &&
	dc.blockCipher != nil && dc.blockCipher.Mem() &&
	dc.IoSpecMem() &&
	pl.token(dc.getToken()) &&
	iospec.P_Agent(dc.getToken(), dc.getRid(), dc.getAbsState()) &&
	(encryptionEnabled ==>
		dc.logLTPk.Mem() &&
		dc.state.kmsService.Mem() &&
		bytes.SliceMem(dc.state.agentSecret))
}

pred (dc *dataChannel) Inv() {
	dc.RecvRoutineMem()
}

pred StartReceivingChanInv(dc *dataChannel, payload MessageReceptionPayload) {
	(payload.status == ReceiveHandshakeResponeEncryptionEnabled ||
		payload.status == ReceiveHandshakeResponeEncryptionDisabled ||
		payload.status == ReceiveOtherResponse) &&
	(payload.status == ReceiveHandshakeResponeEncryptionEnabled ==> dc.MemTransfer(true)) &&
	(payload.status == ReceiveHandshakeResponeEncryptionDisabled ==> dc.MemTransfer(false) && !assumeEncryptionEnabledForVerification()) &&
	(payload.status == ReceiveOtherResponse ==> acc(dc.Mem(), 1/2) &&
		dc.getState() == AgentSecretCreatedAndSigned &&
		unfolding acc(dc.Mem(), 1/2) in dc.hs.complete)
}

pred ResponseChanInv(dc *dataChannel, encryptionEnabled bool) {
	dc.MemTransfer(encryptionEnabled)
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
	dc.InFactTMem()
}

pred (dc *dataChannel) TokenMem()

ghost
requires acc(dc.TokenMem(), _)
pure func (dc *dataChannel) getTokenInternal() pl.Place

ghost
requires acc(dc.IoSpecMem(), _)
pure func (dc *dataChannel) getToken() pl.Place {
	return unfolding acc(dc.IoSpecMem(), _) in dc.getTokenInternal()
}

ghost
requires acc(dc.Mem(), _) && dc.getState() >= Initialized
pure func (dc *dataChannel) GetToken() pl.Place {
	return unfolding acc(dc.Mem(), _) in dc.getToken()
}

ghost
preserves dc.TokenMem()
ensures dc.getTokenInternal() == token
// ensures getRid(sessionId) == old(getRid(sessionId))
// ensures getAbsState(sessionId) == old(getAbsState(sessionId))
func (dc *dataChannel) setToken(token pl.Place)

pred (dc *dataChannel) RidMem()

ghost
requires acc(dc.RidMem(), _)
pure func (dc *dataChannel) getRidInternal() tm.Term

ghost
requires acc(dc.IoSpecMem(), _)
pure func (dc *dataChannel) getRid() tm.Term {
	return unfolding acc(dc.IoSpecMem(), _) in dc.getRidInternal()
}

ghost
requires acc(dc.Mem(), _) && dc.getState() >= Initialized
pure func (dc *dataChannel) GetRid() tm.Term {
	return unfolding acc(dc.Mem(), _) in dc.getRid()
}

ghost
preserves dc.RidMem()
ensures dc.getRidInternal() == rid
// ensures getAbsState(sessionId) == old(getAbsState(sessionId))
// ensures getToken(sessionId) == old(getToken(sessionId))
func (dc *dataChannel) setRid(rid tm.Term)

pred (dc *dataChannel) AbsStateMem()

ghost
requires acc(dc.AbsStateMem(), _)
pure func (dc *dataChannel) getAbsStateInternal() mset[ft.Fact]

ghost
requires acc(dc.IoSpecMem(), _)
pure func (dc *dataChannel) getAbsState() mset[ft.Fact] {
	return unfolding acc(dc.IoSpecMem(), _) in dc.getAbsStateInternal()
}

ghost
requires acc(dc.Mem(), _) && dc.getState() >= Initialized
pure func (dc *dataChannel) GetAbsState() mset[ft.Fact] {
	return unfolding acc(dc.Mem(), _) in dc.getAbsState()
}

ghost
preserves dc.AbsStateMem()
ensures dc.getAbsStateInternal() == state
// ensures getToken(sessionId) == old(getToken(sessionId))
// ensures getRid(sessionId) == old(getRid(sessionId))
func (dc *dataChannel) setAbsState(state mset[ft.Fact])

pred (dc *dataChannel) AgentIdTMem()

ghost
requires acc(dc.AgentIdTMem(), _)
pure func (dc *dataChannel) getAgentIdTInternal() tm.Term

ghost
requires acc(dc.IoSpecMem(), _)
pure func (dc *dataChannel) getAgentIdT() tm.Term {
	return unfolding acc(dc.IoSpecMem(), _) in dc.getAgentIdTInternal()
}

ghost
requires acc(dc.Mem(), _) && dc.getState() >= Initialized
pure func (dc *dataChannel) GetAgentIdT() tm.Term {
	return unfolding acc(dc.Mem(), _) in dc.getAgentIdT()
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
requires acc(dc.IoSpecMem(), _)
pure func (dc *dataChannel) getKMSIdT() tm.Term {
	return unfolding acc(dc.IoSpecMem(), _) in dc.getKMSIdTInternal()
}

ghost
requires acc(dc.Mem(), _) && dc.getState() >= Initialized
pure func (dc *dataChannel) GetKMSIdT() tm.Term {
	return unfolding acc(dc.Mem(), _) in dc.getKMSIdT()
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
requires acc(dc.IoSpecMem(), _)
pure func (dc *dataChannel) getClientIdT() tm.Term {
	return unfolding acc(dc.IoSpecMem(), _) in dc.getClientIdTInternal()
}

ghost
requires acc(dc.Mem(), _) && dc.getState() >= Initialized
pure func (dc *dataChannel) GetClientIdT() tm.Term {
	return unfolding acc(dc.Mem(), _) in dc.getClientIdT()
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
requires acc(dc.IoSpecMem(), _)
pure func (dc *dataChannel) getReaderIdT() tm.Term {
	return unfolding acc(dc.IoSpecMem(), _) in dc.getReaderIdTInternal()
}

ghost
requires acc(dc.Mem(), _) && dc.getState() >= Initialized
pure func (dc *dataChannel) GetReaderIdT() tm.Term {
	return unfolding acc(dc.Mem(), _) in dc.getReaderIdT()
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
requires acc(dc.IoSpecMem(), _)
pure func (dc *dataChannel) getLogLTPkT() tm.Term {
	return unfolding acc(dc.IoSpecMem(), _) in dc.getLogLTPkTInternal()
}

ghost
requires acc(dc.Mem(), _) && dc.getState() >= Initialized
pure func (dc *dataChannel) GetLogLTPkT() tm.Term {
	return unfolding acc(dc.Mem(), _) in dc.getLogLTPkT()
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
requires acc(dc.IoSpecMem(), _)
pure func (dc *dataChannel) getAgentShareT() tm.Term {
	return unfolding acc(dc.IoSpecMem(), _) in dc.getAgentShareTInternal()
}

ghost
requires acc(dc.Mem(), _) && dc.getState() >= Initialized
pure func (dc *dataChannel) GetAgentShareT() tm.Term {
	return unfolding acc(dc.Mem(), _) in dc.getAgentShareT()
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
requires acc(dc.IoSpecMem(), _)
pure func (dc *dataChannel) getAgentShareSignatureT() tm.Term {
	return unfolding acc(dc.IoSpecMem(), _) in dc.getAgentShareSignatureTInternal()
}

ghost
requires acc(dc.Mem(), _) && dc.getState() >= Initialized
pure func (dc *dataChannel) GetAgentShareSignatureT() tm.Term {
	return unfolding acc(dc.Mem(), _) in dc.getAgentShareSignatureT()
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
requires acc(dc.IoSpecMem(), _)
pure func (dc *dataChannel) getInFactT() tm.Term {
	return unfolding acc(dc.IoSpecMem(), _) in dc.getInFactTInternal()
}

ghost
requires acc(dc.Mem(), _) && dc.getState() >= Initialized
pure func (dc *dataChannel) GetInFactT() tm.Term {
	return unfolding acc(dc.Mem(), _) in dc.getInFactT()
}

ghost
preserves dc.InFactTMem()
ensures dc.getInFactTInternal() == inFactT
func (dc *dataChannel) setInFactT(inFactT tm.Term)

ghost
requires acc(dc.Mem(), _) && dc.getState() >= BlockCipherInitialized
pure func (dc *dataChannel) GetEncKeyT() tm.Term {
	return unfolding acc(dc.Mem(), _) in dc.blockCipher.GetEncKeyT()
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
		// @ ensures msg.Mem()
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
	dc.hs.responseChan = make(chan bool)
	//@ dc.hs.responseChan.Init(ResponseChanInv!<dc, _!>, PredTrue!<!>)
	// we allocate some ghost heap space:
	//@ inhale dc.IoSpecMem()
	//@ unfold dc.IoSpecMem()
	// the following assertion is needed:
	//@ assert dc.TokenMem()
	//@ dc.setToken(t0)
	//@ dc.setRid(rid)
	//@ dc.setAbsState(mset[ft.Fact]{})
	//@ fold dc.IoSpecMem()

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
// @ requires dc.IoSpecMem() && pl.token(dc.getToken()) && iospec.P_Agent(dc.getToken(), dc.getRid(), dc.getAbsState())
// @ ensures  dc.Mem()
// @ ensures  err == nil ==> dc.getState() == Initialized
func (dc *dataChannel) initialize(dataStream *datastream.DataStream, logReaderId string) (err error) {
	// @ unfold dc.Mem()
	dc.dataStream = dataStream
	dc.encryptionEnabled = false
	dc.hs.error = nil
	dc.hs.complete = false
	dc.hs.skipped = false
	dc.hs.handshakeEndTime = time.Now()
	dc.hs.handshakeStartTime = time.Now()
	dc.state.kmsService, err = dc.dataStream.GetKMSService( /*@ perm(1/2) @*/ )
	if err != nil {
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
	dc.agentLTKeyARN, dc.logLTPk, err = getInitialValues(dc.state.kmsService, dc.dataStream.GetClientId(), logReaderId /*@, t0, rid @*/)
	if err != nil {
		// @ fold iospec.phiRF_Agent_17(t0, rid, s0)
		// @ fold iospec.P_Agent(t0, rid, s0)
		// @ fold dc.Mem()
		return fmtErrorf("failed to initialize KMS service: %v", err /*@, perm(1/2) @*/)
	}

	// @ s1 := s0 union mset[ft.Fact]{ setupFact }
	// @ unfold dc.IoSpecMem()
	// @ dc.setToken(t1)
	// @ dc.setAbsState(s1)
	// @ dc.setAgentIdT(agentIdT)
	// @ dc.setKMSIdT(kmsIdT)
	// @ dc.setClientIdT(clientIdT)
	// @ dc.setReaderIdT(readerIdT)
	// @ dc.setLogLTPkT(logLTPkT)
	// @ fold dc.IoSpecMem()
	dc.logReaderId = logReaderId
	dc.dataChannelState = Initialized
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
// @	by.gamma(tm.pubTerm(pub.pub_msg(clientId))) == by.gamma(old(iospec.get_e_Setup_Agent_r3(t, rid))) &&
// @	by.gamma(tm.pubTerm(pub.pub_msg(logReaderId))) == by.gamma(old(iospec.get_e_Setup_Agent_r4(t, rid))) &&
// @	by.gamma(tm.pubTerm(pub.pub_msg(agentLTKeyARN))) == by.gamma(old(iospec.get_e_Setup_Agent_r5(t, rid))) &&
// @	logLTPk.Abs() == by.gamma(old(iospec.get_e_Setup_Agent_r6(t, rid)))
// Patern axiom applies locally:
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
func getInitialValues(kmsService *crypto.KMSService, clientId string, logReaderId string /*@, ghost t pl.Place, ghost rid tm.Term @*/) (agentLTKeyARN string, logLTPk *rsa.PublicKey, err error) {
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
	if dc.getState() < HandshakeCompleted {
		return fmtErrorfState("DataChannel is in an invalid state %d", dc.getState())
	}

	if payloadType != mgsContracts.Output && payloadType != mgsContracts.StdErr && payloadType != mgsContracts.ExitCode {
		return fmtErrorfPayloadType("Rejecting stream data message with payload type %d as it would otherwise be sent in plaintext", payloadType)
	}

	//@ unfold dc.Mem()
	//@ t0 := dc.getToken()
	//@ rid := dc.getRid()
	//@ s0 := dc.getAbsState()

	// receive `inputData` from environment:
	//@ unfold iospec.P_Agent(t0, rid, s0)
	//@ unfold iospec.phiRF_Agent_16(t0, rid, s0)
	//@ t1 := iospec.get_e_InFact_placeDst(t0, rid)
	//@ s1 := s0 union mset[ft.Fact]{ ft.InFact_Agent(rid, iospec.get_e_InFact_r1(t0, rid)) }
	//@ unfold QuantifiedSendStreamDataMessageWand(inputData, inputDataT, p)
	//@ unfold SendStreamDataMessageWand(t0, rid, inputData, inputDataT, p)
	//@ apply (pl.token(t0) && iospec.e_InFact(t0, rid)) --* (acc(bytes.SliceMem(inputData), p) && by.gamma(inputDataT) == abs.Abs(inputData) && inputDataT == old[#lhs](iospec.get_e_InFact_r1(t0, rid)) && pl.token(old[#lhs](iospec.get_e_InFact_placeDst(t0, rid))))

	// obtain permission to send the ciphertext containing `inputData`:
	//@ assert exists AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, x, SigX, ClientLtKeyId, Y, SigY, SigSessionKey tm.Term :: ft.St_Agent_10(dc.getRid(), AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, x, SigX, ClientLtKeyId, Y, SigY, SigSessionKey) in s0 && tm.kdf1(tm.exp(Y, x)) == dc.blockCipher.GetEncKeyT()
	// existential elimination:
	//@ AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, x, SigX, ClientLtKeyId, Y, SigY, SigSessionKey := arb.GetArbTerm(), arb.GetArbTerm(), arb.GetArbTerm(), arb.GetArbTerm(), arb.GetArbTerm(), arb.GetArbTerm(), arb.GetArbTerm(), arb.GetArbTerm(), arb.GetArbTerm(), arb.GetArbTerm(), arb.GetArbTerm(), arb.GetArbTerm()
	//@ assume ft.St_Agent_10(dc.getRid(), AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, x, SigX, ClientLtKeyId, Y, SigY, SigSessionKey) in s0 && tm.kdf1(tm.exp(Y, x)) == dc.blockCipher.GetEncKeyT()
	/*@
		l := mset[ft.Fact] {
			ft.St_Agent_10(rid, AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, x, SigX, ClientLtKeyId, Y, SigY, SigSessionKey),
			ft.InFact_Agent(rid, inputDataT),
		}
		a := mset[cl.Claim] {
			cl.AgentSendLoop(rid, AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, x, ClientLtKeyId, Y),
		}
		r := mset[ft.Fact] {
	    	ft.St_Agent_10(rid, AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, x, SigX, ClientLtKeyId, Y, SigY, SigSessionKey),
	        ft.OutFact_Agent(rid, tm.pair(tm.pubTerm(pub.const_Message_pub()), tm.senc(inputDataT, tm.kdf1(tm.exp(Y, x))))),
	        ft.OutFact_Agent(rid, tm.pair(tm.pubTerm(pub.const_Log_pub()), tm.pair(tm.pubTerm(pub.const_Message_pub()), tm.senc(inputDataT, tm.kdf1(tm.exp(Y, x)))))),
		}
		@*/
	//@ unfold iospec.P_Agent(t1, rid, s1)
	//@ unfold iospec.phiR_Agent_11(t1, rid, s1)
	//@ t2 := iospec.get_e_Agent_SendMessages_placeDst(t1, rid, AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, x, SigX, ClientLtKeyId, Y, SigY, SigSessionKey, inputDataT, l, a, r)
	//@ s2 := ft.U(l, r, s1)
	//@ unfold dc.IoSpecMem()
	//@ dc.setToken(t2)
	//@ dc.setAbsState(s2)
	//@ fold dc.IoSpecMem()
	//@ iospec.internBIO_e_Agent_SendMessages(t1, rid, AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, x, SigX, ClientLtKeyId, Y, SigY, SigSessionKey, inputDataT, l, a, r)
	// the following assert stmt is necessary:
	//@ assert ft.St_Agent_10(rid, AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, x, SigX, ClientLtKeyId, Y, SigY, SigSessionKey) in s2
	//@ fold dc.Mem()

	if len(inputData) == 0 {
		logDebugfPayloadType(log, "Ignoring empty stream data payload. PayloadType: %d", payloadType)
		return nil
	}

	return dc.sendData(log, payloadType, inputData /*@, p/2, inputDataT @*/)
}

// @ requires log != nil && noPerm < p && p <= writePerm
// @ requires dc.Mem()
// @ requires dc.getState() >= (payloadType == mgsContracts.Output || payloadType == mgsContracts.StdErr || payloadType == mgsContracts.ExitCode || payloadType == mgsContracts.HandshakeComplete ? BlockCipherReady : BlockCipherInitialized)
// @ requires acc(bytes.SliceMem(inputData), p) && by.gamma(inputDataT) == abs.Abs(inputData)
// @ requires (payloadType == mgsContracts.Output || payloadType == mgsContracts.StdErr || payloadType == mgsContracts.ExitCode || payloadType == mgsContracts.HandshakeComplete) ?
// @ 	ft.OutFact_Agent(dc.GetRid(), tm.pair(mgsContracts.payloadTypeTerm(payloadType), tm.senc(inputDataT, dc.GetEncKeyT()))) # dc.GetAbsState() > 0 :
// @ 	ft.OutFact_Agent(dc.GetRid(), tm.pair(mgsContracts.payloadTypeTerm(payloadType), inputDataT)) # dc.GetAbsState() > 0
// @ preserves acc(log.Mem(), _)
// @ ensures dc.Mem() && dc.getState() == old(dc.getState())
// @ ensures err != nil ==> err.ErrorMem()
func (dc *dataChannel) sendData(log logger.T, payloadType mgsContracts.PayloadType, inputData []byte /*@, ghost p perm, ghost inputDataT tm.Term @*/) (err error) {
	// @ oldState := dc.getState()
	// @ unfold dc.Mem()
	// @ channelId := dc.dataStream.GetChannelId()

	// If encryption has been enabled, encrypt the payload
	if dc.encryptionEnabled && (payloadType == mgsContracts.Output || payloadType == mgsContracts.StdErr || payloadType == mgsContracts.ExitCode || payloadType == mgsContracts.HandshakeComplete) {
		if inputData, err = dc.blockCipher.EncryptWithAESGCM(inputData /*@, p/2 @*/); err != nil {
			err = fmtErrorfInt64Err("error encrypting stream data message sequence %d, err: %v", dc.dataStream.GetStreamDataSequenceNumber( /*@ p/2 @*/ ), err /*@, perm(1/1) @*/)
			// @ fold dc.Mem()
			return
		}
		//@ inputDataT = tm.senc(inputDataT, dc.blockCipher.GetEncKeyT())
	}

	/*@
	t0 := dc.getToken()
	rid := dc.getRid()
	s0 := dc.getAbsState()
	m := tm.pair(mgsContracts.payloadTypeTerm(payloadType), inputDataT)
	unfold iospec.P_Agent(t0, rid, s0)
	unfold iospec.phiRG_Agent_13(t0, rid, s0)
	@*/

	/*@
	// existential elimination:
	AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, x, SigX, ClientLtKeyId, Y, SigY, SigSessionKey := arb.GetArbTerm(), arb.GetArbTerm(), arb.GetArbTerm(), arb.GetArbTerm(), arb.GetArbTerm(), arb.GetArbTerm(), arb.GetArbTerm(), arb.GetArbTerm(), arb.GetArbTerm(), arb.GetArbTerm(), arb.GetArbTerm(), arb.GetArbTerm()
	ghost if dc.dataChannelState >= HandshakeCompleted {
		assert exists AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, x, SigX, ClientLtKeyId, Y, SigY, SigSessionKey tm.Term :: ft.St_Agent_10(dc.getRid(), AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, x, SigX, ClientLtKeyId, Y, SigY, SigSessionKey) in s0 && tm.kdf1(tm.exp(Y, x)) == dc.blockCipher.GetEncKeyT()
		assume ft.St_Agent_10(dc.getRid(), AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, x, SigX, ClientLtKeyId, Y, SigY, SigSessionKey) in s0 && tm.kdf1(tm.exp(Y, x)) == dc.blockCipher.GetEncKeyT()
	}
	@*/

	//@ ghost var t1 pl.Place
	err /*@, t1 @*/ = dc.dataStream.Send(log, payloadType, inputData /*@, p/2, t0, rid, inputDataT, m @*/)
	if err != nil {
		// @ fold iospec.phiRG_Agent_13(t0, rid, s0)
		// @ fold iospec.P_Agent(t0, rid, s0)
		// @ fold dc.Mem()
		return err
	}
	// @ unfold dc.IoSpecMem()
	// @ dc.setToken(t1)
	// @ s1 := s0 setminus mset[ft.Fact]{ ft.OutFact_Agent(rid, m) }
	// @ dc.setAbsState(s1)
	// @ fold dc.IoSpecMem()
	/*@
	ghost if dc.dataChannelState >= HandshakeCompleted {
		// the following assert stmt is necessary:
		assert ft.St_Agent_10(dc.getRid(), AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, x, SigX, ClientLtKeyId, Y, SigY, SigSessionKey) in s1
	}
	@*/
	// @ fold dc.Mem()
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
// @ ensures  err == nil ==> ResponseChanInv!<dc, _!>(res)
// @ ensures  err != nil ==> err.ErrorMem()
func (dc *dataChannel) tryReceiveResponse(timeout time.Duration /*@, ghost p perm @*/) (res bool, err error) {
	var ok bool
	select {
	case res, ok = <-dc.hs.responseChan:
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
// @ ensures  err == nil ==> ResponseChanInv!<dc, _!>(res)
// @ ensures  err != nil ==> err.ErrorMem()
func (dc *dataChannel) tryReceiveResponseAlt(responseChan chan bool, timeout time.Duration) (res bool, err error) {
	var ok bool
	select {
	case res, ok = <-responseChan:
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
ensures  err == nil ==> ResponseChanInv!<dc, _!>(res)
ensures  err != nil ==> err.ErrorMem()
func (dc *dataChannel) tryReceiveResponseModel(timeout time.Duration, ghost p perm) (res bool, err error) {
	if nonDeterministicChoice() {
		unfold acc(dc.Mem(), p)
		fold PredTrue!<!>()
		var ok bool
		res, ok = <-dc.hs.responseChan
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
ensures  err == nil ==> ResponseChanInv!<dc, _!>(res)
ensures  err != nil ==> err.ErrorMem()
func (dc *dataChannel) tryReceiveResponseModelAlt(responseChan chan bool, timeout time.Duration, ghost p perm) (res bool, err error) {
	if nonDeterministicChoice() {
		fold PredTrue!<!>()
		var ok bool
		res, ok = <-responseChan
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
		//@ unfold dc.MemTransfer(true)
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
		//@ unfold dc.IoSpecMem()
		//@ dc.setToken(t1)
		//@ dc.setAbsState(s1)
		//@ dc.setInFactT(receivedMsgT)
		//@ fold dc.IoSpecMem()
		//@ assert by.gamma(receivedMsgT) == streamDataMessage.Abs()
		//@ fold dc.MemTransfer(true)
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
		// the problem is that dc.Mem() is shared between the two threads
		// thus, we have to remove IO spec from Mem at the end of the handshake and share it
		// with both threads using a ghost lock
		//@ unfold acc(dc.Mem(), 1/2)
		//@ unfold streamDataMessage.Mem()
		if dc.encryptionEnabled && streamDataMessage.PayloadType == uint32(mgsContracts.Output) {
			plaintext, err := dc.blockCipher.DecryptWithAESGCM(streamDataMessage.Payload /*@, perm(1/2) @*/)
			if err != nil {
				// send a message to the channel to prepare for next message reception:
				//@ fold acc(dc.Mem(), 1/2)
				dc.resendReceiveOtherResponse()
				err = fmtErrorfInt64Err("Error decrypting stream data message sequence %d, err: %v", streamDataMessage.SequenceNumber, err /*@, perm(1/1) @*/)
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

// @ requires acc(dc.Mem(), 1/2) && dc.getState() == AgentSecretCreatedAndSigned && unfolding acc(dc.Mem(), 1/2) in dc.hs.complete
// @ preserves dc.RecvRoutineMem()
func (dc *dataChannel) resendReceiveOtherResponse() {
	//@ unfold acc(dc.Mem(), 1/2)
	//@ unfold dc.RecvRoutineMem()
	//@ fold acc(dc.Mem(), 1/2)
	payload := MessageReceptionPayload{
		status: ReceiveOtherResponse,
	}
	//@ fold StartReceivingChanInv!<dc, _!>(payload)
	dc.hs.startReceivingChan <- payload
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

/*@
ghost
requires endIdx <= len(actions)
requires forall i int :: { actions[i] } 0 <= i && i < len(actions) ==> acc(actions[i].Mem(), _)
decreases endIdx
pure func secSessionNotFoundBelow(actions []mgsContracts.ProcessedClientAction, endIdx int) bool {
	return endIdx <= 0 ||
		!actions[endIdx - 1].IsSuccessfulSecureSession() && secSessionNotFoundBelow(actions, endIdx - 1)
}

ghost
requires noPerm < p
requires 0 <= idx && idx < len(actions)
requires forall i int :: { actions[i] } 0 <= i && i < len(actions) ==> acc(actions[i].Mem(), p)
requires secSessionNotFoundBelow(actions, idx)
requires actions[idx].IsSuccessfulSecureSession()
ensures  forall i int :: { actions[i] } 0 <= i && i < len(actions) ==> acc(actions[i].Mem(), p)
ensures  mgsContracts.containsSecureSession(actions, 0)
ensures  mgsContracts.getSecureSessionIndex(actions, 0) == idx
func containsSecureSessionLemma(actions []mgsContracts.ProcessedClientAction, idx int, p perm) {
	containsSecureSessionHelperLemma(actions, idx, p, 0)
}

ghost
requires noPerm < p
requires 0 <= startIdx && startIdx <= idx && idx < len(actions)
requires forall i int :: { actions[i] } 0 <= i && i < len(actions) ==> acc(actions[i].Mem(), p)
requires secSessionNotFoundBelow(actions, idx)
requires actions[idx].IsSuccessfulSecureSession()
ensures  forall i int :: { actions[i] } 0 <= i && i < len(actions) ==> acc(actions[i].Mem(), p)
ensures  mgsContracts.containsSecureSession(actions, startIdx)
ensures  mgsContracts.getSecureSessionIndex(actions, startIdx) == idx
decreases len(actions) - startIdx
func containsSecureSessionHelperLemma(actions []mgsContracts.ProcessedClientAction, idx int, p perm, startIdx int) {
	if startIdx != idx {
		containsSecureSessionHelperLemma(actions, idx, p/2, startIdx + 1)
		secSessionNotFoundLemma(actions, idx, p/2, startIdx)
	}
}

ghost
requires noPerm < p
requires 0 <= startIdx && startIdx < idx && idx < len(actions)
requires forall i int :: { actions[i] } 0 <= i && i < len(actions) ==> acc(actions[i].Mem(), p)
requires secSessionNotFoundBelow(actions, idx)
ensures  forall i int :: { actions[i] } 0 <= i && i < len(actions) ==> acc(actions[i].Mem(), p)
ensures  !actions[startIdx].IsSuccessfulSecureSession()
decreases idx
func secSessionNotFoundLemma(actions []mgsContracts.ProcessedClientAction, idx int, p perm, startIdx int) {
	if startIdx + 1 != idx {
		secSessionNotFoundLemma(actions, idx - 1, p/2, startIdx)
	}
}
@*/

/*
ghost
decreases
pure func IsSuccessfulSecureSession(action mgsContracts.ProcessedClientActionAdt) bool {
	return action.ActionType == mgsContracts.SecureSession &&
		action.ActionStatus == mgsContracts.Success
}

ghost
requires 0 <= startIdx && startIdx <= len(actions)
decreases len(actions) - startIdx
pure func containsSecureSession(actions seq[mgsContracts.ProcessedClientActionAdt], startIdx int) bool {
	return startIdx == len(actions) ? false :
		(IsSuccessfulSecureSession(actions[startIdx]) ?
			true : containsSecureSession(actions, startIdx + 1))
}

ghost
requires 0 <= startIdx && startIdx <= len(actions)
requires containsSecureSession(actions, startIdx)
ensures  startIdx <= res && res < len(actions)
ensures  IsSuccessfulSecureSession(actions[res])
decreases len(actions) - startIdx
pure func getSecureSessionIndex(actions seq[mgsContracts.ProcessedClientActionAdt], startIdx int) (res int) {
	return IsSuccessfulSecureSession(actions[startIdx]) ?
			startIdx : getSecureSessionIndex(actions, startIdx + 1)
}

ghost
requires endIdx <= len(actions)
decreases endIdx
pure func secSessionNotFoundBelow(actions seq[mgsContracts.ProcessedClientActionAdt], endIdx int) bool {
	return endIdx <= 0 ||
		(!IsSuccessfulSecureSession(actions[endIdx - 1]) &&
			secSessionNotFoundBelow(actions, endIdx - 1))
}

ghost
requires 0 <= idx && idx < len(actions)
requires secSessionNotFoundBelow(actions, idx)
requires IsSuccessfulSecureSession(actions[idx])
ensures  containsSecureSession(actions, 0)
ensures  getSecureSessionIndex(actions, 0) == idx
func containsSecureSessionLemma(actions seq[mgsContracts.ProcessedClientActionAdt], idx int) {
	containsSecureSessionHelperLemma(actions, idx, 0)
}

ghost
requires 0 <= startIdx && startIdx <= idx && idx < len(actions)
requires secSessionNotFoundBelow(actions, idx)
requires IsSuccessfulSecureSession(actions[idx])
ensures  containsSecureSession(actions, startIdx)
ensures  getSecureSessionIndex(actions, startIdx) == idx
decreases len(actions) - startIdx
func containsSecureSessionHelperLemma(actions seq[mgsContracts.ProcessedClientActionAdt], idx int, startIdx int) {
	if startIdx != idx {
		containsSecureSessionHelperLemma(actions, idx, startIdx + 1)
		secSessionNotFoundLemma(actions, idx, startIdx)
	}
}

ghost
requires 0 <= startIdx && startIdx < idx && idx < len(actions)
requires secSessionNotFoundBelow(actions, idx)
ensures  !IsSuccessfulSecureSession(actions[startIdx])
decreases idx
func secSessionNotFoundLemma(actions seq[mgsContracts.ProcessedClientActionAdt], idx int, startIdx int) {
	if startIdx + 1 != idx {
		secSessionNotFoundLemma(actions, idx - 1, startIdx)
	}
}

ghost
requires noPerm < p
requires acc(handshakeResponsePayload.Mem(), p)
requires 0 <= startIdx && startIdx <= unfolding acc(handshakeResponsePayload.Mem(), p) in len(handshakeResponsePayload.ProcessedClientActions)
ensures acc(handshakeResponsePayload.Mem(), p)
ensures unfolding acc(handshakeResponsePayload.Mem(), p) in
	let res := old(handshakeResponsePayload.Adt(startIdx)) in
	(len(res) == len(handshakeResponsePayload.ProcessedClientActions) - startIdx) &&
	(forall i int :: { res[i] } 0 <= i && i < len(res) ==> res[i] == handshakeResponsePayload.ProcessedClientActions[startIdx + i].Adt())
func HandshakeResponsePayloadAdtLemma(handshakeResponsePayload *mgsContracts.HandshakeResponsePayload, startIdx int, p perm) {
	actionsLen := unfolding acc(handshakeResponsePayload.Mem(), p/2) in len(handshakeResponsePayload.ProcessedClientActions)
	if startIdx != actionsLen {
		HandshakeResponsePayloadAdtLemma(handshakeResponsePayload, startIdx + 1, p/2)
	}
}
*/

// handleHandshakeResponse is the handler for payload type HandshakeResponse
// @ requires log != nil && dc.MemTransfer(encryptionEnabled)
// @ requires streamDataMessage.Mem()
// @ requires unfolding streamDataMessage.Mem() in mgsContracts.PayloadType(streamDataMessage.PayloadType) == mgsContracts.HandshakeResponse
// @ requires unfolding dc.MemTransfer(encryptionEnabled) in by.gamma(dc.getInFactT()) == streamDataMessage.Abs()
// @ preserves acc(log.Mem(), _) && dc.RecvRoutineMem()
// @ ensures  streamDataMessage.Mem()
// @ ensures  err != nil ==> err.ErrorMem()
func (dc *dataChannel) handleHandshakeResponse(log logger.T, streamDataMessage *mgsContracts.AgentMessage, encryptionEnabled bool) (err error) {
	logDebug(log, "Received Handshake Response.")
	// var handshakeResponse /*@ @ @*/ mgsContracts.HandshakeResponsePayload
	// fold handshakeResponse.Mem()
	//@ unfold streamDataMessage.Mem()
	// if err := json.Unmarshal(streamDataMessage.Payload, &handshakeResponse /*@, perm(1/2) @*/); err != nil {
	// 	//@ fold streamDataMessage.Mem()
	// 	return fmtErrorf("Unmarshalling of HandshakeResponse message failed, %s", err /*@, perm(1/1) @*/)
	// }
	handshakeResponse, err := unmarshalHandshakeResponse(streamDataMessage.Payload /*@, perm(1/2) @*/)
	if err != nil {
		//@ fold streamDataMessage.Mem()
		return fmtErrorf("Unmarshalling of HandshakeResponse message failed, %s", err /*@, perm(1/1) @*/)
	}
	//@ assert abs.Abs(streamDataMessage.Payload) == handshakeResponse.Abs()
	// assert handshakeResponse.ContainsSecureSession()
	// assert handshakeResponse.Abs() ==
	//@ ghost var firstActionAbs by.Bytes
	/*@
	ghost if handshakeResponse.ContainsSecureSession() {
		// assert unfolding handshakeResponse.Mem() in mgsContracts.containsSecureSession(handshakeResponse.ProcessedClientActions, 0)
		assert unfolding handshakeResponse.Mem() in len(handshakeResponse.ProcessedClientActions) == 1
		// firstActionAbs := unfolding handshakeResponse.Mem() in handshakeResponse.ProcessedClientActions[mgsContracts.getSecureSessionIndex(handshakeResponse.ProcessedClientActions, 0)].Abs()
		// assert abs.Abs(streamDataMessage.Payload) == by.pairB(by.gamma(tm.pubTerm(pub.const_SecureSessionResponse_pub())), firstActionAbs)
		firstActionAbs = unfolding handshakeResponse.Mem() in handshakeResponse.ProcessedClientActions[0].Abs()
		assert abs.Abs(streamDataMessage.Payload) == by.pairB(by.gamma(tm.pubTerm(pub.const_SecureSessionResponse_pub())), firstActionAbs)
	}
	@*/
	// assert abs.Abs(streamDataMessage.Payload) == by.pairB(by.gamma(tm.pubTerm(pub.const_SecureSessionResponse_pub())), handshakeResponse.Abs())
	//@ msgPayloadB := abs.Abs(streamDataMessage.Payload)
	//@ fold streamDataMessage.Mem()
	// absActions := handshakeResponse.Adt(0)
	// HandshakeResponsePayloadAdtLemma(handshakeResponse, 0, perm(1/2))
	//@ unfold handshakeResponse.Mem()

	i := 0
	actions := handshakeResponse.ProcessedClientActions
	// assert secSessionNotFoundBelow(actions, 0)
	// assert secSessionNotFoundBelow(absActions, 0)
	secureSessionActionIndex := -1
	//@ invariant 0 <= i &&  i <= len(actions)
	//@ invariant dc.MemTransfer(encryptionEnabled)
	//@ invariant acc(log.Mem(), _)
	//@ invariant acc(streamDataMessage.Mem(), 1/2)
	//@ invariant forall j int :: { actions[j] } 0 <= j && j < len(actions) ==> acc(actions[j].Mem(), 1/2) // && actions[j].Adt() == absActions[j]
	// invariant 0 <= secureSessionActionIndex ==>
	//		secureSessionActionIndex < len(actions) &&
	// 	mgsContracts.containsSecureSession(actions, 0) &&
	// 	mgsContracts.getSecureSessionIndex(actions, 0) == secureSessionActionIndex
	// invariant secureSessionActionIndex < 0 ==> (forall j int :: { !actions[j].IsSuccessfulSecureSession() } 0 <= j && j < i ==> !actions[j].IsSuccessfulSecureSession())
	// invariant secureSessionActionIndex < 0 ==> secSessionNotFoundBelow(actions, i)
	// invariant secureSessionActionIndex < 0 ==> secSessionNotFoundBelow(absActions, i)
	//@ invariant msgPayloadB == unfolding acc(streamDataMessage.Mem(), 1/2) in abs.Abs(streamDataMessage.Payload)
	//@ invariant mgsContracts.containsSecureSession(actions, 0) ==> firstActionAbs == actions[0].Abs()
	//@ invariant mgsContracts.containsSecureSession(actions, 0) ==>
	//@		(unfolding acc(streamDataMessage.Mem(), 1/2) in abs.Abs(streamDataMessage.Payload)) == by.pairB(by.gamma(tm.pubTerm(pub.const_SecureSessionResponse_pub())), actions[0].Abs())
	for i = range actions {
		//@ unfold acc(actions[i].Mem(), 1/2)
		action := actions[i]
		var err error
		if action.ActionStatus != mgsContracts.Success {
			err = fmtErrorfActionTypeActionStatusActionError("%s failed on client with status %v error: %s",
				action.ActionType, action.ActionStatus, action.Error)
			//@ fold acc(actions[i].Mem(), 1/2)
		} else {
			switch action.ActionType {
			case mgsContracts.SecureSession:
				//@ fold acc(actions[i].Mem(), 1/2)
				if secureSessionActionIndex < 0 {
					// this is the *first* action we found with matching type and status
					secureSessionActionIndex = i
					// assert i < len(actions)
					// assert actions[i].Type() == mgsContracts.SecureSession
					// assert actions[i].Status() == mgsContracts.Success
					//@ assert mgsContracts.containsSecureSession(actions, i)
					//@ containsSecureSessionLemma(actions, i, perm(1/2))
					// containsSecureSessionLemma(absActions, i)
					//@ assert mgsContracts.containsSecureSession(actions, 0)
					//@ assert mgsContracts.getSecureSessionIndex(actions, 0) == i
					// assert
				} else {
					// this is not necessarily true since the current index
					// could be a duplicate but successful secure session action:
					// assert secSessionNotFoundBelow(actions, i + 1)
				}

				if !encryptionEnabled {
					err = fmtError("unexpected action type 'SecureSession' because encryption is disabled")
					break
				}

				err = dc.processSecureSessionResponse(log, &actions[i])
				if err != nil {
					break
				}
			// case mgsContracts.KMSEncryption:
			// 	err = dc.finalizeKMSEncryption(log, action.ActionResult)
			// 	break
			case mgsContracts.SessionType:
				//@ fold acc(actions[i].Mem(), 1/2)
				break
			default:
				//@ fold acc(actions[i].Mem(), 1/2)
				logWarnfActionType(log, "Unknown handshake client action found, %s", action.ActionType)
			}
		}
		if err != nil {
			logError(log, err /*@, perm(1/1) @*/)
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
	logInfofString(log, "Client side session manager plugin version is: %s", handshakeResponse.ClientVersion)
	//@ fold dc.MemTransfer(encryptionEnabled)
	//@ fold ResponseChanInv!<dc, _!>(encryptionEnabled)
	//@ unfold dc.RecvRoutineMem()
	dc.hs.responseChan <- encryptionEnabled
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
// @ preserves dc.MemTransfer(true) && acc(log.Mem(), _) && acc(action.Mem(), 1/4) && action.IsSuccessfulSecureSession()
func (dc *dataChannel) processSecureSessionResponse(log logger.T, action *mgsContracts.ProcessedClientAction) (err error) {
	//@ unfold acc(action.Mem(), 1/4)
	resp, err := unmarshalSecureSessionResponse(action.ActionResult /*@, perm(1/8) @*/)
	//@ fold acc(action.Mem(), 1/4)
	if err != nil {
		return fmtErrorf("failed to unmarshal action to SecureSessionResponse: %v", err /*@, perm(1/1) @*/)
	}

	// decode the client share
	//@ unfold resp.Mem()
	//@ unfold dc.MemTransfer(true)
	sharedSecret, err /*@, clientSecretB @*/ := unmarshalAndCheckClientShare(resp.ClientShare, dc.state.agentSecret /*@, perm(1/2) @*/)
	if err != nil {
		logError(log, err /*@, perm(1/1) @*/)
		return err
	}

	//@ receivedMsgT := dc.getInFactT()
	// assert by.gamma(receivedMsgT) == by.gamma(Term_M2(rid, by.oneTerm(sidR), ltkT, pskT, ekiT, c3T, h4T, by.oneTerm(epkR), by.oneTerm(mac1), by.oneTerm(mac2)))
	//@ clientSecretT := by.oneTerm(clientSecretB)
	//@ xT := dc.getAgentShareT()
	//@ sigYB := by.msgB(resp.Signature)
	//@ sigYT := by.oneTerm(sigYB)
	//@ clientLtKeyIdB := by.msgB(resp.ClientLTKeyARN)
	//@ clientLtKeyIdT := by.oneTerm(clientLtKeyIdB)
	//@ assert by.gamma(receivedMsgT) == by.gamma(tm.pair(tm.pubTerm(pub.const_SecureSessionResponse_pub()), tm.pair(tm.exp(tm.pubTerm(pub.const_g_pub()), clientSecretT), tm.pair(sigYT, tm.pair(clientLtKeyIdT, tm.hash(tm.exp(tm.exp(tm.pubTerm(pub.const_g_pub()), clientSecretT), xT)))))))

	// verify client signature
	sig, err := base64.StdEncoding.DecodeString(resp.Signature)
	if err != nil {
		return fmtErrorf("failed to decode signature: %v", err /*@, perm(1/1) @*/)
	}

	agentId := dc.dataStream.GetInstanceId()
	//@ fold dc.MemTransfer(true)
	clientSignPayload := &mgsContracts.SignClientSharePayload{
		ClientShare: resp.ClientShare,
		AgentId:     agentId,
	}

	//@ fold clientSignPayload.Mem()
	clientSignPayloadBytes, err := json.Marshal(clientSignPayload /*@, perm(1/2) @*/)
	if err != nil {
		err = fmtErrorf("failed to encode client sign payload: %v", err /*@, perm(1/1) @*/)
		logError(log, err /*@, perm(1/1) @*/)
		return err
	}

	//@ unfold dc.MemTransfer(true)
	ok, err := dc.state.kmsService.Verify(resp.ClientLTKeyARN, clientSignPayloadBytes, sig /*@, perm(1/2) @*/)
	//@ fold dc.MemTransfer(true)
	if !ok {
		return fmtError("failed to verify signature")
	}
	if err != nil {
		return fmtErrorf("failed to verify signature: %v", err /*@, perm(1/1) @*/)
	}

	// generate and store the shared secret
	//@ unfold dc.MemTransfer(true)
	dc.state.sharedSecret = sharedSecret

	// hash the shared secret to obtain the session identifier
	dc.state.sessionID = computeSHA384(dc.state.sharedSecret /*@, 1/2 @*/)

	logDebugfString(log, "agent computed session ID: %v", base64.StdEncoding.EncodeToString(dc.state.sessionID /*@, perm(1/1) @*/))
	// decode the session ID
	var sessionIDBytes []byte
	sessionIDBytes, err = base64.StdEncoding.DecodeString(resp.SessionID)
	if err != nil {
		//@ fold dc.MemTransfer(true)
		err = fmtErrorf("failed to decode server session id: %v", err /*@, perm(1/1) @*/)
		logError(log, err /*@, perm(1/1) @*/)
		return err
	}

	if !bytes.Equal(dc.state.sessionID, sessionIDBytes) {
		err = fmtErrorfBytes2("session ID mismatch: session ID %s does not match client session ID %s", sessionIDBytes, dc.state.sessionID /*@, perm(1/1) @*/)
		//@ fold dc.MemTransfer(true)
		logError(log, err /*@, perm(1/1) @*/)
		return err
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
	logDebugfString(log, "agent read key: %s", encodedAgentReadKey)
	logDebugfString(log, "agent write key: %s", encodedAgentWriteKey)

	// create ciphertext containing session keys:
	sessionKeys := &mgsContracts.SessionKeys{
		AgentReadKey:  encodedAgentReadKey,
		AgentWriteKey: encodedAgentWriteKey,
	}
	//@ fold sessionKeys.Mem()
	sessionKeysBytes, err := json.Marshal(sessionKeys /*@, perm(1/2) @*/)
	if err != nil {
		err = fmtErrorf("failed to encode session keys: %v", err /*@, perm(1/1) @*/)
		logError(log, err /*@, perm(1/1) @*/)
		return err
	}

	//@ cryptoRand.GetReaderMem()
	encryptedSessionKeys, err := rsa.EncryptPKCS1v15(cryptoRand.Reader, dc.logLTPk, sessionKeysBytes /*@, perm(1/2) @*/)
	if err != nil {
		return fmtErrorf("failed to encrypt session keys: %v", err /*@, perm(1/1) @*/)
	}
	encodedEncryptedSessionKeys := base64.StdEncoding.EncodeToString(encryptedSessionKeys /*@, perm(1/2) @*/)
	logInfofString(log, "encrypted base-64-encoded session keys: %s", encodedEncryptedSessionKeys)

	// sign ciphertext containing session keys using KMS:
	signSessionKeysPayload := &mgsContracts.SignSessionKeysPayload{
		EncryptedSessionKeys: encodedEncryptedSessionKeys,
		ClientId:             dc.dataStream.GetClientId(),
	}

	//@ fold signSessionKeysPayload.Mem()
	signSessionKeysPayloadBytes, err := json.Marshal(signSessionKeysPayload /*@, perm(1/2) @*/)
	if err != nil {
		err = fmtErrorf("failed to encode sign session keys payload: %v", err /*@, perm(1/1) @*/)
		logError(log, err /*@, perm(1/1) @*/)
		return err
	}

	/*@
	ghost var t0 pl.Place
	ghost var rid, agentIdT, kmsId, messageT, m tm.Term
	@*/
	sigSessionKeys, err /*@, signatureT @*/ := dc.state.kmsService.Sign(dc.agentLTKeyARN, signSessionKeysPayloadBytes /*@, perm(1/2), t0, rid, agentIdT, kmsId, messageT, m @*/)
	if err != nil {
		err = fmtErrorf("failed to sign session keys payload: %v", err /*@, perm(1/1) @*/)
		logError(log, err /*@, perm(1/1) @*/)
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
		err = fmtErrorf("failed to encode encrypted session keys payload: %v", err /*@, perm(1/1) @*/)
		logError(log, err /*@, perm(1/1) @*/)
		return err
	}
	encodedEncryptedSessionKeysPayloadBytes := base64.StdEncoding.EncodeToString(encryptedSessionKeysPayloadBytes /*@, perm(1/2) @*/)
	logInfofString(log, "encrypted session keys payload that should be sent to log server: %s", encodedEncryptedSessionKeysPayloadBytes)

	// TODO: actually send `encodedEncryptedSessionKeysPayloadBytes` to the log server!

	dc.encryptionEnabled = true

	//@ ghost var readKeyT tm.Term
	//@ ghost var writeKeyT tm.Term
	if err = dc.blockCipher.UpdateEncryptionKeys(log, dc.state.agentReadKey, dc.state.agentWriteKey /*@, perm(1/2), readKeyT, writeKeyT @*/); err != nil {
		//@ fold dc.MemTransfer(true)
		err = fmtErrorf("failed to update block cipher: %v", err /*@, perm(1/1) @*/)
		logError(log, err /*@, perm(1/1) @*/)
		return err
	}
	//@ fold dc.MemTransfer(true)
	return nil
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
// @ requires encryptionEnabled == assumeEncryptionEnabledForVerification()
// @ preserves dc.Mem() && acc(log.Mem(), _)
// @ ensures err == nil ==> dc.getState() == HandshakeCompleted
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
	dc.dataChannelState = BlockCipherInitialized
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
	startReceivingChan := dc.hs.startReceivingChan
	responseChan := dc.hs.responseChan
	//@ fold dc.MemTransfer(encryptionEnabled)
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
	logDebug(log, "Handshake response received")

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
	logInfo(log, "Handshake successfully completed.")
	//@ fold dc.Mem()
	return
}

// buildHandshakeRequestPayload builds payload for HandshakeRequest
// @ requires log != nil && dc.Mem() && dc.getState() == BlockCipherInitialized
// @ preserves acc(log.Mem(), _)
// @ ensures  dc.Mem()
// @ ensures  err == nil ==> payload.Mem()
// @ ensures  err == nil && !encryptionRequested ==> dc.getState() == BlockCipherInitialized
// @ ensures  err == nil && encryptionRequested ==> dc.getState() == AgentSecretCreatedAndSigned
// @ ensures  err == nil && encryptionRequested ==> unfolding dc.Mem() in (
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
			//@ fold dc.Mem()
			logErrorf(log, "failed to generate client secret: %v", err /*@, perm(1/2) @*/)
			return nil, err
		}
		//@ s1 := s0 union mset[ft.Fact]{ ft.FrFact_Agent(rid, agentSecretT) }
		//@ unfold dc.IoSpecMem()
		//@ dc.setToken(t1)
		//@ dc.setAbsState(s1)
		//@ fold dc.IoSpecMem()

		dc.state.agentSecret = agentSecret

		clientId := dc.dataStream.GetClientId()
		signPayloadBytes, err := getSignPayloadBytes(compressedPublic, clientId, dc.logReaderId)
		if err != nil {
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
			dc.dataChannelState = Erroneous
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

		//@ unfold dc.IoSpecMem()
		//@ dc.setToken(t5)
		//@ dc.setAbsState(s5)
		//@ dc.setAgentShareT(agentSecretT)
		//@ dc.setAgentShareSignatureT(signatureT)
		//@ fold dc.IoSpecMem()
		dc.dataChannelState = AgentSecretCreatedAndSigned

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
func getSignPayloadBytes(compressedPublic string, clientId string, logReaderId string) (signPayloadBytes []byte, err error) {
	signPayload := &mgsContracts.SignAgentSharePayload{
		AgentShare:  compressedPublic,
		ClientId:    clientId,
		LogReaderId: logReaderId,
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
// @ requires unfolding dc.Mem() in dc.encryptionEnabled ==>
// @	dc.dataChannelState == AgentSecretCreatedAndSigned &&
// @	handshakeRequestPayload.ContainsSecureSessionAction(by.tuple4B(by.expB(by.generatorB(), by.gamma(dc.getAgentShareT())), by.gamma(dc.getAgentShareSignatureT()), by.msgB(dc.agentLTKeyARN), by.msgB(dc.logReaderId)))
// @ preserves acc(log.Mem(), _)
// @ ensures dc.Mem()
// @ ensures err == nil ==> dc.getState() == HandshakeRequestSent
func (dc *dataChannel) sendHandshakeRequest(log logger.T, handshakeRequestPayload *mgsContracts.HandshakeRequestPayload) (err error) {
	//@ secActionB := unfolding dc.Mem() in by.tuple4B(by.expB(by.generatorB(), by.gamma(dc.getAgentShareT())), by.gamma(dc.getAgentShareSignatureT()), by.msgB(dc.agentLTKeyARN), by.msgB(dc.logReaderId))
	var handshakeRequestPayloadBytes []byte
	if handshakeRequestPayloadBytes, err = marshalHandshakeRequest(handshakeRequestPayload /*@, perm(1/2), secActionB @*/); err != nil {
		return fmtErrorfHandshakeRequestErr("Could not serialize HandshakeRequest message %v, err: %s", handshakeRequestPayload, err /*@, perm(1/2) @*/)
	}

	logDebug(log, "Sending Handshake Request.")
	logTracefHandshakeRequestPayload(log, "Sending HandshakeRequest message with content %v", handshakeRequestPayload /*@, perm(1/2) @*/)
	//@ secActionT := unfolding dc.Mem() in tm.pair(tm.exp(tm.pubTerm(pub.const_g_pub()), dc.getAgentShareT()), tm.pair(dc.getAgentShareSignatureT(), tm.pair(tm.pubTerm(pub.pub_msg(dc.agentLTKeyARN)), tm.pubTerm(pub.pub_msg(dc.logReaderId)))))

	//@ unfold dc.Mem()
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
	//@ unfold dc.IoSpecMem()
	//@ dc.setToken(t1)
	//@ dc.setAbsState(s1)
	//@ fold dc.IoSpecMem()
	dc.dataChannelState = HandshakeRequestSent
	//@ fold dc.Mem()

	if err = dc.sendData(log, mgsContracts.HandshakeRequest, handshakeRequestPayloadBytes /*@, perm(1/2), secActionT @*/); err != nil {
		return fmtErrorf("Failed sending of HandshakeRequest message, err: %s", err /*@, perm(1/2) @*/)
	}
	return nil
}

// @ trusted
// @ requires noPerm < p
// @ requires acc(handshakeRequestPayload.Mem(), p)
// @ requires handshakeRequestPayload.ContainsSecureSessionAction(secActionB)
// @ ensures  acc(handshakeRequestPayload.Mem(), p)
// @ ensures  handshakeRequestPayload.ContainsSecureSessionAction(secActionB)
// @ ensures  err == nil ==> bytes.SliceMem(handshakeRequestPayloadBytes)
// @ ensures  err == nil ==> abs.Abs(handshakeRequestPayloadBytes) == handshakeRequestPayload.Abs(secActionB)
// @ ensures  err != nil ==> err.ErrorMem()
func marshalHandshakeRequest(handshakeRequestPayload *mgsContracts.HandshakeRequestPayload /*@, ghost p perm, ghost secActionB by.Bytes @*/) (handshakeRequestPayloadBytes []byte, err error) {
	return json.Marshal(handshakeRequestPayload /*@, p/2 @*/)
}

// sendHandshakeComplete sends handshake complete
// @ requires log != nil && handshakeCompletePayload.Mem()
// @ requires dc.Mem() && dc.getState() >= BlockCipherReady
// @ preserves acc(log.Mem(), _)
// @ ensures dc.Mem() && dc.getState() == old(dc.getState())
// @ ensures err != nil ==> err.ErrorMem()
func (dc *dataChannel) sendHandshakeComplete(log logger.T, handshakeCompletePayload *mgsContracts.HandshakeCompletePayload) (err error) {
	var handshakeCompletePayloadBytes []byte
	if handshakeCompletePayloadBytes, err = json.Marshal(handshakeCompletePayload /*@, perm(1/2) @*/); err != nil {
		return fmtErrorfHandshakeCompleteErr("Could not serialize HandshakeComplete message %v, err: %s", handshakeCompletePayload, err /*@, perm(1/1) @*/)
	}

	logDebug(log, "Sending HandshakeComplete.")
	logTracefHandshakeCompletePayload(log, "Sending HandshakeComplete message with content %v", handshakeCompletePayload /*@, perm(1/2) @*/)
	//@ ghost var inputDataT tm.Term
	if err = dc.sendData(log, mgsContracts.HandshakeComplete, handshakeCompletePayloadBytes /*@, perm(1/2), inputDataT @*/); err != nil {
		return err
	}
	return nil
}

// GetClientVersion returns version of the client
// @ requires noPerm < p
// @ preserves acc(dc.Mem(), p)
func (dc *dataChannel) GetClientVersion( /*@ ghost p perm @*/ ) (version string, err error) {
	if dc.getState() == Erroneous {
		err = fmtErrorfState("DataChannel is in an invalid state %d", dc.getState())
		return
	}
	return /*@ unfolding acc(dc.Mem(), p) in @*/ dc.hs.clientVersion, nil
}

// GetInstanceId returns id of the target
// @ requires noPerm < p
// @ preserves acc(dc.Mem(), p)
func (dc *dataChannel) GetInstanceId( /*@ ghost p perm @*/ ) (instanceId string, err error) {
	if dc.getState() < Initialized {
		err = fmtErrorfState("DataChannel is in an invalid state %d", dc.getState())
		return
	}
	return /*@ unfolding acc(dc.Mem(), p) in @*/ dc.dataStream.GetInstanceId(), nil
}

// GetRegion returns aws region of the target
// @ requires noPerm < p
// @ preserves acc(dc.Mem(), p)
func (dc *dataChannel) GetRegion( /*@ ghost p perm @*/ ) (region string, err error) {
	if dc.getState() < Initialized {
		err = fmtErrorfState("DataChannel is in an invalid state %d", dc.getState())
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
		err = fmtErrorfState("DataChannel is in an invalid state %d", dc.getState())
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
		err = fmtErrorfState("DataChannel is in an invalid state %d", dc.getState())
		return
	}
	return /*@ unfolding acc(dc.Mem(), _) in @*/ dc.separateOutputPayload, nil
}

// SetSeparateOutputPayload set separateOutputPayload value
// @ preserves dc.Mem()
// @ ensures dc.getState() == old(dc.getState())
func (dc *dataChannel) SetSeparateOutputPayload(separateOutputPayload bool) (err error) {
	if dc.getState() == Erroneous {
		err = fmtErrorfState("DataChannel is in an invalid state %d", dc.getState())
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
		err = fmtErrorfState("DataChannel is in an invalid state %d", dc.getState())
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
		err = fmtErrorfState("DataChannel is in an invalid state %d", dc.getState())
		return
	}
	//@ unfold dc.Mem()
	err = dc.dataStream.Close(log)
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
