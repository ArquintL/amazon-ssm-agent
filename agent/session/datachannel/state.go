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
	IODistributed               DataChannelState = 11
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
	// kmsService is the KMS service used to sign and verify the handshake keyshare
	kmsService *crypto.KMSService
	// Indicates whether encryption was enabled
	encryptionEnabled     bool
	separateOutputPayload bool
	secrets               agentHandshakeSecrets
	logReaderId           string
	logLTPk               *rsa.PublicKey

	// TODO: mark the following fields as ghost as soon as Gobra supports ghost fields
	//@ msgHandlerCtx StreamDataHandlerContext
	//@ ioLock *sync.Mutex
	//@ ioLockDidLocalReceive bool
	//@ ioLockCanRemoteSend bool
	//@ ioLockDidRemoteReceive bool
	//@ ioLockCanLocalSend bool
}

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

// sanitizeStr sanitizes a secret that is a string.
// This is used to ignore safe calls to I/O-performing functions when applying the taint analysis.
// NOTE Currently it is impossible to sanitize slices because they are reference types.
func sanitizeStr(s string) string {
	return s
}

type InputStreamMessageHandler = func(streamDataMessage *mgsContracts.AgentMessage /*@, ghost t pl.Place, ghost rid tm.Term, ghost agentMessageT tm.Term @*/) error

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
// 		by.gamma(dc.getLogLTPkT()) == dc.logLTPk.Abs()) &&
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
	dc.encryptionEnabled == assumeEncryptionEnabledForVerification() &&
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
