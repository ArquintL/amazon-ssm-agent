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

/*@
// the body of this predicate is only provided for illustration purposes
// obtaining `bytes.SliceMem(inputData)` is however only possible by
// applying `SendStreamDataMessageViewShift` and, thus, giving up the
// corresponding token and fact.
pred SendStreamDataMessageViewShiftFootprint(inputData []byte) // {
// 	bytes.SliceMem(inputData)
// }

ghost
decreases
requires pl.token(t) && iospec.e_InFact(t, rid)
requires SendStreamDataMessageViewShiftFootprint(inputData)
ensures  pl.token(old(iospec.get_e_InFact_placeDst(t, rid)))
ensures  bytes.SliceMem(inputData) && by.gamma(inputDataT) == abs.Abs(inputData)
ensures  inputDataT == old(iospec.get_e_InFact_r1(t, rid))
func SendStreamDataMessageViewShift(t pl.Place, rid tm.Term, inputData []byte) (inputDataT tm.Term)
@*/

type IDataChannel interface {

	// @ pred Mem()

	// @ requires log != nil
	// @ requires SendStreamDataMessageViewShiftFootprint(inputData)
	// @ preserves Mem() && acc(log.Mem(), _)
	// @ ensures  err != nil ==> err.ErrorMem()
	// @ ensures  inputProcessed ? bytes.SliceMem(inputData) : SendStreamDataMessageViewShiftFootprint(inputData)
	SendStreamDataMessage(log logger.T, dataType mgsContracts.PayloadType, inputData []byte) (err error /*@, ghost inputProcessed bool @*/)

	// @ requires log != nil
	// @ preserves Mem() && acc(log.Mem(), _)
	// @ ensures  err != nil ==> err.ErrorMem()
	SendAgentSessionStateMessage(log logger.T, sessionStatus mgsContracts.SessionStatus) (err error)

	// @ requires log != nil
	// @ preserves Mem() && acc(log.Mem(), _)
	// @ ensures  err != nil ==> err.ErrorMem()
	SkipHandshake(log logger.T) (err error)

	// @ requires log != nil
	// @ requires encryptionEnabled == assumeEncryptionEnabledForVerification()
	// @ preserves Mem() && acc(log.Mem(), _) && sessionTypeRequest.Mem()
	// @ ensures  err != nil ==> err.ErrorMem()
	PerformHandshake(log logger.T, kmsKeyId string, encryptionEnabled bool, sessionTypeRequest mgsContracts.SessionTypeRequest) (err error)

	// @ requires noPerm < p
	// @ preserves acc(Mem(), p)
	// @ ensures  err != nil ==> err.ErrorMem()
	GetClientVersion( /*@ ghost p perm @*/ ) (version string, err error)

	// @ requires noPerm < p
	// @ preserves acc(Mem(), p)
	// @ ensures  err != nil ==> err.ErrorMem()
	GetInstanceId( /*@ ghost p perm @*/ ) (instanceId string, err error)

	// @ requires noPerm < p
	// @ preserves acc(Mem(), p)
	// @ ensures  err != nil ==> err.ErrorMem()
	GetRegion( /*@ ghost p perm @*/ ) (region string, err error)

	// @ requires noPerm < p
	// @ preserves acc(Mem(), p)
	// @ ensures  err != nil ==> err.ErrorMem()
	IsActive( /*@ ghost p perm @*/ ) (isActive bool, err error)

	// @ requires noPerm < p
	// @ preserves acc(Mem(), p)
	// @ ensures  err != nil ==> err.ErrorMem()
	GetSeparateOutputPayload( /*@ ghost p perm @*/ ) (res bool, err error)

	// @ preserves Mem()
	// @ ensures  err != nil ==> err.ErrorMem()
	SetSeparateOutputPayload(separateOutputPayload bool) (err error)

	// @ requires log != nil
	// @ preserves Mem() && acc(log.Mem(), _)
	// @ ensures  err != nil ==> err.ErrorMem()
	PrepareToCloseChannel(log logger.T) (err error)

	// @ requires log != nil
	// @ preserves Mem() && acc(log.Mem(), _)
	// @ ensures  err != nil ==> err.ErrorMem()
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

	// TODO: mark the following fields as ghost as soon as Gobra supports ghost fields
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

/*@
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

pred (dc *dataChannel) MemFields(state DataChannelState) {
	acc(&dc.dataStream) &&
	acc(&dc.hs.clientVersion) &&
	acc(&dc.hs.error) &&
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
	acc(&dc.hs.startReceivingChan, _) &&
	acc(&dc.hs.responseChan, _) &&
	acc(&dc.ioLock) &&
	(state >= Initialized ==>
		dc.dataStream.Mem() &&
		dc.kmsService.Mem() &&
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
		acc(&dc.ioLock)) &&
	(state != Erroneous && state < IODistributed ==>
		acc(&dc.ioLockDidLocalReceive) && acc(&dc.ioLockCanRemoteSend) &&
		acc(&dc.ioLockDidRemoteReceive) && acc(&dc.ioLockCanLocalSend) &&
		dc.LocalInFactTMem() && dc.RemoteInFactTMem() &&
		dc.LocalOutFactTMem() && dc.RemoteOutFactTMem()) &&
	(state >= Initialized ==>
		dc.IoSpecMemPartial() &&
		dc.dataStream.Mem() &&
		dc.kmsService.Mem() &&
		dc.logLTPk.Mem()) &&
	(state >= Initialized && state < IODistributed ==>
		dc.IoSpecMemMain() &&
		pl.token(dc.getToken()) &&
		iospec.P_Agent(dc.getToken(), dc.getRid(), dc.getAbsState()) &&
		tm.pubTerm(pub.pub_msg(dc.instanceId)) == dc.getAgentIdT() &&
		tm.pubTerm(pub.pub_msg(dc.clientId)) == dc.getClientIdT() &&
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
		bytes.SliceMem(dc.secrets.agentSecret) &&
		by.gamma(dc.getAgentShareT()) == abs.Abs(dc.secrets.agentSecret)) &&
	(state >= BlockCipherReady && dc.encryptionEnabled ==>
		dc.blockCipher.IsReady() &&
		dc.getSharedSecretT() == tm.exp(tm.exp(tm.pubTerm(pub.const_g_pub()), dc.getClientShareT()), dc.getAgentShareT()) &&
		dc.blockCipher.GetEncKeyT() == tm.kdf1(dc.getSharedSecretT()) &&
		dc.blockCipher.GetDecKeyT() == tm.kdf2(dc.getSharedSecretT())) &&
	// relate state to abstract state:
	(state == Initialized || state == BlockCipherInitialized ==>
		ft.Setup_Agent(dc.getRid(), dc.getAgentIdT(), dc.getKMSIdT(), dc.getClientIdT(), dc.getReaderIdT(), tm.pubTerm(pub.pub_msg(dc.secrets.agentLTKeyARN)), dc.getLogLTPkT()) in dc.getAbsState()) &&
	(state == AgentSecretCreatedAndSigned ==>
		ft.St_Agent_2(dc.getRid(), dc.getAgentIdT(), dc.getKMSIdT(), dc.getClientIdT(), dc.getReaderIdT(), tm.pubTerm(pub.pub_msg(dc.secrets.agentLTKeyARN)), dc.getLogLTPkT(), dc.getAgentShareT(), dc.getAgentShareSignatureT()) in dc.getAbsState()) &&
	(state == HandshakeRequestSent ==>
		ft.St_Agent_3(dc.getRid(), dc.getAgentIdT(), dc.getKMSIdT(), dc.getClientIdT(), dc.getReaderIdT(), tm.pubTerm(pub.pub_msg(dc.secrets.agentLTKeyARN)), dc.getLogLTPkT(), dc.getAgentShareT(), dc.getAgentShareSignatureT()) in dc.getAbsState()) &&
	(state == BlockCipherReady ==>
		ft.St_Agent_9(dc.getRid(), dc.getAgentIdT(), dc.getKMSIdT(), dc.getClientIdT(), dc.getReaderIdT(), tm.pubTerm(pub.pub_msg(dc.secrets.agentLTKeyARN)), dc.getLogLTPkT(), dc.getAgentShareT(), dc.getAgentShareSignatureT(), dc.getClientLtKeyIdT(), tm.exp(tm.pubTerm(pub.const_g_pub()), dc.getClientShareT()), dc.getClientShareSignatureT(), dc.getSigSessionKeysT()) in dc.getAbsState()) &&
	(state == HandshakeCompleted ==>
		ft.St_Agent_10(dc.getRid(), dc.getAgentIdT(), dc.getKMSIdT(), dc.getClientIdT(), dc.getReaderIdT(), tm.pubTerm(pub.pub_msg(dc.secrets.agentLTKeyARN)), dc.getLogLTPkT(), dc.getAgentShareT(), dc.getAgentShareSignatureT(), dc.getClientLtKeyIdT(), tm.exp(tm.pubTerm(pub.const_g_pub()), dc.getClientShareT()), dc.getClientShareSignatureT(), dc.getSigSessionKeysT()) in dc.getAbsState()) &&
	(state == IODistributed ==>
		// the idea is that the receiving thread does not get permission to Mem() but a reduced invariant:
		acc(&dc.ioLockDidLocalReceive) && acc(&dc.ioLockCanRemoteSend) &&
		dc.LocalInFactTMem() && dc.RemoteOutFactTMem() &&
		acc(dc.ioLock.LockP()) && dc.ioLock.LockInv() == IoLockInv!<dc, dc.instanceId, dc.clientId, dc.secrets.agentLTKeyARN!>)
}

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
	acc(dc.IoSpecMemPartial(), 1/4) &&
	dc.getSharedSecretT() == tm.exp(tm.exp(tm.pubTerm(pub.const_g_pub()), dc.getClientShareT()), dc.getAgentShareT()) &&
	dc.blockCipher.GetEncKeyT() == tm.kdf1(dc.getSharedSecretT()) &&
	dc.blockCipher.GetDecKeyT() == tm.kdf2(dc.getSharedSecretT()) &&
	acc(&dc.ioLockCanLocalSend, 1/2) && acc(&dc.ioLockDidRemoteReceive, 1/2) &&
	acc(dc.LocalOutFactTMem(), 1/2) && acc(dc.RemoteInFactTMem(), 1/2) &&
	acc(dc.ioLock.LockP(), 1/2) && dc.ioLock.LockInv() == IoLockInv!<dc, dc.instanceId, dc.clientId, dc.secrets.agentLTKeyARN!>
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
	dc.IoSpecMemMain() &&
	dc.IoSpecMemPartial() &&
	(state != Erroneous ==>
		pl.token(dc.getToken()) &&
		iospec.P_Agent(dc.getToken(), dc.getRid(), dc.getAbsState())) &&
	tm.pubTerm(pub.pub_msg(dc.instanceId)) == dc.getAgentIdT() &&
	tm.pubTerm(pub.pub_msg(dc.clientId)) == dc.getClientIdT() &&
	tm.pubTerm(pub.pub_msg(dc.logReaderId)) == dc.getReaderIdT() &&
	by.gamma(dc.getLogLTPkT()) == dc.logLTPk.Abs() &&
	(encryptionEnabled ==>
		dc.logLTPk.Mem() &&
		dc.kmsService.Mem() &&
		bytes.SliceMem(dc.secrets.agentSecret) &&
		by.gamma(dc.getAgentShareT()) == abs.Abs(dc.secrets.agentSecret)) &&
	(state == HandshakeRequestSent ==>
		ft.St_Agent_3(dc.getRid(), dc.getAgentIdT(), dc.getKMSIdT(), dc.getClientIdT(), dc.getReaderIdT(), tm.pubTerm(pub.pub_msg(dc.secrets.agentLTKeyARN)), dc.getLogLTPkT(), dc.getAgentShareT(), dc.getAgentShareSignatureT()) in dc.getAbsState()) &&
	(state >= HandshakeResponseReceived ==>
		bytes.SliceMem(dc.secrets.sharedSecret) &&
		// TODO: we could technically remove `getSharedSecretT` as it only acts as an abbreviation:
		dc.getSharedSecretT() == tm.exp(tm.exp(tm.pubTerm(pub.const_g_pub()), dc.getClientShareT()), dc.getAgentShareT()) &&
		by.gamma(dc.getSharedSecretT()) == abs.Abs(dc.secrets.sharedSecret)) &&
	(state == HandshakeResponseVerified ==>
		ft.St_Agent_6(dc.getRid(), dc.getAgentIdT(), dc.getKMSIdT(), dc.getClientIdT(), dc.getReaderIdT(), tm.pubTerm(pub.pub_msg(dc.secrets.agentLTKeyARN)), dc.getLogLTPkT(), dc.getAgentShareT(), dc.getAgentShareSignatureT(), dc.getClientLtKeyIdT(), tm.exp(tm.pubTerm(pub.const_g_pub()), dc.getClientShareT()), dc.getClientShareSignatureT()) in dc.getAbsState()) &&
	(state == BlockCipherReady ==>
		(encryptionEnabled ==>
			dc.blockCipher.IsReady() &&
			dc.blockCipher.GetEncKeyT() == tm.kdf1(dc.getSharedSecretT()) &&
			dc.blockCipher.GetDecKeyT() == tm.kdf2(dc.getSharedSecretT())) &&
		ft.St_Agent_9(dc.getRid(), dc.getAgentIdT(), dc.getKMSIdT(), dc.getClientIdT(), dc.getReaderIdT(), tm.pubTerm(pub.pub_msg(dc.secrets.agentLTKeyARN)), dc.getLogLTPkT(), dc.getAgentShareT(), dc.getAgentShareSignatureT(), dc.getClientLtKeyIdT(), tm.exp(tm.pubTerm(pub.const_g_pub()), dc.getClientShareT()), dc.getClientShareSignatureT(), dc.getSigSessionKeysT()) in dc.getAbsState())
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
decreases _
requires acc(dc.TokenMem(), _)
pure func (dc *dataChannel) getTokenInternal() pl.Place

ghost
decreases
requires acc(dc.IoSpecMemMain(), _)
pure func (dc *dataChannel) getToken() pl.Place {
	return unfolding acc(dc.IoSpecMemMain(), _) in dc.getTokenInternal()
}

ghost
decreases
requires acc(dc.Mem(), _) && dc.getState() >= Initialized && dc.getState() < IODistributed
pure func (dc *dataChannel) GetToken() pl.Place {
	return unfolding acc(dc.Mem(), _) in unfolding acc(dc.MemInternal(dc.dataChannelState), _) in dc.getToken()
}

ghost
decreases _
preserves dc.TokenMem()
ensures dc.getTokenInternal() == token
func (dc *dataChannel) setToken(token pl.Place)

pred (dc *dataChannel) RidMem()

ghost
decreases _
requires acc(dc.RidMem(), _)
pure func (dc *dataChannel) getRidInternal() tm.Term

ghost
decreases
requires acc(dc.IoSpecMemPartial(), _)
pure func (dc *dataChannel) getRid() tm.Term {
	return unfolding acc(dc.IoSpecMemPartial(), _) in dc.getRidInternal()
}

ghost
decreases
requires acc(dc.Mem(), _) && dc.getState() >= Initialized && dc.getState() < IODistributed
pure func (dc *dataChannel) GetRid() tm.Term {
	return unfolding acc(dc.Mem(), _) in unfolding acc(dc.MemInternal(dc.dataChannelState), _) in dc.getRid()
}

ghost
decreases _
preserves dc.RidMem()
ensures dc.getRidInternal() == rid
func (dc *dataChannel) setRid(rid tm.Term)

pred (dc *dataChannel) AbsStateMem()

ghost
decreases _
requires acc(dc.AbsStateMem(), _)
pure func (dc *dataChannel) getAbsStateInternal() mset[ft.Fact]

ghost
decreases
requires acc(dc.IoSpecMemMain(), _)
pure func (dc *dataChannel) getAbsState() mset[ft.Fact] {
	return unfolding acc(dc.IoSpecMemMain(), _) in dc.getAbsStateInternal()
}

ghost
decreases
requires acc(dc.Mem(), _) && dc.getState() >= Initialized && dc.getState() < IODistributed
pure func (dc *dataChannel) GetAbsState() mset[ft.Fact] {
	return unfolding acc(dc.Mem(), _) in unfolding acc(dc.MemInternal(dc.dataChannelState), _) in dc.getAbsState()
}

ghost
decreases _
preserves dc.AbsStateMem()
ensures dc.getAbsStateInternal() == state
func (dc *dataChannel) setAbsState(state mset[ft.Fact])

pred (dc *dataChannel) AgentIdTMem()

ghost
decreases _
requires acc(dc.AgentIdTMem(), _)
pure func (dc *dataChannel) getAgentIdTInternal() tm.Term

ghost
decreases
requires acc(dc.IoSpecMemPartial(), _)
pure func (dc *dataChannel) getAgentIdT() tm.Term {
	return unfolding acc(dc.IoSpecMemPartial(), _) in dc.getAgentIdTInternal()
}

ghost
decreases
requires acc(dc.Mem(), _) && dc.getState() >= Initialized
pure func (dc *dataChannel) GetAgentIdT() tm.Term {
	return unfolding acc(dc.Mem(), _) in unfolding acc(dc.MemInternal(dc.dataChannelState), _) in dc.getAgentIdT()
}

ghost
decreases _
preserves dc.AgentIdTMem()
ensures dc.getAgentIdTInternal() == agentIdT
func (dc *dataChannel) setAgentIdT(agentIdT tm.Term)

pred (dc *dataChannel) KMSIdTMem()

ghost
decreases _
requires acc(dc.KMSIdTMem(), _)
pure func (dc *dataChannel) getKMSIdTInternal() tm.Term

ghost
decreases
requires acc(dc.IoSpecMemPartial(), _)
pure func (dc *dataChannel) getKMSIdT() tm.Term {
	return unfolding acc(dc.IoSpecMemPartial(), _) in dc.getKMSIdTInternal()
}

ghost
decreases
requires acc(dc.Mem(), _) && dc.getState() >= Initialized
pure func (dc *dataChannel) GetKMSIdT() tm.Term {
	return unfolding acc(dc.Mem(), _) in unfolding acc(dc.MemInternal(dc.dataChannelState), _) in dc.getKMSIdT()
}

ghost
decreases _
preserves dc.KMSIdTMem()
ensures dc.getKMSIdTInternal() == kmsIdT
func (dc *dataChannel) setKMSIdT(kmsIdT tm.Term)

pred (dc *dataChannel) ClientIdTMem()

ghost
decreases _
requires acc(dc.ClientIdTMem(), _)
pure func (dc *dataChannel) getClientIdTInternal() tm.Term

ghost
decreases
requires acc(dc.IoSpecMemPartial(), _)
pure func (dc *dataChannel) getClientIdT() tm.Term {
	return unfolding acc(dc.IoSpecMemPartial(), _) in dc.getClientIdTInternal()
}

ghost
decreases
requires acc(dc.Mem(), _) && dc.getState() >= Initialized
pure func (dc *dataChannel) GetClientIdT() tm.Term {
	return unfolding acc(dc.Mem(), _) in unfolding acc(dc.MemInternal(dc.dataChannelState), _) in dc.getClientIdT()
}

ghost
decreases _
preserves dc.ClientIdTMem()
ensures dc.getClientIdTInternal() == clientIdT
func (dc *dataChannel) setClientIdT(clientIdT tm.Term)

pred (dc *dataChannel) ReaderIdTMem()

ghost
decreases _
requires acc(dc.ReaderIdTMem(), _)
pure func (dc *dataChannel) getReaderIdTInternal() tm.Term

ghost
decreases
requires acc(dc.IoSpecMemPartial(), _)
pure func (dc *dataChannel) getReaderIdT() tm.Term {
	return unfolding acc(dc.IoSpecMemPartial(), _) in dc.getReaderIdTInternal()
}

ghost
decreases
requires acc(dc.Mem(), _) && dc.getState() >= Initialized
pure func (dc *dataChannel) GetReaderIdT() tm.Term {
	return unfolding acc(dc.Mem(), _) in unfolding acc(dc.MemInternal(dc.dataChannelState), _) in dc.getReaderIdT()
}

ghost
decreases _
preserves dc.ReaderIdTMem()
ensures dc.getReaderIdTInternal() == readerIdT
func (dc *dataChannel) setReaderIdT(readerIdT tm.Term)

pred (dc *dataChannel) LogLTPkTMem()

ghost
decreases _
requires acc(dc.LogLTPkTMem(), _)
pure func (dc *dataChannel) getLogLTPkTInternal() tm.Term

ghost
decreases
requires acc(dc.IoSpecMemPartial(), _)
pure func (dc *dataChannel) getLogLTPkT() tm.Term {
	return unfolding acc(dc.IoSpecMemPartial(), _) in dc.getLogLTPkTInternal()
}

ghost
decreases
requires acc(dc.Mem(), _) && dc.getState() >= Initialized
pure func (dc *dataChannel) GetLogLTPkT() tm.Term {
	return unfolding acc(dc.Mem(), _) in unfolding acc(dc.MemInternal(dc.dataChannelState), _) in dc.getLogLTPkT()
}

ghost
decreases _
preserves dc.LogLTPkTMem()
ensures dc.getLogLTPkTInternal() == logLTPkT
func (dc *dataChannel) setLogLTPkT(logLTPkT tm.Term)

pred (dc *dataChannel) AgentShareTMem()

ghost
decreases _
requires acc(dc.AgentShareTMem(), _)
pure func (dc *dataChannel) getAgentShareTInternal() tm.Term

ghost
decreases
requires acc(dc.IoSpecMemPartial(), _)
pure func (dc *dataChannel) getAgentShareT() tm.Term {
	return unfolding acc(dc.IoSpecMemPartial(), _) in dc.getAgentShareTInternal()
}

ghost
decreases
requires acc(dc.Mem(), _) && dc.getState() >= Initialized
pure func (dc *dataChannel) GetAgentShareT() tm.Term {
	return unfolding acc(dc.Mem(), _) in unfolding acc(dc.MemInternal(dc.dataChannelState), _) in dc.getAgentShareT()
}

ghost
decreases _
preserves dc.AgentShareTMem()
ensures dc.getAgentShareTInternal() == shareT
func (dc *dataChannel) setAgentShareT(shareT tm.Term)

pred (dc *dataChannel) AgentShareSignatureTMem()

ghost
decreases _
requires acc(dc.AgentShareSignatureTMem(), _)
pure func (dc *dataChannel) getAgentShareSignatureTInternal() tm.Term

ghost
decreases
requires acc(dc.IoSpecMemPartial(), _)
pure func (dc *dataChannel) getAgentShareSignatureT() tm.Term {
	return unfolding acc(dc.IoSpecMemPartial(), _) in dc.getAgentShareSignatureTInternal()
}

ghost
decreases _
requires acc(dc.Mem(), _) && dc.getState() >= Initialized
pure func (dc *dataChannel) GetAgentShareSignatureT() tm.Term {
	return unfolding acc(dc.Mem(), _) in unfolding acc(dc.MemInternal(dc.dataChannelState), _) in dc.getAgentShareSignatureT()
}

ghost
decreases
preserves dc.AgentShareSignatureTMem()
ensures dc.getAgentShareSignatureTInternal() == signatureT
func (dc *dataChannel) setAgentShareSignatureT(signatureT tm.Term)

pred (dc *dataChannel) InFactTMem()

ghost
decreases _
requires acc(dc.InFactTMem(), _)
pure func (dc *dataChannel) getInFactTInternal() tm.Term

ghost
decreases
requires acc(dc.IoSpecMemPartial(), _)
pure func (dc *dataChannel) getInFactT() tm.Term {
	return unfolding acc(dc.IoSpecMemPartial(), _) in dc.getInFactTInternal()
}

ghost
decreases
requires acc(dc.Mem(), _) && dc.getState() >= Initialized
pure func (dc *dataChannel) GetInFactT() tm.Term {
	return unfolding acc(dc.Mem(), _) in unfolding acc(dc.MemInternal(dc.dataChannelState), _) in dc.getInFactT()
}

ghost
decreases _
preserves dc.InFactTMem()
ensures dc.getInFactTInternal() == inFactT
func (dc *dataChannel) setInFactT(inFactT tm.Term)

pred (dc *dataChannel) SharedSecretTMem()

ghost
decreases _
requires acc(dc.SharedSecretTMem(), _)
pure func (dc *dataChannel) getSharedSecretTInternal() tm.Term

ghost
decreases
requires acc(dc.IoSpecMemPartial(), _)
pure func (dc *dataChannel) getSharedSecretT() tm.Term {
	return unfolding acc(dc.IoSpecMemPartial(), _) in dc.getSharedSecretTInternal()
}

ghost
decreases
requires acc(dc.Mem(), _) && dc.getState() >= Initialized
pure func (dc *dataChannel) GetSharedSecretT() tm.Term {
	return unfolding acc(dc.Mem(), _) in unfolding acc(dc.MemInternal(dc.dataChannelState), _) in dc.getSharedSecretT()
}

ghost
decreases _
preserves dc.SharedSecretTMem()
ensures dc.getSharedSecretTInternal() == sharedSecretT
func (dc *dataChannel) setSharedSecretT(sharedSecretT tm.Term)

pred (dc *dataChannel) ClientLtKeyIdTMem()

ghost
decreases _
requires acc(dc.ClientLtKeyIdTMem(), _)
pure func (dc *dataChannel) getClientLtKeyIdTInternal() tm.Term

ghost
decreases
requires acc(dc.IoSpecMemPartial(), _)
pure func (dc *dataChannel) getClientLtKeyIdT() tm.Term {
	return unfolding acc(dc.IoSpecMemPartial(), _) in dc.getClientLtKeyIdTInternal()
}

ghost
decreases
requires acc(dc.Mem(), _) && dc.getState() >= Initialized
pure func (dc *dataChannel) GetClientLtKeyIdT() tm.Term {
	return unfolding acc(dc.Mem(), _) in unfolding acc(dc.MemInternal(dc.dataChannelState), _) in dc.getClientLtKeyIdT()
}

ghost
decreases _
preserves dc.ClientLtKeyIdTMem()
ensures dc.getClientLtKeyIdTInternal() == clientLtKeyIdT
func (dc *dataChannel) setClientLtKeyIdT(clientLtKeyIdT tm.Term)

pred (dc *dataChannel) ClientShareTMem()

ghost
decreases _
requires acc(dc.ClientShareTMem(), _)
pure func (dc *dataChannel) getClientShareTInternal() tm.Term

ghost
decreases
requires acc(dc.IoSpecMemPartial(), _)
pure func (dc *dataChannel) getClientShareT() tm.Term {
	return unfolding acc(dc.IoSpecMemPartial(), _) in dc.getClientShareTInternal()
}

ghost
decreases
requires acc(dc.Mem(), _) && dc.getState() >= Initialized
pure func (dc *dataChannel) GetClientShareT() tm.Term {
	return unfolding acc(dc.Mem(), _) in unfolding acc(dc.MemInternal(dc.dataChannelState), _) in dc.getClientShareT()
}

ghost
decreases _
preserves dc.ClientShareTMem()
ensures dc.getClientShareTInternal() == clientShareT
func (dc *dataChannel) setClientShareT(clientShareT tm.Term)

pred (dc *dataChannel) ClientShareSignatureTMem()

ghost
decreases _
requires acc(dc.ClientShareSignatureTMem(), _)
pure func (dc *dataChannel) getClientShareSignatureTInternal() tm.Term

ghost
decreases
requires acc(dc.IoSpecMemPartial(), _)
pure func (dc *dataChannel) getClientShareSignatureT() tm.Term {
	return unfolding acc(dc.IoSpecMemPartial(), _) in dc.getClientShareSignatureTInternal()
}

ghost
decreases
requires acc(dc.Mem(), _) && dc.getState() >= Initialized
pure func (dc *dataChannel) GetClientShareSignatureT() tm.Term {
	return unfolding acc(dc.Mem(), _) in unfolding acc(dc.MemInternal(dc.dataChannelState), _) in dc.getClientShareSignatureT()
}

ghost
decreases _
preserves dc.ClientShareSignatureTMem()
ensures dc.getClientShareSignatureTInternal() == clientShareSignatureT
func (dc *dataChannel) setClientShareSignatureT(clientShareSignatureT tm.Term)

pred (dc *dataChannel) SigSessionKeysTMem()

ghost
decreases _
requires acc(dc.SigSessionKeysTMem(), _)
pure func (dc *dataChannel) getSigSessionKeysTInternal() tm.Term

ghost
decreases
requires acc(dc.IoSpecMemPartial(), _)
pure func (dc *dataChannel) getSigSessionKeysT() tm.Term {
	return unfolding acc(dc.IoSpecMemPartial(), _) in dc.getSigSessionKeysTInternal()
}

ghost
decreases
requires acc(dc.Mem(), _) && dc.getState() >= Initialized
pure func (dc *dataChannel) GetSigSessionKeysT() tm.Term {
	return unfolding acc(dc.Mem(), _) in unfolding acc(dc.MemInternal(dc.dataChannelState), _) in dc.getSigSessionKeysT()
}

ghost
decreases _
preserves dc.SigSessionKeysTMem()
ensures dc.getSigSessionKeysTInternal() == sigSessionKeysT
func (dc *dataChannel) setSigSessionKeysT(sigSessionKeysT tm.Term)

pred (dc *dataChannel) LocalInFactTMem()

ghost
decreases _
requires acc(dc.LocalInFactTMem(), _)
pure func (dc *dataChannel) getLocalInFactTInternal() tm.Term

ghost
decreases _
preserves dc.LocalInFactTMem()
ensures dc.getLocalInFactTInternal() == inFactT
func (dc *dataChannel) setLocalInFactT(inFactT tm.Term)

pred (dc *dataChannel) RemoteInFactTMem()

ghost
decreases _
requires acc(dc.RemoteInFactTMem(), _)
pure func (dc *dataChannel) getRemoteInFactTInternal() tm.Term

ghost
decreases _
preserves dc.RemoteInFactTMem()
ensures dc.getRemoteInFactTInternal() == inFactT
func (dc *dataChannel) setRemoteInFactT(inFactT tm.Term)

pred (dc *dataChannel) LocalOutFactTMem()

ghost
decreases _
requires acc(dc.LocalOutFactTMem(), _)
pure func (dc *dataChannel) getLocalOutFactTInternal() tm.Term

ghost
decreases _
preserves dc.LocalOutFactTMem()
ensures dc.getLocalOutFactTInternal() == outFactT
func (dc *dataChannel) setLocalOutFactT(outFactT tm.Term)

pred (dc *dataChannel) RemoteOutFactTMem()

ghost
decreases _
requires acc(dc.RemoteOutFactTMem(), _)
pure func (dc *dataChannel) getRemoteOutFactTInternal() tm.Term

ghost
decreases _
preserves dc.RemoteOutFactTMem()
ensures dc.getRemoteOutFactTInternal() == outFactT
func (dc *dataChannel) setRemoteOutFactT(outFactT tm.Term)

ghost
decreases
requires acc(dc.Mem(), _) && dc.getState() >= BlockCipherInitialized
pure func (dc *dataChannel) GetEncKeyT() tm.Term {
	return unfolding acc(dc.Mem(), _) in unfolding acc(dc.MemInternal(dc.dataChannelState), _) in dc.blockCipher.GetEncKeyT()
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
