package iosanitization

// this file contains wrappers for I/O operations that enforce and consume
// I/O permissions. In return, we can assume that these wrappers sanitize
// all parameters as we have proven that these operations are permitted
// by the protocol model. However, all functions in this package must only
// be called by verified functions in the datachannel package. Otherwise,
// we do not prove that the preconditions are satisfied.

import (
	logger "github.com/aws/amazon-ssm-agent/agent/log"
	mgsContracts "github.com/aws/amazon-ssm-agent/agent/session/contracts"
	"github.com/aws/amazon-ssm-agent/agent/session/crypto"
	"github.com/aws/amazon-ssm-agent/agent/session/datastream"
	//@ "bytes"
	//@ abs "github.com/aws/amazon-ssm-agent/agent/iospecs/abs"
	//@ by "github.com/aws/amazon-ssm-agent/agent/iospecs/bytes"
	//@ ft "github.com/aws/amazon-ssm-agent/agent/iospecs/fact"
	//@ "github.com/aws/amazon-ssm-agent/agent/iospecs/iospec"
	//@ pl "github.com/aws/amazon-ssm-agent/agent/iospecs/place"
	//@ pub "github.com/aws/amazon-ssm-agent/agent/iospecs/pub"
	//@ tm "github.com/aws/amazon-ssm-agent/agent/iospecs/term"
)

// ----- KMS -----

// @ requires noPerm < p
// @ requires kmsService.Mem() && acc(bytes.SliceMem(message), p)
// @ requires m == tm.pair(tm.pubTerm(pub.const_SignRequest_pub()), tm.pair(tm.pubTerm(pub.pub_msg(keyID)), messageT))
// @ requires pl.token(t) && iospec.e_Out_KMS(t, rid, agentId, kmsId, rid, m) && by.gamma(messageT) == abs.Abs(message)
// @ requires let t1 := iospec.get_e_Out_KMS_placeDst(t, rid, agentId, kmsId, rid, m) in (
// @     iospec.e_In_KMS(t1, rid))
// @ ensures  kmsService.Mem() && acc(bytes.SliceMem(message), p)
// @ ensures  err == nil ==> bytes.SliceMem(signature) && by.gamma(signatureT) == abs.Abs(signature)
// @ ensures  err != nil ==> err.ErrorMem()
// @ ensures  err == nil ==> let t1 := old(iospec.get_e_Out_KMS_placeDst(t, rid, agentId, kmsId, rid, m)) in (
// @     pl.token(old(iospec.get_e_In_KMS_placeDst(t1, rid))) &&
// @     kmsId == old(iospec.get_e_In_KMS_r1(t1, rid)) &&
// @     agentId == old(iospec.get_e_In_KMS_r2(t1, rid)) &&
// @     rid == old(iospec.get_e_In_KMS_r3(t1, rid)) &&
// @     tm.pair(tm.pubTerm(pub.const_SignResponse_pub()), signatureT) == old(iospec.get_e_In_KMS_r4(t1, rid)))
func KMSSign(kmsService *crypto.KMSService, keyID string, message []byte /*@, ghost p perm, ghost t pl.Place, ghost rid tm.Term, ghost agentId tm.Term, ghost kmsId tm.Term, ghost messageT tm.Term, ghost m tm.Term @*/) (signature []byte, err error /*@, ghost signatureT tm.Term @*/) {
	return kmsService.Sign(keyID, message /*@, p, t, rid, agentId, kmsId, messageT, m @*/)
}

// @ requires noPerm < p
// @ requires m == tm.pair(tm.pubTerm(pub.const_VerifyRequest_pub()), tm.pair(clientId, tm.pair(kmsKeyIdT, tm.pair(messageT, signatureT))))
// @ requires kmsService.Mem() && acc(bytes.SliceMem(message), p) && acc(bytes.SliceMem(signature), p)
// @ requires pl.token(t) && iospec.e_Out_KMS(t, rid, agentId, kmsId, rid, m) && by.gamma(kmsKeyIdT) == by.msgB(kmsKeyId) && by.gamma(messageT) == abs.Abs(message) && by.gamma(signatureT) == abs.Abs(signature)
// @ requires let t1 := iospec.get_e_Out_KMS_placeDst(t, rid, agentId, kmsId, rid, m) in (
// @     iospec.e_In_KMS(t1, rid))
// @ ensures  kmsService.Mem() && acc(bytes.SliceMem(message), p) && acc(bytes.SliceMem(signature), p)
// @ ensures  err != nil ==> err.ErrorMem()
// @ ensures  err == nil ==> let t1 := old(iospec.get_e_Out_KMS_placeDst(t, rid, agentId, kmsId, rid, m)) in (
// @     pl.token(old(iospec.get_e_In_KMS_placeDst(t1, rid))) &&
// @     kmsId == old(iospec.get_e_In_KMS_r1(t1, rid)) &&
// @     agentId == old(iospec.get_e_In_KMS_r2(t1, rid)) &&
// @     rid == old(iospec.get_e_In_KMS_r3(t1, rid)) &&
// @     tm.pubTerm(pub.const_VerifyResponse_pub()) == old(iospec.get_e_In_KMS_r4(t1, rid)))
func KMSVerify(kmsService *crypto.KMSService, kmsKeyId string, message []byte, signature []byte /*@, ghost p perm, ghost t pl.Place, ghost rid tm.Term, ghost agentId tm.Term, ghost kmsId tm.Term, ghost clientId tm.Term, ghost kmsKeyIdT tm.Term, ghost messageT tm.Term, ghost signatureT tm.Term, ghost m tm.Term @*/) (success bool, err error) {
	return kmsService.Verify(kmsKeyId, message, signature /*@, p, t, rid, agentId, kmsId, clientId, kmsKeyIdT, messageT, signatureT, m @*/)
}

// ----- DataStream -----

// @ requires log != nil && noPerm < p
// @ requires bytes.SliceMem(inputData)
// @ requires m == tm.pair(mgsContracts.payloadTypeTerm(payloadType), inputDataT)
// @ requires pl.token(t) && iospec.e_OutFact(t, rid, m) && by.gamma(inputDataT) == abs.Abs(inputData)
// @ preserves acc(dataStream.Mem(), p) && acc(log.Mem(), _)
// @ ensures  err != nil ==> err.ErrorMem()
// @ ensures  err == nil ==> pl.token(t1) && t1 == old(iospec.get_e_OutFact_placeDst(t, rid, m))
// @ ensures  err != nil ==> t1 == t && pl.token(t) && iospec.e_OutFact(t, rid, m) && iospec.get_e_OutFact_placeDst(t, rid, m) == old(iospec.get_e_OutFact_placeDst(t, rid, m))
func DataStreamSend(dataStream *datastream.DataStream, log logger.T, payloadType mgsContracts.PayloadType, inputData []byte /*@, ghost p perm, ghost t pl.Place, ghost rid tm.Term, ghost inputDataT tm.Term, ghost m tm.Term @*/) (err error /*@, ghost t1 pl.Place @*/) {
	return dataStream.Send(log, payloadType, inputData /*@, p, t, rid, inputDataT, m @*/)
}

// ----- DataChannel -----

type InputStreamMessageHandler = func(streamDataMessage *mgsContracts.AgentMessage /*@, ghost t pl.Place, ghost rid tm.Term, ghost agentMessageT tm.Term @*/) error

/*@
// this is non-ghost because it's the spec for a non-ghost closure implementation
requires agentMessage.Mem()
requires pl.token(t) && iospec.e_OutFact(t, rid, agentMessageT) && by.gamma(agentMessageT) == agentMessage.Abs()
ensures  pl.token(old(iospec.get_e_OutFact_placeDst(t, rid, agentMessageT)))
func StreamDataHandlerSpec(agentMessage *mgsContracts.AgentMessage, ghost t pl.Place, ghost rid tm.Term, ghost agentMessageT tm.Term) (err error)
@*/

// @ requires handler implements StreamDataHandlerSpec{}
// @ requires agentMessage.Mem()
// @ requires pl.token(t) && iospec.e_OutFact(t, rid, agentMessageT) && by.gamma(agentMessageT) == agentMessage.Abs()
// @ ensures  pl.token(old(iospec.get_e_OutFact_placeDst(t, rid, agentMessageT)))
func DataChannelForwardToMessageHandler(handler InputStreamMessageHandler, agentMessage *mgsContracts.AgentMessage /*@, ghost t pl.Place, ghost rid tm.Term, ghost agentMessageT tm.Term @*/) (err error) {
	return handler(agentMessage /*@, t, rid, agentMessageT @*/) /*@ as StreamDataHandlerSpec{} @*/
}

// calling this function results in treating `data` being treated as received from the environment / attacker (on the
// level of the abstract model). Thus, this function can be seen as performing a virtual input operation.
// However, since `data` is treated as coming from the attacker, `data` must not be tainted.
// @ trusted
// @ decreases
// @ requires acc(bytes.SliceMem(data), 1/16)
// @ requires pl.token(t) && iospec.e_InFact(t, rid)
// @ ensures  acc(bytes.SliceMem(data), 1/16) && by.gamma(dataT) == abs.Abs(data)
// @ ensures  pl.token(t1) && t1 == old(iospec.get_e_InFact_placeDst(t, rid))
// @ ensures  dataT == old(iospec.get_e_InFact_r1(t, rid))
func PerformVirtualInputOperation(data []byte /*@, ghost t pl.Place, ghost rid tm.Term @*/) /*@ (ghost t1 pl.Place, dataT tm.Term) @*/ {
	return
}

// calling this function results in treating `msg` being treated as received from the environment / attacker (on the
// level of the abstract model). Thus, this function can be seen as performing a virtual input operation.
// However, since `msg` is treated as coming from the attacker, `msg` must not be tainted.
// @ trusted
// @ decreases
// @ requires acc(msg.Mem(), 1/16)
// @ requires pl.token(t) && iospec.e_InFact(t, rid)
// @ ensures  acc(msg.Mem(), 1/16) && by.gamma(dataT) == msg.Abs()
// @ ensures  pl.token(t1) && t1 == old(iospec.get_e_InFact_placeDst(t, rid))
// @ ensures  dataT == old(iospec.get_e_InFact_r1(t, rid))
func PerformVirtualInputOperationAgentMessage(msg *mgsContracts.AgentMessage /*@, ghost t pl.Place, ghost rid tm.Term @*/) /*@ (ghost t1 pl.Place, dataT tm.Term) @*/ {
	return
}
