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
	//@ cryptoRand "crypto/rand"

	logger "github.com/aws/amazon-ssm-agent/agent/log"
	mgsContracts "github.com/aws/amazon-ssm-agent/agent/session/contracts"
	"github.com/aws/amazon-ssm-agent/agent/version"
	//@ abs "github.com/aws/amazon-ssm-agent/agent/iospecs/abs"
	//@ by "github.com/aws/amazon-ssm-agent/agent/iospecs/bytes"
	//@ cl "github.com/aws/amazon-ssm-agent/agent/iospecs/claim"
	//@ ft "github.com/aws/amazon-ssm-agent/agent/iospecs/fact"
	//@ "github.com/aws/amazon-ssm-agent/agent/iospecs/iospec"
	//@ pl "github.com/aws/amazon-ssm-agent/agent/iospecs/place"
	//@ pub "github.com/aws/amazon-ssm-agent/agent/iospecs/pub"
	//@ tm "github.com/aws/amazon-ssm-agent/agent/iospecs/term"
	//@ ut "github.com/aws/amazon-ssm-agent/agent/iospecs/util"
)

// buildHandshakeRequestPayload builds payload for HandshakeRequest
// @ requires log != nil && dc.Mem() && dc.getState() == BlockCipherInitialized && request.Mem()
// @ preserves acc(log.Mem(), _)
// @ ensures  dc.Mem()
// @ ensures  err == nil ==> payload.Mem() && payload.ContainsSessionTypeAction(request)
// @ ensures  err == nil ==> ((payload.Mem() && payload.ContainsSessionTypeAction(request)) --* request.Mem())
// @ ensures  err == nil && !encryptionRequested ==> dc.getState() == BlockCipherInitialized
// @ ensures  err == nil && encryptionRequested ==> dc.getState() == AgentSecretCreatedAndSigned
// @ ensures  err == nil && encryptionRequested ==> payload.ContainsSecureSessionAction(by.tuple4B(by.expB(by.generatorB(), by.gamma(dc.GetAgentShareT())), by.gamma(dc.GetAgentShareSignatureT()), by.msgB(dc.getAgentLTKeyARN()), by.msgB(dc.getLogReaderId())))
// @ ensures  err != nil ==> err.ErrorMem() && request.Mem()
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
		//@ t0 := dc.io.getToken()
		//@ rid := dc.io.getRid()
		//@ s0 := dc.io.getAbsState()
		//@ unfold iospec.P_Agent(t0, rid, s0)
		//@ unfold iospec.phiRF_Agent_14(t0, rid, s0)
		//@ agentSecretT := iospec.get_e_FrFact_r1(t0, rid)
		agentSecret, compressedPublic, err /*@, t1 @*/ := generateAndEncodeEllipticKey( /*@ t0, rid @*/ )
		if err != nil {
			//@ fold iospec.phiRF_Agent_14(t0, rid, s0)
			//@ fold iospec.P_Agent(t0, rid, s0)
			//@ fold dc.MemInternal(BlockCipherInitialized)
			//@ fold dc.Mem()
			logErrorf(log, "failed to generate client secret", err /*@, perm(1/2) @*/)
			return nil, err
		}
		//@ s1 := s0 union mset[ft.Fact]{ ft.FrFact_Agent(rid, agentSecretT) }
		//@ unfold dc.io.IoSpecMemMain()
		//@ dc.io.token = t1
		//@ dc.io.absState = s1
		//@ fold dc.io.IoSpecMemMain()

		dc.secrets.agentSecret = agentSecret

		signPayloadBytes, err := getSignAgentSharePayloadBytes(compressedPublic, dc.clientId, dc.logReaderId)
		if err != nil {
			//@ fold dc.MemInternal(BlockCipherInitialized)
			//@ fold dc.Mem()
			return nil, errHandshake()
		}

		//@ signPayloadT := ut.tuple3(tm.exp(tm.pubTerm(pub.const_g_pub()), agentSecretT), tm.pubTerm(pub.pub_msg(dc.logReaderId)), tm.pubTerm(pub.pub_msg(dc.clientId)))
		//@ t2, t3, t4, s4, m := dc.performTransitions_0_12_15(t1, rid, s1, agentSecretT, dc.secrets.agentLTKeyARN)

		sig, err /*@, signatureT @*/ := signAndEncode(dc.kmsService, dc.secrets.agentLTKeyARN, signPayloadBytes /*@, perm(1/2), t2, rid, dc.io.getAgentIdT(), dc.io.getKMSIdT(), signPayloadT, m @*/)
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
			return nil, errHandshake()
		}

		//@ t5, s5 := dc.performTransition_1(t4, rid, s4, agentSecretT, dc.secrets.agentLTKeyARN, signatureT)
		//@ unfold dc.io.IoSpecMemMain()
		//@ unfold dc.io.IoSpecMemPartial()
		//@ dc.io.token = t5
		//@ dc.io.absState = s5
		//@ dc.io.agentShareT = agentSecretT
		//@ dc.io.agentShareSignatureT = signatureT
		//@ fold dc.io.IoSpecMemPartial()
		//@ fold dc.io.IoSpecMemMain()
		//@ unfold acc(dc.MemChannelState(), 1/2)
		dc.dataChannelState = AgentSecretCreatedAndSigned
		//@ fold acc(dc.MemChannelState(), 1/2)

		req := mgsContracts.SecureSessionRequest{
			Version:        1,
			ShareAlgorithm: "P384",
			AgentShare:     compressedPublic,
			Signature:      sig,
			AgentLTKeyARN:  dc.secrets.agentLTKeyARN,
			LogReaderId:    dc.logReaderId,
		}
		//@ fold req.Mem()
		//@ fold dc.MemInternal(AgentSecretCreatedAndSigned)
		//@ fold dc.Mem()

		secureSessionAction := mgsContracts.RequestedClientAction{
			ActionType:       mgsContracts.SecureSession,
			ActionParameters: req,
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
	/*@ package (handshakeRequest.Mem() && handshakeRequest.ContainsSessionTypeAction(request)) --* request.Mem() {
		unfold handshakeRequest.Mem()
		unfold handshakeRequest.RequestedClientActions[0].Mem()
		assert handshakeRequest.RequestedClientActions[0].ActionType == mgsContracts.SessionType
		assert handshakeRequest.RequestedClientActions[0].ActionParameters == request
		assert handshakeRequest.RequestedClientActions[0].ActionParameters.(mgsContracts.SessionTypeRequest).Mem()
	} @*/

	return handshakeRequest, nil
}

/*@
ghost
decreases
requires acc(&dc.io, 1/2) && acc(dc.io.IoSpecMemPartial(), 1/2)
requires pl.token(t0) && iospec.P_Agent(t0, rid, s0)
requires ft.Setup_Agent(rid, dc.io.getAgentIdT(), dc.io.getKMSIdT(), dc.io.getClientIdT(), dc.io.getReaderIdT(), tm.pubTerm(pub.pub_msg(agentLTKeyARN)), dc.io.getLogLTPkT()) in s0
requires ft.FrFact_Agent(rid, agentSecretT) in s0
ensures  acc(&dc.io, 1/2) && acc(dc.io.IoSpecMemPartial(), 1/2)
ensures  pl.token(t1) && iospec.P_Agent(t3, rid, s3)
ensures  iospec.e_Out_KMS(t1, rid, dc.io.getAgentIdT(), dc.io.getKMSIdT(), rid, m) && t2 == iospec.get_e_Out_KMS_placeDst(t1, rid, dc.io.getAgentIdT(), dc.io.getKMSIdT(), rid, m)
ensures  iospec.e_In_KMS(t2, rid) && t3 == iospec.get_e_In_KMS_placeDst(t2, rid)
ensures  ft.St_Agent_1(rid, dc.io.getAgentIdT(), dc.io.getKMSIdT(), dc.io.getClientIdT(), dc.io.getReaderIdT(), tm.pubTerm(pub.pub_msg(agentLTKeyARN)), dc.io.getLogLTPkT(), agentSecretT) in s3
ensures  ft.In_KMS_Agent(rid, iospec.get_e_In_KMS_r1(t2, rid), iospec.get_e_In_KMS_r2(t2, rid), iospec.get_e_In_KMS_r3(t2, rid), iospec.get_e_In_KMS_r4(t2, rid)) in s3
ensures  m == ut.tuple5(tm.pubTerm(pub.const_SignRequest_pub()), tm.pubTerm(pub.pub_msg(agentLTKeyARN)), tm.exp(tm.pubTerm(pub.const_g_pub()), agentSecretT), dc.io.getReaderIdT(), dc.io.getClientIdT())
func (dc *dataChannel) performTransitions_0_12_15(t0 pl.Place, rid tm.Term, s0 mset[ft.Fact], agentSecretT tm.Term, agentLTKeyARN string) (t1, t2, t3 pl.Place, s3 mset[ft.Fact], m tm.Term) {
	agentIdT := dc.io.getAgentIdT()
	kmsIdT := dc.io.getKMSIdT()
	clientIdT := dc.io.getClientIdT()
	readerIdT := dc.io.getReaderIdT()
	agentLtKeyIdT := tm.pubTerm(pub.pub_msg(agentLTKeyARN))
	signPayloadT := tm.pair(tm.exp(tm.pubTerm(pub.const_g_pub()), agentSecretT), tm.pair(readerIdT, clientIdT))
	logPkT := dc.io.getLogLTPkT()

	// unfold phiR_Agent_0 to obtain Out_KMS_Agent fact
	m = tm.pair(tm.pubTerm(pub.const_SignRequest_pub()), tm.pair(agentLtKeyIdT, signPayloadT))
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
	unfold iospec.P_Agent(t0, rid, s0)
	unfold iospec.phiR_Agent_0(t0, rid, s0)
	t1 = iospec.internBIO_e_Agent_SendSignRequest(t0, rid, agentIdT, kmsIdT, clientIdT, readerIdT, agentLtKeyIdT, logPkT, agentSecretT, l, a, r)
	s1 := ft.U(l, r, s0)

	// unfold phiRG_Agent_12 to obtain e_Out_KMS permission
	unfold iospec.P_Agent(t1, rid, s1)
	unfold iospec.phiRG_Agent_12(t1, rid, s1)
	t2 = iospec.get_e_Out_KMS_placeDst(t1, rid, agentIdT, kmsIdT, rid, m)
	s2 := s1 setminus mset[ft.Fact] { ft.Out_KMS_Agent(rid, agentIdT, kmsIdT, rid, m) }

	// unfold phiRF_Agent_15 to obtain e_In_KMS permission since `signAndEncode` performs a send and receive operation
	unfold iospec.P_Agent(t2, rid, s2)
	unfold iospec.phiRF_Agent_15(t2, rid, s2)
	t3 = iospec.get_e_In_KMS_placeDst(t2, rid)
	s3 = s2 union mset[ft.Fact] { ft.In_KMS_Agent(rid, iospec.get_e_In_KMS_r1(t2, rid), iospec.get_e_In_KMS_r2(t2, rid), iospec.get_e_In_KMS_r3(t2, rid), iospec.get_e_In_KMS_r4(t2, rid)) }
}

ghost
decreases
requires acc(&dc.io, 1/2) && acc(dc.io.IoSpecMemPartial(), 1/2)
requires pl.token(t0) && iospec.P_Agent(t0, rid, s0)
requires ft.St_Agent_1(rid, dc.io.getAgentIdT(), dc.io.getKMSIdT(), dc.io.getClientIdT(), dc.io.getReaderIdT(), tm.pubTerm(pub.pub_msg(agentLTKeyARN)), dc.io.getLogLTPkT(), agentSecretT) in s0
requires ft.In_KMS_Agent(rid, dc.io.getKMSIdT(), dc.io.getAgentIdT(), rid, tm.pair(tm.pubTerm(pub.const_SignResponse_pub()), signatureT)) in s0
ensures  acc(&dc.io, 1/2) && acc(dc.io.IoSpecMemPartial(), 1/2)
ensures  pl.token(t1) && iospec.P_Agent(t1, rid, s1)
ensures  ft.St_Agent_2(rid, dc.io.getAgentIdT(), dc.io.getKMSIdT(), dc.io.getClientIdT(), dc.io.getReaderIdT(), tm.pubTerm(pub.pub_msg(agentLTKeyARN)), dc.io.getLogLTPkT(), agentSecretT, signatureT) in s1
func (dc *dataChannel) performTransition_1(t0 pl.Place, rid tm.Term, s0 mset[ft.Fact], agentSecretT tm.Term, agentLTKeyARN string, signatureT tm.Term) (t1 pl.Place, s1 mset[ft.Fact]) {
	agentIdT := dc.io.getAgentIdT()
	kmsIdT := dc.io.getKMSIdT()
	clientIdT := dc.io.getClientIdT()
	readerIdT := dc.io.getReaderIdT()
	agentLtKeyIdT := tm.pubTerm(pub.pub_msg(agentLTKeyARN))
	signPayloadT := tm.pair(tm.exp(tm.pubTerm(pub.const_g_pub()), agentSecretT), tm.pair(readerIdT, clientIdT))
	logPkT := dc.io.getLogLTPkT()

	// unfold phiR_Agent_1 to transition to St_Agent_2
	l := mset[ft.Fact] {
		ft.St_Agent_1(rid, agentIdT, kmsIdT, clientIdT, readerIdT, agentLtKeyIdT, logPkT, agentSecretT),
		ft.In_KMS_Agent(rid, kmsIdT, agentIdT, rid, tm.pair(tm.pubTerm(pub.const_SignResponse_pub()), signatureT)),
	}
	a := mset[cl.Claim] {
		cl.AgentSignResponse(kmsIdT, agentIdT, rid, tm.pair(tm.pubTerm(pub.const_SignResponse_pub()), signatureT)),
	}
	r := mset[ft.Fact] {
		ft.St_Agent_2(rid, agentIdT, kmsIdT, clientIdT, readerIdT, agentLtKeyIdT, logPkT, agentSecretT, signatureT),
	}
	unfold iospec.P_Agent(t0, rid, s0)
	unfold iospec.phiR_Agent_1(t0, rid, s0)
	t1 = iospec.internBIO_e_Agent_RecvSignResponse(t0, rid, agentIdT, kmsIdT, clientIdT, readerIdT, agentLtKeyIdT, logPkT, agentSecretT, signatureT, l, a, r)
	s1 = ft.U(l, r, s0)
}
@*/

// sendHandshakeRequest sends handshake request
// @ requires log != nil && handshakeRequestPayload.Mem() && handshakeRequestPayload.ContainsSessionTypeAction(request)
// @ requires dc.Mem() && dc.getState() >= BlockCipherInitialized
// @ requires unfolding acc(dc.Mem(), _) in unfolding acc(dc.MemInternal(dc.dataChannelState), _) in dc.encryptionEnabled ==>
// @	dc.dataChannelState == AgentSecretCreatedAndSigned &&
// @	handshakeRequestPayload.ContainsSecureSessionAction(by.tuple4B(by.expB(by.generatorB(), by.gamma(dc.io.getAgentShareT())), by.gamma(dc.io.getAgentShareSignatureT()), by.msgB(dc.secrets.agentLTKeyARN), by.msgB(dc.logReaderId)))
// @ preserves acc(log.Mem(), _)
// @ ensures  dc.Mem() && handshakeRequestPayload.Mem() && handshakeRequestPayload.ContainsSessionTypeAction(request)
// @ ensures  err == nil ==> dc.getState() == HandshakeRequestSent
// @ ensures  err != nil ==> err.ErrorMem()
func (dc *dataChannel) sendHandshakeRequest(log logger.T, handshakeRequestPayload *mgsContracts.HandshakeRequestPayload /*@, ghost request mgsContracts.SessionTypeRequest @*/) (err error) {
	//@ secActionB := unfolding acc(dc.Mem(), _) in unfolding acc(dc.MemInternal(dc.dataChannelState), _) in by.tuple4B(by.expB(by.generatorB(), by.gamma(dc.io.getAgentShareT())), by.gamma(dc.io.getAgentShareSignatureT()), by.msgB(dc.secrets.agentLTKeyARN), by.msgB(dc.logReaderId))
	var handshakeRequestPayloadBytes []byte
	if handshakeRequestPayloadBytes, err = marshalHandshakeRequest(handshakeRequestPayload /*@, perm(1/2), secActionB @*/); err != nil {
		return fmtErrorf("Could not serialize HandshakeRequest message", err /*@, perm(1/1) @*/)
	}

	logDebug(log, "Sending Handshake Request.")
	// logHandshakeRequest(log, handshakeRequestPayload /*@, perm(1/2) @*/)

	//@ unfold dc.Mem()
	//@ state := dc.dataChannelState
	//@ unfold dc.MemInternal(state)
	//@ secActionT := tm.pair(tm.exp(tm.pubTerm(pub.const_g_pub()), dc.io.getAgentShareT()), tm.pair(dc.io.getAgentShareSignatureT(), tm.pair(tm.pubTerm(pub.pub_msg(dc.secrets.agentLTKeyARN)), tm.pubTerm(pub.pub_msg(dc.logReaderId)))))
	//@ t0 := dc.io.getToken()
	//@ rid := dc.io.getRid()
	//@ s0 := dc.io.getAbsState()
	/*@
	agentIdT := dc.io.getAgentIdT()
	kmsIdT := dc.io.getKMSIdT()
	clientIdT := dc.io.getClientIdT()
	readerIdT := dc.io.getReaderIdT()
	agentLtKeyIdT := tm.pubTerm(pub.pub_msg(dc.secrets.agentLTKeyARN))
	logPkT := dc.io.getLogLTPkT()
	agentSecretT := dc.io.getAgentShareT()
	signatureT := dc.io.getAgentShareSignatureT()
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
	//@ unfold dc.io.IoSpecMemMain()
	//@ dc.io.token = t1
	//@ dc.io.absState = s1
	//@ fold dc.io.IoSpecMemMain()
	//@ unfold acc(dc.MemChannelState(), 1/2)
	dc.dataChannelState = HandshakeRequestSent
	//@ fold acc(dc.MemChannelState(), 1/2)
	//@ fold dc.MemInternal(HandshakeRequestSent)
	//@ fold dc.Mem()

	if err = dc.sendData(log, mgsContracts.HandshakeRequest, handshakeRequestPayloadBytes /*@, secActionT, false, false @*/); err != nil {
		return fmtErrorf("Failed sending of HandshakeRequest message, err", err /*@, perm(1/1) @*/)
	}
	return nil
}
