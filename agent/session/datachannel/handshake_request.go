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
)

// buildHandshakeRequestPayload builds payload for HandshakeRequest
// @ requires log != nil && dc.Mem() && dc.getState() == BlockCipherInitialized && request.Mem()
// @ preserves acc(log.Mem(), _)
// @ ensures  dc.Mem()
// @ ensures  err == nil ==> payload.Mem() && payload.ContainsSessionTypeAction(request)
// @ ensures  err == nil ==> ((payload.Mem() && payload.ContainsSessionTypeAction(request)) --* request.Mem())
// @ ensures  err == nil && !encryptionRequested ==> dc.getState() == BlockCipherInitialized
// @ ensures  err == nil && encryptionRequested ==> dc.getState() == AgentSecretCreatedAndSigned
// @ ensures  err == nil && encryptionRequested ==> unfolding acc(dc.Mem(), _) in unfolding acc(dc.MemInternal(AgentSecretCreatedAndSigned), _) in (
// @	payload.ContainsSecureSessionAction(by.tuple4B(by.expB(by.generatorB(), by.gamma(dc.getAgentShareT())), by.gamma(dc.getAgentShareSignatureT()), by.msgB(dc.secrets.agentLTKeyARN), by.msgB(dc.logReaderId))))
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
			logErrorf(log, "failed to generate client secret", err /*@, perm(1/2) @*/)
			return nil, err
		}
		//@ s1 := s0 union mset[ft.Fact]{ ft.FrFact_Agent(rid, agentSecretT) }
		//@ unfold dc.IoSpecMemMain()
		//@ dc.setToken(t1)
		//@ dc.setAbsState(s1)
		//@ fold dc.IoSpecMemMain()

		dc.secrets.agentSecret = agentSecret

		signPayloadBytes, err := getSignAgentSharePayloadBytes(compressedPublic, dc.clientId, dc.logReaderId)
		if err != nil { //argot:ignore
			//@ fold dc.MemInternal(BlockCipherInitialized)
			//@ fold dc.Mem()
			return nil, errHandshake()
		}
		//@ signPayloadT := tm.pair(tm.exp(tm.pubTerm(pub.const_g_pub()), agentSecretT), tm.pair(tm.pubTerm(pub.pub_msg(dc.logReaderId)), tm.pubTerm(pub.pub_msg(dc.clientId))))

		// unfold phiR_Agent_0 to obtain Out_KMS_Agent fact
		/*@
			agentIdT := dc.getAgentIdT()
			kmsIdT := dc.getKMSIdT()
			clientIdT := dc.getClientIdT()
			readerIdT := dc.getReaderIdT()
			agentLtKeyIdT := tm.pubTerm(pub.pub_msg(dc.secrets.agentLTKeyARN))
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

		sig, err /*@, signatureT @*/ := signAndEncode(dc.kmsService, dc.secrets.agentLTKeyARN, signPayloadBytes /*@, perm(1/2), t2, rid, agentIdT, kmsIdT, signPayloadT, m @*/)
		if err != nil { //argot:ignore
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

// sendHandshakeRequest sends handshake request
// @ requires log != nil && handshakeRequestPayload.Mem() && handshakeRequestPayload.ContainsSessionTypeAction(request)
// @ requires dc.Mem() && dc.getState() >= BlockCipherInitialized
// @ requires unfolding acc(dc.Mem(), _) in unfolding acc(dc.MemInternal(dc.dataChannelState), _) in dc.encryptionEnabled ==>
// @	dc.dataChannelState == AgentSecretCreatedAndSigned &&
// @	handshakeRequestPayload.ContainsSecureSessionAction(by.tuple4B(by.expB(by.generatorB(), by.gamma(dc.getAgentShareT())), by.gamma(dc.getAgentShareSignatureT()), by.msgB(dc.secrets.agentLTKeyARN), by.msgB(dc.logReaderId)))
// @ preserves acc(log.Mem(), _)
// @ ensures  dc.Mem() && handshakeRequestPayload.Mem() && handshakeRequestPayload.ContainsSessionTypeAction(request)
// @ ensures  err == nil ==> dc.getState() == HandshakeRequestSent
// @ ensures  err != nil ==> err.ErrorMem()
func (dc *dataChannel) sendHandshakeRequest(log logger.T, handshakeRequestPayload *mgsContracts.HandshakeRequestPayload /*@, ghost request mgsContracts.SessionTypeRequest @*/) (err error) {
	//@ secActionB := unfolding acc(dc.Mem(), _) in unfolding acc(dc.MemInternal(dc.dataChannelState), _) in by.tuple4B(by.expB(by.generatorB(), by.gamma(dc.getAgentShareT())), by.gamma(dc.getAgentShareSignatureT()), by.msgB(dc.secrets.agentLTKeyARN), by.msgB(dc.logReaderId))
	var handshakeRequestPayloadBytes []byte
	if handshakeRequestPayloadBytes, err = marshalHandshakeRequest(handshakeRequestPayload /*@, perm(1/2), secActionB @*/); err != nil {
		return fmtErrorf("Could not serialize HandshakeRequest message", err /*@, perm(1/1) @*/)
	}

	logDebug(log, "Sending Handshake Request.")
	// logHandshakeRequest(log, handshakeRequestPayload /*@, perm(1/2) @*/)

	//@ unfold dc.Mem()
	//@ state := dc.dataChannelState
	//@ unfold dc.MemInternal(state)
	//@ secActionT := tm.pair(tm.exp(tm.pubTerm(pub.const_g_pub()), dc.getAgentShareT()), tm.pair(dc.getAgentShareSignatureT(), tm.pair(tm.pubTerm(pub.pub_msg(dc.secrets.agentLTKeyARN)), tm.pubTerm(pub.pub_msg(dc.logReaderId)))))
	//@ t0 := dc.getToken()
	//@ rid := dc.getRid()
	//@ s0 := dc.getAbsState()
	/*@
	agentIdT := dc.getAgentIdT()
	kmsIdT := dc.getKMSIdT()
	clientIdT := dc.getClientIdT()
	readerIdT := dc.getReaderIdT()
	agentLtKeyIdT := tm.pubTerm(pub.pub_msg(dc.secrets.agentLTKeyARN))
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

	if err = dc.sendData(log, mgsContracts.HandshakeRequest, handshakeRequestPayloadBytes /*@, secActionT, false, false @*/); err != nil {
		return fmtErrorf("Failed sending of HandshakeRequest message, err", err /*@, perm(1/1) @*/)
	}
	return nil
}
