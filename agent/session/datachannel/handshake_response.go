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
	"encoding/base64"

	mgsContracts "github.com/aws/amazon-ssm-agent/agent/session/contracts"
	"github.com/aws/amazon-ssm-agent/agent/session/datachannel/iosanitization"
	//@ abs "github.com/aws/amazon-ssm-agent/agent/iospecs/abs"
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

// handleHandshakeResponse is the handler for payload type HandshakeResponse
// @ requires dc.MemTransfer(HandshakeRequestSent, encryptionEnabled)
// @ requires streamDataMessage.Mem()
// @ requires unfolding streamDataMessage.Mem() in mgsContracts.PayloadType(streamDataMessage.PayloadType) == mgsContracts.HandshakeResponse
// @ requires unfolding dc.MemTransfer(HandshakeRequestSent, encryptionEnabled) in by.gamma(dc.io.getInFactT()) == streamDataMessage.Abs() && ft.InFact_Agent(dc.io.getRid(), dc.io.getInFactT()) in dc.io.getAbsState()
// @ preserves dc.RecvRoutineMem()
// @ ensures  streamDataMessage.Mem()
// @ ensures  err != nil ==> err.ErrorMem()
func (dc *dataChannel) handleHandshakeResponse(streamDataMessage *mgsContracts.AgentMessage, encryptionEnabled bool) (err error) {
	//@ unfold streamDataMessage.Mem()
	handshakeResponse, err := unmarshalHandshakeResponse(streamDataMessage.Payload /*@, perm(1/2) @*/)
	//@ fold streamDataMessage.Mem()
	if err != nil {
		return fmtErrorf("Unmarshalling of HandshakeResponse message failed", err /*@, perm(1/1) @*/)
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
	//@ invariant acc(streamDataMessage.Mem(), 1/2)
	//@ invariant unfolding acc(streamDataMessage.Mem(), 1/2) in
	//@		mgsContracts.PayloadType(streamDataMessage.PayloadType) == mgsContracts.HandshakeResponse &&
	//@ 	abs.Abs(streamDataMessage.Payload) == handshakeResponse.Abs()
	//@ invariant i <= 1 ==> !containsSecureSessionAction
	//@ invariant !containsSecureSessionAction ==> unfolding dc.MemTransfer(state, encryptionEnabled) in by.gamma(dc.io.getInFactT()) == streamDataMessage.Abs() && ft.InFact_Agent(dc.io.getRid(), dc.io.getInFactT()) in dc.io.getAbsState()
	for i := 0; i < len(actions); i++ {
		//@ unfold acc(handshakeResponse.Mem(), 1/2)
		//@ unfold acc(actions[i].Mem(), 1/2)
		action := actions[i]
		if action.ActionStatus != mgsContracts.Success {
			err = fmtErrorActionFailure(action.ActionType, action.ActionStatus, action.Error)
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
						state, err = dc.processSecureSessionResponse(&actions[i])
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
		// logError(log, err /*@, perm(1/1) @*/)
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
	//@ fold acc(handshakeResponse.Mem(), 1/2)
	//@ fold dc.MemTransfer(state, encryptionEnabled)
	payload := ResponseChanPayload{encryptionEnabled, state}
	//@ fold ResponseChanInv!<dc, _!>(payload)
	//@ unfold dc.RecvRoutineMem()
	dc.hs.responseChan <- payload
	//@ fold dc.RecvRoutineMem()
	return nil
}

// @ requires dc.MemTransfer(HandshakeRequestSent, true) && acc(action.Mem(), 1/4) && action.IsSuccessfulSecureSession()
// @ requires unfolding dc.MemTransfer(HandshakeRequestSent, true) in by.gamma(dc.io.getInFactT()) == by.pairB(by.gamma(mgsContracts.payloadTypeTerm(mgsContracts.HandshakeResponse)), action.Abs()) && ft.InFact_Agent(dc.io.getRid(), dc.io.getInFactT()) in dc.io.getAbsState()
// @ ensures  dc.MemTransfer(state, true) && acc(action.Mem(), 1/4)
// @ ensures  err == nil ==> state == BlockCipherReady
// @ ensures  err != nil ==> err.ErrorMem()
func (dc *dataChannel) processSecureSessionResponse(action *mgsContracts.ProcessedClientAction) (state DataChannelState, err error) {
	state, err = dc.verifySecureSessionResponse(action)
	if err != nil {
		state = Erroneous
		return state, errHandshake()
	}

	state, err = dc.completeSecureSessionResponseProcessing()
	if err != nil {
		state = Erroneous
		return state, errHandshake()
	}

	return state, nil
}

// @ requires dc.MemTransfer(HandshakeRequestSent, true) && acc(action.Mem(), 1/8) && action.IsSuccessfulSecureSession()
// @ requires unfolding dc.MemTransfer(HandshakeRequestSent, true) in by.gamma(dc.io.getInFactT()) == by.pairB(by.gamma(mgsContracts.payloadTypeTerm(mgsContracts.HandshakeResponse)), action.Abs()) && ft.InFact_Agent(dc.io.getRid(), dc.io.getInFactT()) in dc.io.getAbsState()
// @ ensures  dc.MemTransfer(state, true) && acc(action.Mem(), 1/8)
// @ ensures  err == nil ==> state == HandshakeResponseVerified
// @ ensures  err != nil ==> err.ErrorMem() && state == Erroneous
func (dc *dataChannel) verifySecureSessionResponse(action *mgsContracts.ProcessedClientAction) (state DataChannelState, err error) {
	state = HandshakeRequestSent
	//@ unfold acc(action.Mem(), 1/8)
	resp, err := unmarshalSecureSessionResponse(action.ActionResult /*@, perm(1/16) @*/)
	//@ fold acc(action.Mem(), 1/8)
	if err != nil {
		//@ unfold dc.MemTransfer(state, true)
		state = Erroneous
		//@ fold dc.MemTransfer(state, true)
		return state, errHandshake()
	}

	// decode the client share
	//@ unfold resp.Mem()
	//@ unfold dc.MemTransfer(state, true)
	sharedSecret, err /*@, clientSecretB @*/ := unmarshalAndCheckClientShare(resp.ClientShare, dc.secrets.agentSecret /*@, perm(1/2) @*/)
	if err != nil {
		state = Erroneous
		//@ fold dc.MemTransfer(state, true)
		return state, errHandshake()
	}

	dc.secrets.sharedSecret = sharedSecret

	// hash the shared secret to obtain the session identifier
	dc.secrets.sessionID = computeSHA384(sharedSecret /*@, 1/2 @*/)

	// decode the session ID
	sessionIDBytes, err := base64.StdEncoding.DecodeString(resp.SessionID)
	if err != nil {
		state = Erroneous
		//@ fold dc.MemTransfer(state, true)
		return state, errHandshake()
	}

	if !equal(dc.secrets.sessionID, sessionIDBytes) {
		state = Erroneous
		//@ fold dc.MemTransfer(state, true)
		return state, errHandshake()
	}

	//@ receivedMsgT := dc.io.getInFactT()
	//@ xT := dc.io.getAgentShareT()
	//@ sigYB := by.msgB(resp.Signature)
	//@ clientLtKeyIdB := by.msgB(resp.ClientLTKeyARN)
	//@ t0 := dc.io.getToken()
	//@ rid, AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, xT, SigX := dc.io.getRid(), dc.io.getAgentIdT(), dc.io.getKMSIdT(), dc.io.getClientIdT(), dc.io.getReaderIdT(), tm.pubTerm(pub.pub_msg(dc.secrets.agentLTKeyARN)), dc.io.getLogLTPkT(), dc.io.getAgentShareT(), dc.io.getAgentShareSignatureT()
	//@ s0 := dc.io.getAbsState()

	// retrieve the term representation of `clientSecretT`, `sigYT`, and `clientLtKeyIdT` by applying our term-uniqueness assumption of the received message:
	//@ clientSecretT, sigYT, clientLtKeyIdT := pattern.patternRequirementSecSessResp(rid, AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, xT, SigX, by.oneTerm(clientSecretB), by.oneTerm(sigYB), by.oneTerm(clientLtKeyIdB), receivedMsgT, t0, s0)
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
	//@ unfold dc.io.IoSpecMemMain()
	//@ unfold dc.io.IoSpecMemPartial()
	//@ dc.io.token = t1
	//@ dc.io.absState = s1
	//@ dc.io.sharedSecretT = sharedSecretT
	//@ dc.io.clientLtKeyIdT = clientLtKeyIdT
	//@ dc.io.clientShareT = clientSecretT
	//@ dc.io.clientShareSignatureT = sigYT
	//@ fold dc.io.IoSpecMemPartial()
	//@ fold dc.io.IoSpecMemMain()
	state = HandshakeResponseReceived

	// verify client signature
	sig, err := base64.StdEncoding.DecodeString(resp.Signature)
	if err != nil {
		state = Erroneous
		//@ fold dc.MemTransfer(state, true)
		err = errHandshake()
		return
	}

	agentId := dc.instanceId
	//@ fold dc.MemTransfer(state, true)

	clientSignPayloadBytes, err := getVerifyPayloadBytes(resp.ClientShare, agentId)
	if err != nil {
		//@ unfold dc.MemTransfer(state, true)
		state = Erroneous
		//@ fold dc.MemTransfer(state, true)
		err = errHandshake()
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
	ok, err := iosanitization.KMSVerify(dc.kmsService, resp.ClientLTKeyARN, clientSignPayloadBytes, sig /*@, perm(1/2), t2, rid, AgentId, KMSId, ClientId, clientLtKeyIdT, messageT, sigYT, verifyReqT @*/) // call to function has the necessary I/O spec
	if !ok {
		state = Erroneous
		//@ fold dc.MemTransfer(state, true)
		err = errHandshake()
		return
	}
	if err != nil {
		state = Erroneous
		//@ fold dc.MemTransfer(state, true)
		err = errHandshake()
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
	//@ unfold dc.io.IoSpecMemMain()
	//@ unfold dc.io.IoSpecMemPartial()
	//@ dc.io.token = t5
	//@ dc.io.absState = s5
	//@ fold dc.io.IoSpecMemPartial()
	//@ fold dc.io.IoSpecMemMain()
	state = HandshakeResponseVerified
	//@ fold dc.MemTransfer(state, true)
	return
}

// @ requires dc.MemTransfer(HandshakeResponseVerified, true)
// @ ensures  dc.MemTransfer(state, true)
// @ ensures  err == nil ==> state == BlockCipherReady
// @ ensures  err != nil ==> err.ErrorMem() && state == Erroneous
func (dc *dataChannel) completeSecureSessionResponseProcessing() (state DataChannelState, err error) {
	state = HandshakeResponseVerified
	//@ unfold dc.MemTransfer(state, true)
	//@ rid, AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, xT, SigX := dc.io.getRid(), dc.io.getAgentIdT(), dc.io.getKMSIdT(), dc.io.getClientIdT(), dc.io.getReaderIdT(), tm.pubTerm(pub.pub_msg(dc.secrets.agentLTKeyARN)), dc.io.getLogLTPkT(), dc.io.getAgentShareT(), dc.io.getAgentShareSignatureT()
	//@ t0 := dc.io.getToken()
	//@ s0 := dc.io.getAbsState()
	sharedSecret := dc.secrets.sharedSecret
	//@ sharedSecretT := dc.io.getSharedSecretT()
	//@ clientLtKeyIdT := dc.io.getClientLtKeyIdT()
	//@ clientSecretT := dc.io.getClientShareT()
	//@ sigYT := dc.io.getClientShareSignatureT()

	// use the shared secret to generate read and write keys
	agentWriteKey, err := computeKdf(sharedSecret, true /*@, perm(1/8) @*/)
	if err != nil {
		state = Erroneous
		//@ fold dc.MemTransfer(state, true)
		return state, errHandshake()
	}
	dc.secrets.agentWriteKey = agentWriteKey

	agentReadKey, err := computeKdf(sharedSecret, false /*@, perm(1/8) @*/)
	if err != nil {
		state = Erroneous
		//@ fold dc.MemTransfer(state, true)
		return state, errHandshake()
	}
	dc.secrets.agentReadKey = agentReadKey

	sessionKeysBytes, err := getSessionKeysPayload(agentWriteKey, agentReadKey /*@, perm(1/8) @*/)
	if err != nil {
		state = Erroneous
		//@ fold dc.MemTransfer(state, true)
		return state, errHandshake()
	}
	//@ sessionKeysBytesT := tm.pair(tm.kdf1(sharedSecretT), tm.kdf2(sharedSecretT))
	//@ assert abs.Abs(sessionKeysBytes) == by.gamma(sessionKeysBytesT)

	encodedEncryptedSessionKeys, err := encryptAndEncode(sessionKeysBytes, dc.logLTPk /*@, perm(1/2) @*/)
	if err != nil {
		state = Erroneous
		//@ fold dc.MemTransfer(state, true)
		return state, errHandshake()
	}
	//@ encodedEncryptedSessionKeysT := tm.aenc(sessionKeysBytesT, dc.io.getLogLTPkT())
	//@ assert by.msgB(encodedEncryptedSessionKeys) == by.gamma(encodedEncryptedSessionKeysT)

	// sign ciphertext containing session keys using KMS:
	signSessionKeysPayloadBytes, err := getSignSessionKeysPayloadBytes(encodedEncryptedSessionKeys, dc.clientId)
	if err != nil {
		state = Erroneous
		//@ fold dc.MemTransfer(state, true)
		return state, errHandshake()
	}
	//@ messageT := tm.pair(encodedEncryptedSessionKeysT, dc.io.getClientIdT())
	//@ assert abs.Abs(signSessionKeysPayloadBytes) == by.gamma(messageT)
	//@ m := ut.tuple3(tm.pubTerm(pub.const_SignRequest_pub()), tm.pubTerm(pub.pub_msg(dc.secrets.agentLTKeyARN)), messageT)
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
	encodedSigSessionKeys, err /*@, sigSessionKeysT @*/ := signAndEncode(dc.kmsService, dc.secrets.agentLTKeyARN, signSessionKeysPayloadBytes /*@, perm(1/2), t1, rid, AgentId, KMSId, messageT, m @*/)
	if err != nil {
		state = Erroneous
		//@ fold dc.MemTransfer(state, true)
		return state, errHandshake()
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
	encodedEncryptedSessionKeysPayloadBytes, err := getEncryptedSessionKeysPayload(encodedEncryptedSessionKeys, encodedSigSessionKeys, dc.instanceId, dc.secrets.agentLTKeyARN, dc.clientId)
	if err != nil {
		state = Erroneous
		//@ fold dc.MemTransfer(state, true)
		return state, errHandshake()
	}

	_ = encodedEncryptedSessionKeysPayloadBytes // TODO send to log server

	//@ encryptedSessionKeysPayloadT := ut.tuple5(encodedEncryptedSessionKeysT, sigSessionKeysT, AgentId, AgentLtKeyId, ClientId)
	//@ assert by.msgB(encodedEncryptedSessionKeysPayloadBytes) == by.gamma(encryptedSessionKeysPayloadT)

	// TODO: actually send `encodedEncryptedSessionKeysPayloadBytes` to the log server!
	// use `phiRG_Agent_13` and the `OutFact_Agent` fact in s5 to obtain the corresponding send permission
	//@ assert ft.OutFact_Agent(rid, tm.pair(tm.pubTerm(pub.const_EncryptedSessionKey_pub()), encryptedSessionKeysPayloadT)) in s5

	if err := dc.blockCipher.UpdateEncryptionKeys(dc.secrets.agentReadKey, dc.secrets.agentWriteKey /*@, perm(1/2), tm.kdf2(sharedSecretT), tm.kdf1(sharedSecretT) @*/); err != nil {
		state = Erroneous
		//@ fold dc.MemTransfer(state, true)
		return state, errHandshake()
	}

	//@ unfold dc.io.IoSpecMemMain()
	//@ unfold dc.io.IoSpecMemPartial()
	//@ dc.io.token = t5
	//@ dc.io.absState = s5
	//@ dc.io.sigSessionKeysT = sigSessionKeysT
	//@ fold dc.io.IoSpecMemPartial()
	//@ fold dc.io.IoSpecMemMain()
	state = BlockCipherReady
	dc.encryptionEnabled = true
	//@ fold dc.MemTransfer(state, true)
	return
}
