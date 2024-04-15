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
	"crypto/elliptic"
	cryptoRand "crypto/rand"
	"crypto/rsa"
	"encoding/base64"
	"encoding/json"

	//@ "bytes"

	mgsContracts "github.com/aws/amazon-ssm-agent/agent/session/contracts"
	"github.com/aws/amazon-ssm-agent/agent/session/crypto"
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
// @ requires unfolding dc.MemTransfer(HandshakeRequestSent, encryptionEnabled) in by.gamma(dc.getInFactT()) == streamDataMessage.Abs() && ft.InFact_Agent(dc.getRid(), dc.getInFactT()) in dc.getAbsState()
// @ preserves dc.RecvRoutineMem()
// @ ensures  streamDataMessage.Mem()
// @ ensures  err != nil ==> err.ErrorMem()
func (dc *dataChannel) handleHandshakeResponse(streamDataMessage *mgsContracts.AgentMessage, encryptionEnabled bool) (err error) {
	// logDebug(log, "Received Handshake Response.")
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
	//@ invariant !containsSecureSessionAction ==> unfolding dc.MemTransfer(state, encryptionEnabled) in by.gamma(dc.getInFactT()) == streamDataMessage.Abs() && ft.InFact_Agent(dc.getRid(), dc.getInFactT()) in dc.getAbsState()
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
				// logUnknownActionType(log, action.ActionType)
			}
		}
		if err != nil { //argot:ignore
			break
		}
	}

	if err == nil && encryptionEnabled && !containsSecureSessionAction { //argot:ignore
		err = fmtError("No 'SecureSession' action found despite encryption being enabled")
	}
	if err != nil { //argot:ignore
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
	// logInfoString(log, "Client side session manager plugin version is", handshakeResponse.ClientVersion)
	//@ fold acc(handshakeResponse.Mem(), 1/2)
	//@ fold dc.MemTransfer(state, encryptionEnabled)
	payload := ResponseChanPayload{encryptionEnabled, state}
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

// @ requires dc.MemTransfer(HandshakeRequestSent, true) && acc(action.Mem(), 1/4) && action.IsSuccessfulSecureSession()
// @ requires unfolding dc.MemTransfer(HandshakeRequestSent, true) in by.gamma(dc.getInFactT()) == by.pairB(by.gamma(mgsContracts.payloadTypeTerm(mgsContracts.HandshakeResponse)), action.Abs()) && ft.InFact_Agent(dc.getRid(), dc.getInFactT()) in dc.getAbsState()
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
// @ requires unfolding dc.MemTransfer(HandshakeRequestSent, true) in by.gamma(dc.getInFactT()) == by.pairB(by.gamma(mgsContracts.payloadTypeTerm(mgsContracts.HandshakeResponse)), action.Abs()) && ft.InFact_Agent(dc.getRid(), dc.getInFactT()) in dc.getAbsState()
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
	if err != nil { //argot:ignore
		state = Erroneous
		//@ fold dc.MemTransfer(state, true)
		return state, errHandshake()
	}

	dc.secrets.sharedSecret = sharedSecret

	// hash the shared secret to obtain the session identifier
	dc.secrets.sessionID = computeSHA384(sharedSecret /*@, 1/2 @*/)
	// logDebugHex(log, "agent computed session ID", base64.StdEncoding.EncodeToString(dc.state.sessionID /*@, perm(1/2) @*/))

	// decode the session ID
	sessionIDBytes, err := base64.StdEncoding.DecodeString(resp.SessionID)
	if err != nil { //argot:ignore
		state = Erroneous
		//@ fold dc.MemTransfer(state, true)
		return state, errHandshake()
	}

	if !equal(dc.secrets.sessionID, sessionIDBytes) { //argot:ignore
		state = Erroneous
		//@ fold dc.MemTransfer(state, true)
		return state, errHandshake()
	}

	//@ receivedMsgT := dc.getInFactT()
	//@ xT := dc.getAgentShareT()
	//@ sigYB := by.msgB(resp.Signature)
	//@ clientLtKeyIdB := by.msgB(resp.ClientLTKeyARN)
	//@ t0 := dc.getToken()
	//@ rid, AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, xT, SigX := dc.getRid(), dc.getAgentIdT(), dc.getKMSIdT(), dc.getClientIdT(), dc.getReaderIdT(), tm.pubTerm(pub.pub_msg(dc.secrets.agentLTKeyARN)), dc.getLogLTPkT(), dc.getAgentShareT(), dc.getAgentShareSignatureT()
	//@ s0 := dc.getAbsState()

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
	if err != nil { //argot:ignore
		state = Erroneous
		//@ fold dc.MemTransfer(state, true)
		err = errHandshake()
		return
	}

	agentId := dc.instanceId
	//@ fold dc.MemTransfer(state, true)

	clientSignPayloadBytes, err := getVerifyPayloadBytes(resp.ClientShare, agentId)
	if err != nil { //argot:ignore
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
	ok, err := iosanitization.KMSVerify(dc.kmsService, resp.ClientLTKeyARN, clientSignPayloadBytes, sig /*@, perm(1/2), t2, rid, AgentId, KMSId, ClientId, clientLtKeyIdT, messageT, sigYT, verifyReqT @*/)
	if !ok {
		state = Erroneous
		//@ fold dc.MemTransfer(state, true)
		err = errHandshake()
		return
	}
	if err != nil { //argot:ignore
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
		err = fmtError("failed to decode server share")
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

// @ trusted
// @ ensures err == nil ==> bytes.SliceMem(clientSignPayload)
// @ ensures err == nil ==> abs.Abs(clientSignPayload) == by.pairB(by.msgB(clientShare), by.msgB(agentId))
// @ ensures err != nil ==> err.ErrorMem()
func getVerifyPayloadBytes(clientShare string, agentId string) (clientSignPayload []byte, err error) {
	payload := &mgsContracts.SignClientSharePayload{
		ClientShare: clientShare,
		AgentId:     agentId,
	}

	//@ fold payload.Mem()
	return json.Marshal(payload /*@, perm(1/2) @*/)
}

// @ requires dc.MemTransfer(HandshakeResponseVerified, true)
// @ ensures  dc.MemTransfer(state, true)
// @ ensures  err == nil ==> state == BlockCipherReady
// @ ensures  err != nil ==> err.ErrorMem() && state == Erroneous
func (dc *dataChannel) completeSecureSessionResponseProcessing() (state DataChannelState, err error) {
	state = HandshakeResponseVerified
	//@ unfold dc.MemTransfer(state, true)
	//@ rid, AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, xT, SigX := dc.getRid(), dc.getAgentIdT(), dc.getKMSIdT(), dc.getClientIdT(), dc.getReaderIdT(), tm.pubTerm(pub.pub_msg(dc.secrets.agentLTKeyARN)), dc.getLogLTPkT(), dc.getAgentShareT(), dc.getAgentShareSignatureT()
	//@ t0 := dc.getToken()
	//@ s0 := dc.getAbsState()
	sharedSecret := dc.secrets.sharedSecret
	//@ sharedSecretT := dc.getSharedSecretT()
	//@ clientLtKeyIdT := dc.getClientLtKeyIdT()
	//@ clientSecretT := dc.getClientShareT()
	//@ sigYT := dc.getClientShareSignatureT()

	// use the shared secret to generate read and write keys
	agentWriteKey, err := computeKdf(sharedSecret, true /*@, perm(1/8) @*/)
	if err != nil { //argot:ignore
		state = Erroneous
		//@ fold dc.MemTransfer(state, true)
		return state, errHandshake()
	}
	dc.secrets.agentWriteKey = agentWriteKey

	agentReadKey, err := computeKdf(sharedSecret, false /*@, perm(1/8) @*/)
	if err != nil { //argot:ignore
		state = Erroneous
		//@ fold dc.MemTransfer(state, true)
		return state, errHandshake()
	}
	dc.secrets.agentReadKey = agentReadKey

	sessionKeysBytes, err := getSessionKeysPayload(agentWriteKey, agentReadKey /*@, perm(1/8) @*/)
	if err != nil { //argot:ignore
		state = Erroneous
		//@ fold dc.MemTransfer(state, true)
		return state, errHandshake()
	}
	//@ sessionKeysBytesT := tm.pair(tm.kdf1(sharedSecretT), tm.kdf2(sharedSecretT))
	//@ assert abs.Abs(sessionKeysBytes) == by.gamma(sessionKeysBytesT)

	encodedEncryptedSessionKeys, err := encryptAndEncode(sessionKeysBytes, dc.logLTPk /*@, perm(1/2) @*/)
	if err != nil { //argot:ignore
		state = Erroneous
		//@ fold dc.MemTransfer(state, true)
		return state, errHandshake()
	}
	//@ encodedEncryptedSessionKeysT := tm.aenc(sessionKeysBytesT, dc.getLogLTPkT())
	//@ assert by.msgB(encodedEncryptedSessionKeys) == by.gamma(encodedEncryptedSessionKeysT)

	// sign ciphertext containing session keys using KMS:
	signSessionKeysPayloadBytes, err := getSignSessionKeysPayloadBytes(encodedEncryptedSessionKeys, dc.clientId)
	if err != nil { //argot:ignore
		state = Erroneous
		//@ fold dc.MemTransfer(state, true)
		return state, errHandshake()
	}
	//@ messageT := tm.pair(encodedEncryptedSessionKeysT, dc.getClientIdT())
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
	if err != nil { //argot:ignore
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
	if err != nil { //argot:ignore
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

	if err := dc.blockCipher.UpdateEncryptionKeys(dc.secrets.agentReadKey, dc.secrets.agentWriteKey /*@, perm(1/2), tm.kdf2(sharedSecretT), tm.kdf1(sharedSecretT) @*/); err != nil { //argot:ignore
		state = Erroneous
		//@ fold dc.MemTransfer(state, true)
		return state, errHandshake()
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
// @ requires noPerm < p
// @ preserves acc(bytes.SliceMem(payload), p) && acc(pk.Mem(), p)
// @ ensures  err == nil ==> by.msgB(encodedCiphertext) == by.aencB(abs.Abs(payload), pk.Abs())
// @ ensures  err != nil ==> err.ErrorMem()
func encryptAndEncode(payload []byte, pk *rsa.PublicKey /*@, ghost p perm @*/) (encodedCiphertext string, err error) {
	//@ cryptoRand.GetReaderMem()
	ciphertext, err := rsa.EncryptPKCS1v15(cryptoRand.Reader, pk, payload /*@, p > writePerm ? perm(1/1) : p/2 @*/)
	if err != nil { //argot:ignore
		err = fmtErrorf("failed to encrypt session keys", err /*@, perm(1/1) @*/)
		return
	}
	encodedCiphertext = base64.StdEncoding.EncodeToString(ciphertext /*@, perm(1/2) @*/)
	return
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
	sig, err /*@, signatureT @*/ = iosanitization.KMSSign(kmsService, keyId, message /*@, p, t, rid, agentId, kmsId, messageT, m @*/)
	if err != nil { //argot:ignore
		return
	}
	signature = base64.StdEncoding.EncodeToString(sig /*@, perm(1/2)@*/)
	return
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
	if err != nil { //argot:ignore
		return
	}

	encryptedSessionKeysPayload = base64.StdEncoding.EncodeToString(encryptedSessionKeysPayloadBytes /*@, perm(1/2) @*/)
	return
}
