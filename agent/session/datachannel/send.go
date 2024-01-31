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
	"encoding/json"
	//@ "bytes"

	logger "github.com/aws/amazon-ssm-agent/agent/log"
	mgsContracts "github.com/aws/amazon-ssm-agent/agent/session/contracts"
	//@ abs "github.com/aws/amazon-ssm-agent/agent/iospecs/abs"
	//@ by "github.com/aws/amazon-ssm-agent/agent/iospecs/bytes"
	//@ cl "github.com/aws/amazon-ssm-agent/agent/iospecs/claim"
	//@ ft "github.com/aws/amazon-ssm-agent/agent/iospecs/fact"
	//@ "github.com/aws/amazon-ssm-agent/agent/iospecs/iospec"
	//@ pl "github.com/aws/amazon-ssm-agent/agent/iospecs/place"
	//@ pub "github.com/aws/amazon-ssm-agent/agent/iospecs/pub"
	//@ tm "github.com/aws/amazon-ssm-agent/agent/iospecs/term"
)


// SendStreamDataMessage sends a data message in a form of AgentMessage for streaming.
// Requires that the handshake is either complete or skipped
// @ requires log != nil
// @ requires QuantifiedSendStreamDataMessageWand(inputData, inputDataT, p)
// @ preserves dc.Mem()
// @ preserves acc(log.Mem(), _)
// @ ensures err != nil ==> err.ErrorMem()
func (dc *dataChannel) SendStreamDataMessage(log logger.T, payloadType mgsContracts.PayloadType, inputData []byte /*@, ghost p perm, ghost inputDataT tm.Term @*/) (err error) {
	if dc.getState() != IODistributed {
		return fmtErrorInvalidState(dc.getState())
	}

	if payloadType != mgsContracts.Output && payloadType != mgsContracts.StdErr && payloadType != mgsContracts.ExitCode {
		return fmtErrorfPayloadType("Rejecting stream data message as it would otherwise be sent in plaintext, payload type", payloadType)
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
			err = fmtErrorfInt64Err("error encrypting stream data message sequence", dc.dataStream.GetStreamDataSequenceNumber( /*@ p/4 @*/ ), err /*@, perm(1/1) @*/)
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
		logErrorf(log, "Cannot serialize AgentSessionState message err", err /*@, perm(1/1) @*/)
		return err
	}

	sessionStatusStr := string(sessionStatus)
	//@ fold sessionStatusStr.Mem()
	logDebug(log, "Send AgentSessionState message with session status" + sessionStatusStr)
	if err := dc.dataStream.SendAgentMessage(log, mgsContracts.AgentSessionState, agentSessionStateContentBytes); err != nil {
		return err
	}
	return nil
}
