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
	//@ "bytes"

	logger "github.com/aws/amazon-ssm-agent/agent/log"
	mgsContracts "github.com/aws/amazon-ssm-agent/agent/session/contracts"
	"github.com/aws/amazon-ssm-agent/agent/session/datachannel/iosanitization"
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
// @ preserves dc != nil ==> dc.Mem()
// @ preserves log != nil ==> acc(log.Mem(), _)
// @ preserves inputData != nil ==> bytes.SliceMem(inputData)
// @ ensures   err != nil ==> err.ErrorMem()
func (dc *dataChannel) SendStreamDataMessage(log logger.T, payloadType mgsContracts.PayloadType, inputData []byte) (err error) {
	if dc == nil || log == nil || inputData == nil {
		return fmtErrorNil()
	}
	if dc.getState() != IODistributed {
		return fmtErrorInvalidState(dc.getState())
	}

	if payloadType != mgsContracts.Output && payloadType != mgsContracts.StdErr && payloadType != mgsContracts.ExitCode {
		return fmtErrorfPayloadType("Rejecting stream data message as it would otherwise be sent in plaintext, payload type", payloadType)
	}

	//@ unfold dc.Mem()
	//@ unfold acc(dc.MemInternal(IODistributed), 1/2)
	//@ rid, AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, xT, SigX := dc.io.getRid(), dc.io.getAgentIdT(), dc.io.getKMSIdT(), dc.io.getClientIdT(), dc.io.getReaderIdT(), tm.pubTerm(pub.pub_msg(dc.secrets.agentLTKeyARN)), dc.io.getLogLTPkT(), dc.io.getAgentShareT(), dc.io.getAgentShareSignatureT()

	// ----- start local receive I/O operation -----
	//@ dc.ioLock.Lock()
	//@ unfold IoLockInv!<dc, dc.instanceId, dc.clientId, dc.secrets.agentLTKeyARN!>()

	//@ t0 := dc.io.getToken()
	//@ s0 := dc.io.getAbsState()

	// receive `inputData` from environment:
	//@ unfold iospec.P_Agent(t0, rid, s0)
	//@ unfold iospec.phiRF_Agent_16(t0, rid, s0)
	//@ s1 := s0 union mset[ft.Fact]{ ft.InFact_Agent(rid, iospec.get_e_InFact_r1(t0, rid)) }
	/*@ t1, inputDataT := @*/
	iosanitization.PerformVirtualInputOperation(inputData /*@, t0, rid @*/)

	//@ unfold dc.io.IoSpecMemMain()
	//@ dc.io.token = t1
	//@ dc.io.absState = s1
	//@ dc.io.localInFactT = inputDataT
	//@ dc.ioLockDidLocalReceive = true
	//@ fold dc.io.IoSpecMemMain()

	//@ fold IoLockInv!<dc, dc.instanceId, dc.clientId, dc.secrets.agentLTKeyARN!>()
	//@ dc.ioLock.Unlock()
	// ----- end local receive I/O operation -----

	// ----- start internal I/O operation -----
	//@ dc.ioLock.Lock()
	//@ unfold IoLockInv!<dc, dc.instanceId, dc.clientId, dc.secrets.agentLTKeyARN!>()
	//@ t1 = dc.io.getToken()
	//@ s1 = dc.io.getAbsState()
	//@ sharedSecretT := dc.io.getSharedSecretT()
	//@ clientLtKeyIdT := dc.io.getClientLtKeyIdT()
	//@ clientSecretT := dc.io.getClientShareT()
	//@ sigYT := dc.io.getClientShareSignatureT()
	//@ sigSessionKeysT := dc.io.getSigSessionKeysT()

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

	//@ unfold dc.io.IoSpecMemMain()
	//@ dc.io.token = t2
	//@ dc.io.absState = s2
	//@ dc.ioLockDidLocalReceive = false
	//@ dc.io.remoteOutFactT = tm.pair(tm.pubTerm(pub.const_Message_pub()), tm.senc(inputDataT, tm.kdf1(sharedSecretT)))
	//@ dc.ioLockCanRemoteSend = true
	//@ fold dc.io.IoSpecMemMain()

	//@ fold IoLockInv!<dc, dc.instanceId, dc.clientId, dc.secrets.agentLTKeyARN!>()
	//@ dc.ioLock.Unlock()
	// ----- end internal I/O operation -----

	if !dc.encryptionEnabled {
		// since `dataStream.Send` (called within `sendData`) will store `inputData` in a queue to send out possibly later, we duplicate the byte slice
		// such that callers can reuse the input parameter.
		// This is necessary since there are clients reusing the same byte slice, which would otherwise result in a data race.
		// However, this is dead code when we assume that clients enable encryption.
		inputData = duplicate(inputData /*@, perm(1/2) @*/)
	}

	//@ fold acc(dc.MemInternal(IODistributed), 1/2)
	//@ fold dc.Mem()

	return dc.sendData(log, payloadType, inputData /*@, inputDataT, true, true @*/)
}

// @ requires log != nil
// @ requires dc.Mem()
// @ requires requiresEncryption == (payloadType == mgsContracts.Output || payloadType == mgsContracts.StdErr || payloadType == mgsContracts.ExitCode || payloadType == mgsContracts.HandshakeComplete)
// @ requires dc.getState() >= (requiresEncryption ? BlockCipherReady : BlockCipherInitialized)
// @ requires requiresLock ==>
// @ 	dc.getState() == IODistributed && requiresEncryption &&
// @	dc.GetIoLockCanRemoteSend() && dc.GetRemoteOutFactT() == tm.pair(mgsContracts.payloadTypeTerm(payloadType), tm.senc(inputDataT, dc.GetEncKeyT()))
// @ requires !requiresLock ==>
// @	dc.getState() < IODistributed &&
// @	(requiresEncryption ?
// @ 		ft.OutFact_Agent(dc.GetRid(), tm.pair(mgsContracts.payloadTypeTerm(payloadType), tm.senc(inputDataT, dc.GetEncKeyT()))) # dc.GetAbsState() > 0 :
// @ 		ft.OutFact_Agent(dc.GetRid(), tm.pair(mgsContracts.payloadTypeTerm(payloadType), inputDataT)) # dc.GetAbsState() > 0)
// @ requires bytes.SliceMem(inputData) && by.gamma(inputDataT) == abs.Abs(inputData)
// @ preserves acc(log.Mem(), _)
// @ ensures dc.Mem() && dc.getState() == old(dc.getState())
// @ ensures old(unfolding dc.Mem() in unfolding acc(dc.MemInternal(dc.dataChannelState), 1/2) in dc.encryptionEnabled) && requiresEncryption ==> bytes.SliceMem(inputData)
// @ ensures err != nil ==> err.ErrorMem()
func (dc *dataChannel) sendData(log logger.T, payloadType mgsContracts.PayloadType, inputData []byte /*@, ghost inputDataT tm.Term, ghost requiresEncryption bool, ghost requiresLock bool @*/) (err error) {
	// @ ghost state := dc.getState()
	// @ unfold dc.Mem()
	// @ unfold acc(dc.MemInternal(state), 1/2)

	// If encryption has been enabled, encrypt the payload
	if dc.encryptionEnabled && (payloadType == mgsContracts.Output || payloadType == mgsContracts.StdErr || payloadType == mgsContracts.ExitCode || payloadType == mgsContracts.HandshakeComplete) {
		if inputData, err = dc.blockCipher.EncryptWithAESGCM(inputData /*@, perm(1/4) @*/); err != nil {
			err = fmtErrorfInt64Err("error encrypting stream data message sequence", dc.dataStream.GetStreamDataSequenceNumber( /*@ perm(1/2) @*/ ), err /*@, perm(1/1) @*/)
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
		unfold IoLockInv!<dc, dc.instanceId, dc.clientId, dc.secrets.agentLTKeyARN!>()
	} else {
		unfold acc(dc.MemInternal(state), 1/2)
	}

	rid, AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, xT, SigX := dc.io.getRid(), dc.io.getAgentIdT(), dc.io.getKMSIdT(), dc.io.getClientIdT(), dc.io.getReaderIdT(), tm.pubTerm(pub.pub_msg(dc.secrets.agentLTKeyARN)), dc.io.getLogLTPkT(), dc.io.getAgentShareT(), dc.io.getAgentShareSignatureT()
	t0 := dc.io.getToken()
	s0 := dc.io.getAbsState()
	sharedSecretT := dc.io.getSharedSecretT()
	clientLtKeyIdT := dc.io.getClientLtKeyIdT()
	clientSecretT := dc.io.getClientShareT()
	sigYT := dc.io.getClientShareSignatureT()
	sigSessionKeysT := dc.io.getSigSessionKeysT()
	m := tm.pair(mgsContracts.payloadTypeTerm(payloadType), inputDataT)
	unfold iospec.P_Agent(t0, rid, s0)
	unfold iospec.phiRG_Agent_13(t0, rid, s0)
	@*/

	//@ ghost var t1 pl.Place
	err /*@, t1 @*/ = iosanitization.DataStreamSend(dc.dataStream, log, payloadType, inputData /*@, perm(1/2), t0, rid, inputDataT, m @*/)
	if err != nil {
		/*@
		fold iospec.phiRG_Agent_13(t0, rid, s0)
		fold iospec.P_Agent(t0, rid, s0)
		ghost if requiresLock {
			fold IoLockInv!<dc, dc.instanceId, dc.clientId, dc.secrets.agentLTKeyARN!>()
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
	unfold dc.io.IoSpecMemMain()
	dc.io.token = t1
	s1 := s0 setminus mset[ft.Fact]{ ft.OutFact_Agent(rid, m) }
	dc.io.absState = s1
	fold dc.io.IoSpecMemMain()
	ghost if requiresLock {
		dc.ioLockCanRemoteSend = false
		fold IoLockInv!<dc, dc.instanceId, dc.clientId, dc.secrets.agentLTKeyARN!>()
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
