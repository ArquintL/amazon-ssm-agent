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
	logger "github.com/aws/amazon-ssm-agent/agent/log"
	mgsContracts "github.com/aws/amazon-ssm-agent/agent/session/contracts"
	//@ by "github.com/aws/amazon-ssm-agent/agent/iospecs/bytes"
	//@ cl "github.com/aws/amazon-ssm-agent/agent/iospecs/claim"
	//@ ft "github.com/aws/amazon-ssm-agent/agent/iospecs/fact"
	//@ "github.com/aws/amazon-ssm-agent/agent/iospecs/iospec"
	//@ pub "github.com/aws/amazon-ssm-agent/agent/iospecs/pub"
	//@ tm "github.com/aws/amazon-ssm-agent/agent/iospecs/term"
	//@ ut "github.com/aws/amazon-ssm-agent/agent/iospecs/util"
)

// buildHandshakeCompletePayload builds payload for HandshakeComplete
// @ requires log != nil && dc.Mem() && dc.getState() >= Initialized
// @ requires unfolding acc(dc.Mem(), _) in unfolding acc(dc.MemInternal(dc.dataChannelState), _) in dc.encryptionEnabled ==> dc.dataChannelState == BlockCipherReady
// @ preserves acc(log.Mem(), _)
// @ ensures dc.Mem() && dc.getState() == old(dc.getState())
// @ ensures err == nil ==> payload.Mem() && payload.Abs() == by.gamma(tm.pair(tm.pubTerm(pub.const_HandshakeCompletePayload_pub()), dc.GetInFactT()))
// @ ensures err == nil ==> ft.InFact_Agent(dc.GetRid(), dc.GetInFactT()) in dc.GetAbsState()
// @ ensures err != nil ==> err.ErrorMem()
func (dc *dataChannel) buildHandshakeCompletePayload(log logger.T) (payload *mgsContracts.HandshakeCompletePayload, err error) {
	clientVersion, err := dc.GetClientVersion()
	if err != nil {
		return
	}

	//@ unfold dc.Mem()
	//@ state := dc.dataChannelState
	//@ unfold dc.MemInternal(state)
	//@ t0 := dc.io.getToken()
	//@ rid := dc.io.getRid()
	//@ s0 := dc.io.getAbsState()
	//@ unfold iospec.P_Agent(t0, rid, s0)
	//@ unfold iospec.phiRF_Agent_16(t0, rid, s0)
	//@ t1 := iospec.get_e_InFact_placeDst(t0, rid)

	duration := dc.hs.handshakeEndTime.Sub(dc.hs.handshakeStartTime)
	customerMessage, err /*@, payloadT @*/ := getHandshakeCompletePayload(duration, dc.separateOutputPayload, dc.encryptionEnabled, clientVersion /*@, t0, rid @*/)
	if err != nil {
		//@ fold iospec.phiRF_Agent_16(t0, rid, s0)
		//@ fold iospec.P_Agent(t0, rid, s0)
		//@ fold dc.MemInternal(state)
		//@ fold dc.Mem()
		return
	}
	//@ s1 := s0 union mset[ft.Fact]{ ft.InFact_Agent(rid, payloadT) }
	//@ unfold dc.io.IoSpecMemMain()
	//@ unfold dc.io.IoSpecMemPartial()
	//@ dc.io.token = t1
	//@ dc.io.absState = s1
	//@ dc.io.inFactT = payloadT
	//@ fold dc.io.IoSpecMemPartial()
	//@ fold dc.io.IoSpecMemMain()
	//@ fold dc.MemInternal(state)
	//@ fold dc.Mem()

	payload = &mgsContracts.HandshakeCompletePayload{
		HandshakeTimeToComplete: duration,
		CustomerMessage:         customerMessage,
	}
	//@ fold payload.Mem()
	return
}

// sendHandshakeComplete sends handshake complete
// @ requires log != nil && handshakeCompletePayload.Mem()
// @ requires dc.Mem() && dc.getState() == BlockCipherReady
// @ requires handshakeCompletePayload.Abs() == by.gamma(tm.pair(tm.pubTerm(pub.const_HandshakeCompletePayload_pub()), dc.GetInFactT()))
// @ requires ft.InFact_Agent(dc.GetRid(), dc.GetInFactT()) in dc.GetAbsState()
// @ preserves acc(log.Mem(), _)
// @ ensures dc.Mem()
// @ ensures err == nil ==> dc.getState() == HandshakeCompleted && dc.isHandshakeCompleted()
// @ ensures err != nil ==> err.ErrorMem()
func (dc *dataChannel) sendHandshakeComplete(log logger.T, handshakeCompletePayload *mgsContracts.HandshakeCompletePayload) (err error) {
	handshakeCompletePayloadBytes, err := marshalHandshakeComplete(handshakeCompletePayload /*@, perm(1/2) @*/)
	if err != nil {
		return fmtErrorSerializeHandshakeComplete(handshakeCompletePayload, err /*@, perm(1/1) @*/)
	}

	logDebug(log, "Sending HandshakeComplete.")
	logHandshakeComplete(log, handshakeCompletePayload /*@, perm(1/2) @*/)
	//@ payloadT := dc.GetInFactT()
	//@ inputDataT := tm.pair(tm.pubTerm(pub.const_HandshakeCompletePayload_pub()), payloadT)

	//@ unfold dc.Mem()
	//@ unfold dc.MemInternal(BlockCipherReady)
	//@ rid, AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, xT, SigX := dc.io.getRid(), dc.io.getAgentIdT(), dc.io.getKMSIdT(), dc.io.getClientIdT(), dc.io.getReaderIdT(), tm.pubTerm(pub.pub_msg(dc.secrets.agentLTKeyARN)), dc.io.getLogLTPkT(), dc.io.getAgentShareT(), dc.io.getAgentShareSignatureT()
	//@ t0 := dc.io.getToken()
	//@ s0 := dc.io.getAbsState()
	//@ sharedSecretT := dc.io.getSharedSecretT()
	//@ clientLtKeyIdT := dc.io.getClientLtKeyIdT()
	//@ clientSecretT := dc.io.getClientShareT()
	//@ sigYT := dc.io.getClientShareSignatureT()
	//@ sigSessionKeysT := dc.io.getSigSessionKeysT()
	/*@
		l := mset[ft.Fact] {
			ft.St_Agent_9(rid, AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, xT, SigX, clientLtKeyIdT, tm.exp(tm.pubTerm(pub.const_g_pub()), clientSecretT), sigYT, sigSessionKeysT),
			ft.InFact_Agent(rid, payloadT),
		}
		a := mset[cl.Claim] {
			cl.Agent_Finish(AgentId),
			cl.Secret(tm.pair(tm.kdf1(sharedSecretT), tm.kdf2(sharedSecretT))),
			cl.Commit(tm.pubTerm(pub.const_Agent_pub()), tm.pubTerm(pub.const_Client_pub()), ut.tuple4(AgentId, ClientId, tm.kdf1(sharedSecretT), tm.kdf2(sharedSecretT))),
			cl.Running(tm.pubTerm(pub.const_Agent_pub()), tm.pubTerm(pub.const_Client_pub()), ut.tuple4(AgentId, ClientId, tm.kdf1(sharedSecretT), tm.kdf2(sharedSecretT))),
			cl.HonestReader(ReaderId),
			cl.HonestKmsOwner(AgentId),
			cl.HonestKmsOwner(ClientId),
			cl.AgentHandshakeCompleted(rid, AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, xT, clientLtKeyIdT, tm.exp(tm.pubTerm(pub.const_g_pub()), clientSecretT)),
		}
		r := mset[ft.Fact] {
		    ft.St_Agent_10(rid, AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, xT, SigX, clientLtKeyIdT, tm.exp(tm.pubTerm(pub.const_g_pub()), clientSecretT), sigYT, sigSessionKeysT),
			ft.OutFact_Agent(rid, tm.pair(tm.pubTerm(pub.const_HandshakeComplete_pub()), tm.senc(tm.pair(tm.pubTerm(pub.const_HandshakeCompletePayload_pub()), payloadT), tm.kdf1(sharedSecretT)))),
			ft.OutFact_Agent(rid, ut.tuple3(tm.pubTerm(pub.const_Log_pub()), tm.pubTerm(pub.const_HandshakeComplete_pub()), tm.senc(tm.pair(tm.pubTerm(pub.const_HandshakeCompletePayload_pub()), payloadT), tm.kdf1(sharedSecretT)))),
		}
	@*/
	//@ unfold iospec.P_Agent(t0, rid, s0)
	//@ unfold iospec.phiR_Agent_9(t0, rid, s0)
	//@ t1 := iospec.internBIO_e_Agent_SendHandshakeComplete(t0, rid, AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, xT, SigX, clientLtKeyIdT, tm.exp(tm.pubTerm(pub.const_g_pub()), clientSecretT), sigYT, sigSessionKeysT, payloadT, l, a, r)
	//@ s1 := ft.U(l, r, s0)
	//@ unfold dc.io.IoSpecMemMain()
	//@ dc.io.token = t1
	//@ dc.io.absState = s1
	//@ fold dc.io.IoSpecMemMain()
	//@ unfold acc(dc.MemChannelState(), 1/2)
	dc.dataChannelState = HandshakeCompleted
	//@ fold acc(dc.MemChannelState(), 1/2)
	//@ fold dc.MemInternal(HandshakeCompleted)
	//@ fold dc.Mem()

	if err = dc.sendData(log, mgsContracts.HandshakeComplete, handshakeCompletePayloadBytes /*@, inputDataT, true, false @*/); err != nil {
		return err
	}

	//@ unfold dc.Mem()
	//@ unfold dc.MemInternal(HandshakeCompleted)
	dc.hs.complete = true
	//@ fold dc.MemInternal(HandshakeCompleted)
	//@ fold dc.Mem()

	return nil
}
