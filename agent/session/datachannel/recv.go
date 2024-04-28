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
	mgsContracts "github.com/aws/amazon-ssm-agent/agent/session/contracts"
	"github.com/aws/amazon-ssm-agent/agent/session/datachannel/iosanitization"
	//@ "github.com/aws/amazon-ssm-agent/agent/session/datastream"
	//@ abs "github.com/aws/amazon-ssm-agent/agent/iospecs/abs"
	//@ by "github.com/aws/amazon-ssm-agent/agent/iospecs/bytes"
	//@ cl "github.com/aws/amazon-ssm-agent/agent/iospecs/claim"
	//@ ft "github.com/aws/amazon-ssm-agent/agent/iospecs/fact"
	//@ "github.com/aws/amazon-ssm-agent/agent/iospecs/iospec"
	//@ "github.com/aws/amazon-ssm-agent/agent/iospecs/pattern"
	//@ pl "github.com/aws/amazon-ssm-agent/agent/iospecs/place"
	//@ pub "github.com/aws/amazon-ssm-agent/agent/iospecs/pub"
	//@ tm "github.com/aws/amazon-ssm-agent/agent/iospecs/term"
)

// processStreamDataMessage gets called for all messages of type OutputStreamDataMessage
// @ requires datastream.StreamDataHandlerFootprint(streamDataMessage)
// @ preserves dc.RecvRoutineMem()
// @ ensures err != nil ==> err.ErrorMem()
func (dc *dataChannel) processStreamDataMessage(streamDataMessage *mgsContracts.AgentMessage) (err error) {

	payload, err := dc.tryReceiveMessageReceptionStatus(channelStatusTimeout)
	if err != nil {
		return err
	}

	//@ unfold StartReceivingChanInv!<dc, _!>(payload)
	switch payload.status {
	case ReceiveHandshakeResponeEncryptionEnabled:
		//@ unfold dc.MemTransfer(HandshakeRequestSent, true)
		//@ t0 := dc.getToken()
		//@ rid := dc.getRid()
		//@ s0 := dc.getAbsState()
		//@ unfold iospec.P_Agent(t0, rid, s0)
		//@ unfold iospec.phiRF_Agent_16(t0, rid, s0)
		//@ t1 := iospec.get_e_InFact_placeDst(t0, rid)
		//@ receivedMsgT := datastream.StreamDataHandlerViewShift(t0, rid, streamDataMessage)
		//@ s1 := s0 union mset[ft.Fact]{ ft.InFact_Agent(rid, receivedMsgT) }
		//@ unfold dc.IoSpecMemMain()
		//@ unfold dc.IoSpecMemPartial()
		//@ dc.setToken(t1)
		//@ dc.setAbsState(s1)
		//@ dc.setInFactT(receivedMsgT)
		//@ fold dc.IoSpecMemPartial()
		//@ fold dc.IoSpecMemMain()
		//@ assert by.gamma(receivedMsgT) == streamDataMessage.Abs()
		//@ fold dc.MemTransfer(HandshakeRequestSent, true)
		payloadType := /*@ unfolding streamDataMessage.Mem() in @*/ streamDataMessage.PayloadType
		switch mgsContracts.PayloadType(payloadType) {
		case mgsContracts.HandshakeResponse:
			{
				// PayloadType is HandshakeResponse so we call our own handler instead of the plugin handler
				if err = dc.handleHandshakeResponse(streamDataMessage, true); err != nil {
					return fmtErrorf("processing of HandshakeResponse message failed", err /*@, perm(1/1) @*/)
				}
			}
		default:
			return fmtError("received message with unexpected payload type")
		}
		//@ assert streamDataMessage.Mem()
	case ReceiveHandshakeResponeEncryptionDisabled:
		// since we assume that encryption is enabled for proving refinement, we can derive here
		// a contradiction, i.e., this case corresponds to dead code if encryption is enabled:
		//@ assert false
		payloadType := /*@ unfolding streamDataMessage.Mem() in @*/ streamDataMessage.PayloadType
		switch mgsContracts.PayloadType(payloadType) {
		case mgsContracts.HandshakeResponse:
			{
				// PayloadType is HandshakeResponse so we call our own handler instead of the plugin handler
				if err = dc.handleHandshakeResponse(streamDataMessage, false); err != nil {
					return fmtErrorf("processing of HandshakeResponse message failed", err /*@, perm(1/1) @*/)
				}
			}
		default:
			return fmtError("received message with unexpected payload type")
		}
	case ReceiveOtherResponse:
		//@ unfold dc.MemRecv()

		// ----- start remote receive I/O operation -----
		//@ dc.ioLock.Lock()
		//@ unfold IoLockInv!<dc, dc.instanceId, dc.clientId, dc.secrets.agentLTKeyARN!>()

		//@ t0 := dc.getToken()
		//@ rid := dc.getRid()
		//@ s0 := dc.getAbsState()
		//@ unfold iospec.P_Agent(t0, rid, s0)
		//@ unfold iospec.phiRF_Agent_16(t0, rid, s0)
		//@ t1 := iospec.get_e_InFact_placeDst(t0, rid)
		//@ receivedMsgT := datastream.StreamDataHandlerViewShift(t0, rid, streamDataMessage)
		//@ s1 := s0 union mset[ft.Fact]{ ft.InFact_Agent(rid, receivedMsgT) }

		//@ unfold dc.IoSpecMemMain()
		//@ dc.setToken(t1)
		//@ dc.setAbsState(s1)
		//@ dc.setRemoteInFactT(receivedMsgT)
		//@ dc.ioLockDidRemoteReceive = true
		//@ fold dc.IoSpecMemMain()

		//@ fold IoLockInv!<dc, dc.instanceId, dc.clientId, dc.secrets.agentLTKeyARN!>()
		//@ dc.ioLock.Unlock()
		// ----- end remote receive I/O operation -----

		//@ unfold streamDataMessage.Mem()
		if dc.encryptionEnabled && mgsContracts.PayloadType(streamDataMessage.PayloadType) == mgsContracts.Output {
			plaintext, err := dc.blockCipher.DecryptWithAESGCM(streamDataMessage.Payload /*@, perm(1/4) @*/)
			if err != nil {
				// send a message to the channel to prepare for next message reception:
				//@ fold dc.MemRecv()
				dc.resendReceiveOtherResponse()
				err = fmtErrorfInt64Err("Error decrypting stream data message sequence", streamDataMessage.SequenceNumber, err /*@, perm(1/1) @*/)
				//@ fold streamDataMessage.Mem()
				return err
			}
			streamDataMessage.Payload = plaintext
		} else if dc.encryptionEnabled {
			// send a message to the channel to prepare for next message reception:
			//@ fold dc.MemRecv()
			dc.resendReceiveOtherResponse()
			err = fmtErrorfInt64("Unknown payload type of stream data message sequence", streamDataMessage.SequenceNumber)
			//@ fold streamDataMessage.Mem()
			return err
		}
		//@ plaintextB := abs.Abs(streamDataMessage.Payload)
		//@ fold streamDataMessage.Mem()

		// Ignore stream data message if handshake is neither skipped nor completed
		if !dc.hs.skipped && !dc.hs.complete {
			// this case should provably not occur as status `ReceiveOtherResponse`
			// is supposed to be sent on the `startReceivingChan` channel AFTER the
			// handshake has completed.
			// While this branch existed in the original implementation, we can actually
			// prove that this branch cannot exist:
			//@ assert false
		}

		// ----- start internal I/O operation -----
		//@ dc.ioLock.Lock()
		//@ unfold IoLockInv!<dc, dc.instanceId, dc.clientId, dc.secrets.agentLTKeyARN!>()
		//@ t1 = dc.getToken()
		//@ s1 = dc.getAbsState()
		//@ rid, AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, xT, SigX := dc.getRid(), dc.getAgentIdT(), dc.getKMSIdT(), dc.getClientIdT(), dc.getReaderIdT(), tm.pubTerm(pub.pub_msg(dc.secrets.agentLTKeyARN)), dc.getLogLTPkT(), dc.getAgentShareT(), dc.getAgentShareSignatureT()
		//@ sharedSecretT := dc.getSharedSecretT()
		//@ clientLtKeyIdT := dc.getClientLtKeyIdT()
		//@ clientSecretT := dc.getClientShareT()
		//@ sigYT := dc.getClientShareSignatureT()
		//@ sigSessionKeysT := dc.getSigSessionKeysT()
		// temporarily unfolding the block cipher's memory to learn the relation between the decryption term and its byte representation:
		//@ assert unfolding acc(dc.blockCipher.Mem(), _) in dc.blockCipher.GetDecKeyB() == by.gamma(dc.blockCipher.GetDecKeyT())
		//@ payloadT := pattern.patternRequirementTransportMessage(rid, AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, xT, SigX, clientLtKeyIdT, tm.exp(tm.pubTerm(pub.const_g_pub()), clientSecretT), sigYT, sigSessionKeysT, by.oneTerm(plaintextB), receivedMsgT, t1, s1)
		//@ outMsgT := tm.pair(tm.pubTerm(pub.const_Message_pub()), payloadT)
		// obtain permission to send the ciphertext containing `inputData`:
		/*@
			l := mset[ft.Fact] {
				ft.St_Agent_10(rid, AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, xT, SigX, clientLtKeyIdT, tm.exp(tm.pubTerm(pub.const_g_pub()), clientSecretT), sigYT, sigSessionKeysT),
				ft.InFact_Agent(rid, tm.pair(tm.pubTerm(pub.const_Message_pub()), tm.senc(payloadT, tm.kdf2(sharedSecretT)))),
			}
			a := mset[cl.Claim] {
				cl.AgentRecvLoop(rid, AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, xT, clientLtKeyIdT, tm.exp(tm.pubTerm(pub.const_g_pub()), clientSecretT)),
			}
			r := mset[ft.Fact] {
		    	ft.St_Agent_10(rid, AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, xT, SigX, clientLtKeyIdT, tm.exp(tm.pubTerm(pub.const_g_pub()), clientSecretT), sigYT, sigSessionKeysT),
				ft.OutFact_Agent(rid, tm.pair(tm.pubTerm(pub.const_Message_pub()), payloadT)),
			}
			@*/
		//@ unfold iospec.P_Agent(t1, rid, s1)
		//@ unfold iospec.phiR_Agent_10(t1, rid, s1)
		//@ t2 := iospec.internBIO_e_Agent_ReceiveMessages(t1, rid, AgentId, KMSId, ClientId, ReaderId, AgentLtKeyId, logPk, xT, SigX, clientLtKeyIdT, tm.exp(tm.pubTerm(pub.const_g_pub()), clientSecretT), sigYT, sigSessionKeysT, payloadT, l, a, r)
		//@ s2 := ft.U(l, r, s1)

		//@ unfold dc.IoSpecMemMain()
		//@ dc.setToken(t2)
		//@ dc.setAbsState(s2)
		//@ dc.ioLockDidRemoteReceive = false
		//@ dc.setLocalOutFactT(outMsgT)
		//@ dc.ioLockCanLocalSend = true
		//@ fold dc.IoSpecMemMain()

		//@ fold IoLockInv!<dc, dc.instanceId, dc.clientId, dc.secrets.agentLTKeyARN!>()
		//@ dc.ioLock.Unlock()
		// ----- end internal I/O operation -----

		// ----- start internal send I/O operation -----
		//@ dc.ioLock.Lock()
		//@ unfold IoLockInv!<dc, dc.instanceId, dc.clientId, dc.secrets.agentLTKeyARN!>()

		//@ t2 = dc.getToken()
		//@ s2 = dc.getAbsState()
		//@ unfold iospec.P_Agent(t2, rid, s2)
		//@ unfold iospec.phiRG_Agent_13(t2, rid, s2)
		//@ t3 := iospec.get_e_OutFact_placeDst(t2, rid, outMsgT)
		//@ s3 := s2 setminus mset[ft.Fact]{ ft.OutFact_Agent(rid, outMsgT) }

		//@ fold dc.MemRecv()
		//@ unfold dc.RecvRoutineMem()
		err = iosanitization.DataChannelForwardToMessageHandler(dc.inputStreamMessageHandler, streamDataMessage /*@, t2, rid, outMsgT @*/)
		if err != nil {
			err = fmtError("inputStreamMessageHandler returned an error")
		}
		//@ fold dc.RecvRoutineMem()

		//@ unfold dc.MemRecv()
		//@ unfold dc.IoSpecMemMain()
		//@ dc.setToken(t3)
		//@ dc.setAbsState(s3)
		//@ dc.ioLockCanLocalSend = false
		//@ fold dc.IoSpecMemMain()

		//@ fold IoLockInv!<dc, dc.instanceId, dc.clientId, dc.secrets.agentLTKeyARN!>()
		//@ dc.ioLock.Unlock()
		// ----- end internal send I/O operation -----

		//@ fold dc.MemRecv()
		dc.resendReceiveOtherResponse()
		if err != nil {
			return err
		}
	}

	return nil
}

// requires acc(dc.Mem(), 1/2) && dc.getState() == AgentSecretCreatedAndSigned && unfolding acc(dc.Mem(), _) in unfolding acc(dc.MemInternal(AgentSecretCreatedAndSigned), _) in dc.hs.complete
// @ requires dc.MemRecv() && unfolding acc(dc.MemRecv(), _) in dc.dataChannelState == IODistributed && dc.hs.complete
// @ preserves dc.RecvRoutineMem()
func (dc *dataChannel) resendReceiveOtherResponse() {
	//@ unfold acc(dc.MemRecv(), 1/2)
	//@ unfold dc.RecvRoutineMem()
	//@ fold acc(dc.MemRecv(), 1/2)
	payload := MessageReceptionPayload{
		status: ReceiveOtherResponse,
	}
	//@ fold StartReceivingChanInv!<dc, _!>(payload)
	dc.hs.startReceivingChan <- payload
	//@ fold dc.RecvRoutineMem()
}
