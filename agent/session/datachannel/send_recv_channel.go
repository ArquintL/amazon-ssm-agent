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
	"time"

	//@ mgsContracts "github.com/aws/amazon-ssm-agent/agent/session/contracts"
	//@ abs "github.com/aws/amazon-ssm-agent/agent/iospecs/abs"
	//@ by "github.com/aws/amazon-ssm-agent/agent/iospecs/bytes"
	//@ "github.com/aws/amazon-ssm-agent/agent/iospecs/iospec"
	//@ pl "github.com/aws/amazon-ssm-agent/agent/iospecs/place"
	//@ tm "github.com/aws/amazon-ssm-agent/agent/iospecs/term"
)

// @ trusted
// @ preserves dc.RecvRoutineMem()
// @ ensures  err == nil ==> StartReceivingChanInv!<dc, _!>(res)
// @ ensures  err != nil ==> err.ErrorMem()
func (dc *dataChannel) tryReceiveMessageReceptionStatus(timeout time.Duration) (res MessageReceptionPayload, err error) {
	var ok bool
	select {
	case res, ok = <-dc.hs.startReceivingChan:
		if !ok {
			err = fmtError("Channel has been closed")
		}
	case <-time.After(timeout):
		err = fmtError("Timeout occurred waiting for receiving a message on a channel")
	}
	return
}

// @ trusted
// @ requires noPerm < p
// @ preserves acc(dc.Mem(), p) && dc.getState() == AgentSecretCreatedAndSigned
// @ ensures  err == nil ==> ResponseChanInv!<dc, _!>(payload)
// @ ensures  err != nil ==> err.ErrorMem()
func (dc *dataChannel) tryReceiveResponse(timeout time.Duration /*@, ghost p perm @*/) (payload ResponseChanPayload, err error) {
	var ok bool
	select {
	case payload, ok = <-dc.hs.responseChan:
		if !ok {
			err = fmtError("Channel has been closed")
		}
	case <-time.After(timeout):
		err = fmtError("Timeout occurred waiting for receiving a message on a channel")
	}
	return
}

// @ trusted
// @ requires acc(responseChan.RecvChannel(), _)
// @ requires responseChan.RecvGivenPerm() == PredTrue!<!>
// @ requires responseChan.RecvGotPerm() == ResponseChanInv!<dc, _!>
// @ ensures  responseChan.RecvChannel()
// @ ensures  responseChan.RecvGivenPerm() == PredTrue!<!>
// @ ensures  responseChan.RecvGotPerm() == ResponseChanInv!<dc, _!>
// @ ensures  err == nil ==> ResponseChanInv!<dc, _!>(payload)
// @ ensures  err != nil ==> err.ErrorMem()
func (dc *dataChannel) tryReceiveResponseAlt(responseChan chan ResponseChanPayload, timeout time.Duration) (payload ResponseChanPayload, err error) {
	var ok bool
	select {
	case payload, ok = <-responseChan:
		if !ok {
			err = fmtError("Channel has been closed")
		}
	case <-time.After(timeout):
		err = fmtError("Timeout occurred waiting for receiving a message on a channel")
	}
	return
}

/*@
// `nonDeterministicChoice` returns either true or false.
// Since we do not constrain the result value, the verifier
// considers both return values for any invocation of `nonDeterministicChoice()`
ghost
func nonDeterministicChoice() bool

// this models `tryReceiveMessageReceptionStatus` as Gobra does not yet support the `select` statement
// we use this function to validate the spec of `tryReceiveMessageReceptionStatus`
ghost
preserves dc.RecvRoutineMem()
ensures  err == nil ==> StartReceivingChanInv!<dc, _!>(res)
ensures  err != nil ==> err.ErrorMem()
func (dc *dataChannel) tryReceiveMessageReceptionStatusModel(timeout time.Duration) (res MessageReceptionPayload, err error) {
	if nonDeterministicChoice() {
		unfold dc.RecvRoutineMem()
		fold PredTrue!<!>()
		var ok bool
		res, ok = <-dc.hs.startReceivingChan
		fold dc.RecvRoutineMem()
		if !ok {
			err = fmtError("Channel has been closed")
			return
		}
	} else {
		err = fmtError("Timeout occurred waiting for receiving a message on a channel")
	}
	return
}

// this models `tryReceiveResponse` as Gobra does not yet support the `select` statement
// we use this function to validate the spec of `tryReceiveResponse`
ghost
requires noPerm < p
preserves acc(dc.Mem(), p) && dc.getState() == AgentSecretCreatedAndSigned
ensures  err == nil ==> ResponseChanInv!<dc, _!>(payload)
ensures  err != nil ==> err.ErrorMem()
func (dc *dataChannel) tryReceiveResponseModel(timeout time.Duration, ghost p perm) (payload ResponseChanPayload, err error) {
	if nonDeterministicChoice() {
		unfold acc(dc.Mem(), p)
		unfold acc(dc.MemInternal(dc.dataChannelState), p)
		fold PredTrue!<!>()
		var ok bool
		payload, ok = <-dc.hs.responseChan
		fold acc(dc.MemInternal(dc.dataChannelState), p)
		fold acc(dc.Mem(), p)
		if !ok {
			err = fmtError("Channel has been closed")
			return
		}
	} else {
		err = fmtError("Timeout occurred waiting for receiving a message on a channel")
	}
	return
}

ghost
requires noPerm < p
preserves acc(responseChan.RecvChannel(), p)
preserves responseChan.RecvGivenPerm() == PredTrue!<!>
preserves responseChan.RecvGotPerm() == ResponseChanInv!<dc, _!>
ensures  err == nil ==> ResponseChanInv!<dc, _!>(payload)
ensures  err != nil ==> err.ErrorMem()
func (dc *dataChannel) tryReceiveResponseModelAlt(responseChan chan ResponseChanPayload, timeout time.Duration, ghost p perm) (payload ResponseChanPayload, err error) {
	if nonDeterministicChoice() {
		fold PredTrue!<!>()
		var ok bool
		payload, ok = <-responseChan
		if !ok {
			err = fmtError("Channel has been closed")
			return
		}
	} else {
		err = fmtError("Timeout occurred waiting for receiving a message on a channel")
	}
	return
}
@*/

/*@
// TODO remove (used to  justify magic wand for `processStreamDataMessage`)
trusted
requires pl.token(t) && iospec.e_InFact(t, rid)
ensures   ok ==> msg.Mem() // && by.gamma(term) == abs.Abs(packet)
ensures   ok ==> pl.token(t1) && t1 == old(iospec.get_e_InFact_placeDst(t, rid)) && term == old(iospec.get_e_InFact_r1(t, rid))
ensures  !ok ==> t1 == t && pl.token(t) && iospec.e_InFact(t, rid) && iospec.get_e_InFact_placeDst(t, rid) == old(iospec.get_e_InFact_placeDst(t, rid)) && iospec.get_e_InFact_r1(t, rid) == old(iospec.get_e_InFact_r1(t, rid))
func Receive(streamDataMessage *mgsContracts.AgentMessage, ghost t pl.Place, ghost rid tm.Term) (msg *mgsContracts.AgentMessage, ok bool, ghost term tm.Term, ghost t1 pl.Place) {
	msg = streamDataMessage
	return
}

// TODO remove (used to  justify magic wand for `processStreamDataMessage`)
func ReceiveWand(streamDataMessage *mgsContracts.AgentMessage, ghost t pl.Place, ghost rid tm.Term) (msg *mgsContracts.AgentMessage, ok bool, ghost term tm.Term, ghost t1 pl.Place) {
	package (pl.token(t) && iospec.e_InFact(t, rid)) --* (ok ==> msg.Mem() && pl.token(t1) && t1 == old[#lhs](iospec.get_e_InFact_placeDst(t, rid)) && term == old[#lhs](iospec.get_e_InFact_r1(t, rid))) {
		msg, ok, term, t1 = Receive(streamDataMessage, t, rid)
		assert ok ==> msg.Mem()
	}
}
@*/
