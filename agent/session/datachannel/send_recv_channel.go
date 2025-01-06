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
// @ requires acc(responseChan.RecvChannel(), _)
// @ requires responseChan.RecvGivenPerm() == PredTrue!<!>
// @ requires responseChan.RecvGotPerm() == ResponseChanInv!<dc, _!>
// @ ensures  responseChan.RecvChannel()
// @ ensures  responseChan.RecvGivenPerm() == PredTrue!<!>
// @ ensures  responseChan.RecvGotPerm() == ResponseChanInv!<dc, _!>
// @ ensures  err == nil ==> ResponseChanInv!<dc, _!>(payload)
// @ ensures  err != nil ==> err.ErrorMem()
func (dc *dataChannel) tryReceiveResponse(responseChan chan ResponseChanPayload, timeout time.Duration) (payload ResponseChanPayload, err error) {
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
decreases
func nonDeterministicChoice() bool

// this models `tryReceiveMessageReceptionStatus` as Gobra does not yet support the `select` statement
// we use this function to validate the spec of `tryReceiveMessageReceptionStatus`
ghost
decreases _
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
			err = ghostFmtError("Channel has been closed")
			return
		}
	} else {
		err = ghostFmtError("Timeout occurred waiting for receiving a message on a channel")
	}
	return
}

// this models `tryReceiveResponse` as Gobra does not yet support the `select` statement
// we use this function to validate the spec of `tryReceiveResponse`
ghost
decreases _
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
			err = ghostFmtError("Channel has been closed")
			return
		}
	} else {
		err = ghostFmtError("Timeout occurred waiting for receiving a message on a channel")
	}
	return
}

ghost
trusted
decreases
ensures err != nil && err.ErrorMem()
func ghostFmtError(str string) (err error) {
	return fmt.Errorf(str)
}
@*/
