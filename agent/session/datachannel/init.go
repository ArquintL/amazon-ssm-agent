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

	contextPkg "github.com/aws/amazon-ssm-agent/agent/context"
	mgsContracts "github.com/aws/amazon-ssm-agent/agent/session/contracts"
	"github.com/aws/amazon-ssm-agent/agent/session/datastream"
	"github.com/aws/amazon-ssm-agent/agent/task"
	//@ "github.com/aws/amazon-ssm-agent/agent/iospecs/arb"
	//@ ft "github.com/aws/amazon-ssm-agent/agent/iospecs/fact"
	//@ "github.com/aws/amazon-ssm-agent/agent/iospecs/iospec"
	//@ pl "github.com/aws/amazon-ssm-agent/agent/iospecs/place"
	//@ "github.com/aws/amazon-ssm-agent/agent/session/datachannel/iosanitization"
)

// NewDataChannel constructs datachannel objects.
// `context` and `cancelFlag` are opaque to the core. We assume that they are thread safe
// @ requires context != nil ==> acc(context.Mem(), _)
// @ requires cancelFlag != nil ==> acc(cancelFlag.Mem(), _)
// @ requires inputStreamMessageHandler implements iosanitization.StreamDataHandlerSpec{}
// @ ensures  res.Mem() && typeOf(res) == *dataChannel
// @ ensures  err == nil ==> res.(* dataChannel).getState() == Initialized
func NewDataChannel(context contextPkg.T,
	channelId string,
	clientId string,
	logReaderId string,
	inputStreamMessageHandler InputStreamMessageHandler,
	cancelFlag task.CancelFlag) (res IDataChannel, err error) {

	// pick an arbitrary rid for this protocol session and inhale the IO specification for
	// the SSM agent and the chosen protocol session:
	//@ t0, rid := arb.GetArbPlace(), arb.GetArbTerm()
	//@ inhale pl.token(t0) && iospec.P_Agent(t0, rid, mset[ft.Fact]{})

	tmp /*@ @ @*/ := dataChannel{}
	dc := &tmp
	cl :=
		// @ requires  msg != nil ==> msg.Mem()
		// @ preserves tmp.RecvRoutineMem()
		// @ ensures   err != nil ==> err.ErrorMem()
		func /*@ callHandler @*/ (msg *mgsContracts.AgentMessage) (err error) {
			if msg == nil {
				return fmtError("received agent message is nil")
			}
			err = tmp.processStreamDataMessage(msg)
			return
		}
	/*@
		proof cl implements datastream.StreamDataHandlerSpec{dc} {
	        unfold dc.Inv()
	        err = cl(msg) as callHandler
			fold dc.Inv()
	    }
	@*/

	dc.dataChannelState = Uninitialized
	dc.hs.startReceivingChan = make(chan MessageReceptionPayload)
	//@ dc.hs.startReceivingChan.Init(StartReceivingChanInv!<dc, _!>, PredTrue!<!>)
	dc.inputStreamMessageHandler = inputStreamMessageHandler
	dc.hs.responseChan = make(chan ResponseChanPayload)
	//@ dc.hs.responseChan.Init(ResponseChanInv!<dc, _!>, PredTrue!<!>)
	//@ ghost dc.io = new(ioSpecFields)
	//@ dc.io.token = t0
	//@ dc.io.rid = rid
	//@ dc.io.absState = mset[ft.Fact]{}
	// fold dc.IoSpecMem()
	//@ fold dc.io.IoSpecMemMain()
	//@ fold dc.io.IoSpecMemPartial()

	//@ fold dc.RecvRoutineMem()
	//@ fold acc(dc.MemChannelState(), 1/2)
	//@ fold dc.MemInternal(Uninitialized)
	//@ fold dc.Mem()
	//@ fold dc.Inv()
	dataStream, err := datastream.NewDataStream(context,
		channelId,
		clientId,
		logReaderId,
		cl,
		cancelFlag,
		/*@ dc @*/)
	if err != nil {
		// we return a non-nil dc such that we can ensure `dc.Mem()`
		// independent of `err`. However, clients should check whether
		// `err` is nil.
		return dc, fmtErrorf("failed to create data stream with error", err /*@, perm(1/2) @*/)
	}

	err = dc.initialize(dataStream)
	if err != nil {
		return dc, err
	}

	return dc, nil
}

// initialize populates datachannel object.
// @ requires dc.Mem() && dc.getState() == Uninitialized && dataStream.Mem()
// @ requires acc(&dc.io, 1/2) && dc.io.IoSpecMemMain() && dc.io.IoSpecMemPartial() && pl.token(dc.io.getToken()) && iospec.P_Agent(dc.io.getToken(), dc.io.getRid(), dc.io.getAbsState())
// @ ensures  dc.Mem()
// @ ensures  err == nil ==> dc.getState() == Initialized
func (dc *dataChannel) initialize(dataStream *datastream.DataStream) (err error) {
	// @ unfold dc.Mem()
	// @ unfold dc.MemInternal(Uninitialized)
	dc.dataStream = dataStream
	dc.encryptionEnabled = false
	dc.hs.error = nil
	dc.hs.complete = false
	dc.hs.skipped = false
	dc.hs.handshakeEndTime = time.Now()
	dc.hs.handshakeStartTime = time.Now()

	dc.kmsService, err = dataStream.GetKMSService( /*@ perm(1/2) @*/ )
	if err != nil {
		// @ fold dc.MemInternal(Uninitialized)
		// @ fold dc.Mem()
		return fmtErrorf("failed to initialize KMS service", err /*@, perm(1/2) @*/)
	}

	// @ t0 := dc.io.getToken()
	// @ rid := dc.io.getRid()
	// @ s0 := dc.io.getAbsState()
	// @ unfold iospec.P_Agent(t0, rid, s0)
	// @ unfold iospec.phiRF_Agent_17(t0, rid, s0)
	// @ t1 := iospec.get_e_Setup_Agent_placeDst(t0, rid)
	// @ agentIdT := iospec.get_e_Setup_Agent_r1(t0, rid)
	// @ kmsIdT := iospec.get_e_Setup_Agent_r2(t0, rid)
	// @ clientIdT := iospec.get_e_Setup_Agent_r3(t0, rid)
	// @ readerIdT := iospec.get_e_Setup_Agent_r4(t0, rid)
	// @ logLTPkT := iospec.get_e_Setup_Agent_r6(t0, rid)
	// @ setupFact := ft.Setup_Agent(rid, agentIdT, kmsIdT, clientIdT, readerIdT, iospec.get_e_Setup_Agent_r5(t0, rid), logLTPkT)
	dc.instanceId, dc.clientId, dc.logReaderId, dc.secrets.agentLTKeyARN, dc.logLTPk, err = getInitialValues(dc.dataStream, dc.kmsService /*@, t0, rid @*/)
	if err != nil {
		// @ fold iospec.phiRF_Agent_17(t0, rid, s0)
		// @ fold iospec.P_Agent(t0, rid, s0)
		// @ fold dc.MemInternal(Uninitialized)
		// @ fold dc.Mem()
		return fmtError("failed to initialize KMS key values")
		// return fmtErrorf("failed to initialize KMS service", err /*@, perm(1/2) @*/)
	}

	// @ s1 := s0 union mset[ft.Fact]{ setupFact }
	// @ unfold dc.io.IoSpecMemMain()
	// @ unfold dc.io.IoSpecMemPartial()
	// @ dc.io.token = t1
	// @ dc.io.absState = s1
	// @ dc.io.agentIdT = agentIdT
	// @ dc.io.kMSIdT = kmsIdT
	// @ dc.io.clientIdT = clientIdT
	// @ dc.io.readerIdT = readerIdT
	// @ dc.io.logLTPkT = logLTPkT
	// @ fold dc.io.IoSpecMemPartial()
	// @ fold dc.io.IoSpecMemMain()
	// @ unfold acc(dc.MemChannelState(), 1/2)
	dc.dataChannelState = Initialized
	// @ fold acc(dc.MemChannelState(), 1/2)
	// @ fold dc.MemInternal(Initialized)
	// @ fold dc.Mem()
	return nil
}
