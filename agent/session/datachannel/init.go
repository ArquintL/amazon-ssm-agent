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
// @ requires context != nil && acc(context.Mem(), _) && acc(cancelFlag.Mem(), _)
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
		// @ requires datastream.StreamDataHandlerFootprint(msg)
		// @ preserves tmp.RecvRoutineMem()
		// @ ensures err != nil ==> err.ErrorMem()
		func /*@ callHandler @*/ (msg *mgsContracts.AgentMessage) (err error) {
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
	// we allocate some ghost heap space:
	//@ inhale dc.IoSpecMem()
	//@ unfold dc.IoSpecMem()
	// the following assertion is needed:
	//@ assert dc.TokenMem()
	//@ dc.setToken(t0)
	//@ dc.setRid(rid)
	//@ dc.setAbsState(mset[ft.Fact]{})
	// fold dc.IoSpecMem()
	//@ fold dc.IoSpecMemMain()
	//@ fold dc.IoSpecMemPartial()

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
// @ requires dc.IoSpecMemMain() && dc.IoSpecMemPartial() && pl.token(dc.getToken()) && iospec.P_Agent(dc.getToken(), dc.getRid(), dc.getAbsState())
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

	// @ t0 := dc.getToken()
	// @ rid := dc.getRid()
	// @ s0 := dc.getAbsState()
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
	// @ unfold dc.IoSpecMemMain()
	// @ unfold dc.IoSpecMemPartial()
	// @ dc.setToken(t1)
	// @ dc.setAbsState(s1)
	// @ dc.setAgentIdT(agentIdT)
	// @ dc.setKMSIdT(kmsIdT)
	// @ dc.setClientIdT(clientIdT)
	// @ dc.setReaderIdT(readerIdT)
	// @ dc.setLogLTPkT(logLTPkT)
	// @ fold dc.IoSpecMemPartial()
	// @ fold dc.IoSpecMemMain()
	// @ unfold acc(dc.MemChannelState(), 1/2)
	dc.dataChannelState = Initialized
	// @ fold acc(dc.MemChannelState(), 1/2)
	// @ fold dc.MemInternal(Initialized)
	// @ fold dc.Mem()
	return nil
}
