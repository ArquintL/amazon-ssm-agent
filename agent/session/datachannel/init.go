package datachannel

import (
	cryptoRand "crypto/rand"
	"crypto/rsa"
	"time"

	contextPkg "github.com/aws/amazon-ssm-agent/agent/context"
	"github.com/aws/amazon-ssm-agent/agent/log"
	mgsContracts "github.com/aws/amazon-ssm-agent/agent/session/contracts"
	"github.com/aws/amazon-ssm-agent/agent/session/crypto"
	"github.com/aws/amazon-ssm-agent/agent/session/datastream"
	"github.com/aws/amazon-ssm-agent/agent/task"
	//@ by "github.com/aws/amazon-ssm-agent/agent/iospecs/bytes"
	//@ ft "github.com/aws/amazon-ssm-agent/agent/iospecs/fact"
	//@ "github.com/aws/amazon-ssm-agent/agent/iospecs/iospec"
	//@ pl "github.com/aws/amazon-ssm-agent/agent/iospecs/place"
	//@ pub "github.com/aws/amazon-ssm-agent/agent/iospecs/pub"
	//@ tm "github.com/aws/amazon-ssm-agent/agent/iospecs/term"
)

// NewDataChannel constructs datachannel objects.
// @ requires context.Mem() && cancelFlag.Mem()
// @ requires ctx != nil && ctx.Inv() && inputStreamMessageHandler implements StreamDataHandlerSpec{ctx}
// @ requires pl.token(t0) && iospec.P_Agent(t0, rid, mset[ft.Fact]{})
// @ ensures  res.Mem() && typeOf(res) == *dataChannel
// @ ensures  err == nil ==> res.(* dataChannel).getState() == Initialized
// TODO: make `ctx` a ghost parameter as soon as Gobra supports ghost fields
func NewDataChannel(context contextPkg.T,
	channelId string,
	clientId string,
	logReaderId string,
	inputStreamMessageHandler InputStreamMessageHandler,
	cancelFlag task.CancelFlag,
	/*@ ctx StreamDataHandlerContext, t0 pl.Place, rid tm.Term @*/) (res IDataChannel, err error) {

	tmp /*@ @ @*/ := dataChannel{}
	dc := &tmp
	cl := // @ requires log != nil
		// @ requires datastream.QuantifiedStreamDataHandlerSpecWand(msg)
		// @ preserves acc(log.Mem(), _) && tmp.RecvRoutineMem()
		// @ ensures err == nil ==> msg.Mem()
		// @ ensures err != nil ==> err.ErrorMem()
		func /*@ callHandler @*/ (_ log.T, msg *mgsContracts.AgentMessage) (err error) {
			err = tmp.processStreamDataMessage(msg)
			return
		}
	/*@
		proof cl implements datastream.StreamDataHandlerSpec{dc} {
	        unfold dc.Inv()
	        err = cl(log, msg) as callHandler
			fold dc.Inv()
	    }
	@*/

	dc.dataChannelState = Uninitialized
	dc.hs.startReceivingChan = make(chan MessageReceptionPayload)
	//@ dc.hs.startReceivingChan.Init(StartReceivingChanInv!<dc, _!>, PredTrue!<!>)
	dc.inputStreamMessageHandler = inputStreamMessageHandler
	//@ dc.msgHandlerCtx = ctx
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
		cl,
		cancelFlag,
		/*@ dc @*/)
	if err != nil {
		// we return a non-nil dc such that we can ensure `dc.Mem()`
		// independent of `err`. However, clients should check whether
		// `err` is nil.
		return dc, fmtErrorf("failed to create data stream with error", err /*@, perm(1/2) @*/)
	}

	err = dc.initialize(dataStream, logReaderId)
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
func (dc *dataChannel) initialize(dataStream *datastream.DataStream, logReaderId string) (err error) {
	// @ unfold dc.Mem()
	// @ unfold dc.MemInternal(Uninitialized)
	dc.dataStream = dataStream
	dc.encryptionEnabled = false
	dc.hs.error = nil
	dc.hs.complete = false
	dc.hs.skipped = false
	dc.hs.handshakeEndTime = time.Now()
	dc.hs.handshakeStartTime = time.Now()
	var kms *crypto.KMSService
	ds := dc.dataStream
	kms, err = ds.GetKMSService()
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
	agentLTKeyARN, logLTPk, err := getInitialValues(kms /*@, t0, rid @*/)
	if err != nil {
		// @ fold iospec.phiRF_Agent_17(t0, rid, s0)
		// @ fold iospec.P_Agent(t0, rid, s0)
		// @ fold dc.MemInternal(Uninitialized)
		// @ fold dc.Mem()
		return fmtError("failed to initialize KMS key values")
		// return fmtErrorf("failed to initialize KMS service", err /*@, perm(1/2) @*/)
	}

	dc.secrets.agentLTKeyARN = agentLTKeyARN
	dc.logLTPk = logLTPk
	dc.kmsService = kms
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
	dc.logReaderId = logReaderId
	// @ unfold acc(dc.MemChannelState(), 1/2)
	dc.dataChannelState = Initialized
	// @ fold acc(dc.MemChannelState(), 1/2)
	// @ fold dc.MemInternal(Initialized)
	// @ fold dc.Mem()
	return nil
}

// we assume that this function returns the initial values used by this agent session
// according to the `Agent_Init` Tamarin rule
// @ trusted
// @ preserves kmsService.Mem()
// @ requires pl.token(t) && iospec.e_Setup_Agent(t, rid)
// @ ensures  err == nil ==> logLTPk.Mem()
// @ ensures  err == nil ==> pl.token(old(iospec.get_e_Setup_Agent_placeDst(t, rid))) &&
// @	by.gamma(tm.pubTerm(pub.pub_msg(agentId))) == by.gamma(old(iospec.get_e_Setup_Agent_r1(t, rid))) &&
// @	by.gamma(tm.pubTerm(pub.pub_msg(clientId))) == by.gamma(old(iospec.get_e_Setup_Agent_r3(t, rid))) &&
// @	by.gamma(tm.pubTerm(pub.pub_msg(logReaderId))) == by.gamma(old(iospec.get_e_Setup_Agent_r4(t, rid))) &&
// @	by.gamma(tm.pubTerm(pub.pub_msg(agentLTKeyARN))) == by.gamma(old(iospec.get_e_Setup_Agent_r5(t, rid))) &&
// @	logLTPk.Abs() == by.gamma(old(iospec.get_e_Setup_Agent_r6(t, rid)))
// Patern axiom applies locally:
// @ ensures  by.gamma(old(iospec.get_e_Setup_Agent_r1(t, rid))) == by.gamma(tm.pubTerm(pub.pub_msg(agentId))) ==> old(iospec.get_e_Setup_Agent_r1(t, rid)) == tm.pubTerm(pub.pub_msg(agentId))
// @ ensures  by.gamma(old(iospec.get_e_Setup_Agent_r3(t, rid))) == by.gamma(tm.pubTerm(pub.pub_msg(clientId))) ==> old(iospec.get_e_Setup_Agent_r3(t, rid)) == tm.pubTerm(pub.pub_msg(clientId))
// @ ensures  by.gamma(old(iospec.get_e_Setup_Agent_r4(t, rid))) == by.gamma(tm.pubTerm(pub.pub_msg(logReaderId))) ==> old(iospec.get_e_Setup_Agent_r4(t, rid)) == tm.pubTerm(pub.pub_msg(logReaderId))
// @ ensures  by.gamma(old(iospec.get_e_Setup_Agent_r5(t, rid))) == by.gamma(tm.pubTerm(pub.pub_msg(agentLTKeyARN))) ==> old(iospec.get_e_Setup_Agent_r5(t, rid)) == tm.pubTerm(pub.pub_msg(agentLTKeyARN))
// @ ensures err != nil ==> err.ErrorMem()
// @ ensures err != nil ==> pl.token(t) && iospec.e_Setup_Agent(t, rid) &&
// @ 	iospec.get_e_Setup_Agent_placeDst(t, rid) == old(iospec.get_e_Setup_Agent_placeDst(t, rid)) &&
// @ 	iospec.get_e_Setup_Agent_r1(t, rid) == old(iospec.get_e_Setup_Agent_r1(t, rid)) &&
// @ 	iospec.get_e_Setup_Agent_r2(t, rid) == old(iospec.get_e_Setup_Agent_r2(t, rid)) &&
// @ 	iospec.get_e_Setup_Agent_r3(t, rid) == old(iospec.get_e_Setup_Agent_r3(t, rid)) &&
// @ 	iospec.get_e_Setup_Agent_r4(t, rid) == old(iospec.get_e_Setup_Agent_r4(t, rid)) &&
// @ 	iospec.get_e_Setup_Agent_r5(t, rid) == old(iospec.get_e_Setup_Agent_r5(t, rid)) &&
// @ 	iospec.get_e_Setup_Agent_r6(t, rid) == old(iospec.get_e_Setup_Agent_r6(t, rid))
func getInitialValues(kmsService *crypto.KMSService /*@, ghost t pl.Place, ghost rid tm.Term @*/) (agentLTKeyARN string, logLTPk *rsa.PublicKey, err error) {
	metadata, err := kmsService.CreateKeyAssymetric()
	if err != nil {
		err = fmtErrorf("failed to create agent LTK", err /*@, perm(1/1) @*/)
		return "", nil, err /*@, t @*/
	}

	//@ unfold metadata.Mem()
	if metadata.Arn == nil {
		err = fmtErrorfMetadata("asymmetric key ARN is nil, metadata", metadata /*@, perm(1/2) @*/)
		return "", nil, err /*@, t @*/
	}
	agentLTKeyARN = *metadata.Arn
	//@ cryptoRand.GetReaderMem()
	sk, err := rsa.GenerateKey(cryptoRand.Reader, 4096 /*@, perm(1/2) @*/)
	if err != nil {
		err = fmtErrorf("failed to create log secret key", err /*@, perm(1/1) @*/)
		return "", nil, err /*@, t @*/
	}
	//@ unfold sk.Mem()
	logLTPk = &sk.PublicKey
	return
}
