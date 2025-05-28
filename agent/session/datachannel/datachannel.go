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
	"errors"
	"time"

	//@ "sync"

	logger "github.com/aws/amazon-ssm-agent/agent/log"
	mgsContracts "github.com/aws/amazon-ssm-agent/agent/session/contracts"
	"github.com/aws/amazon-ssm-agent/agent/session/datachannel/cryptolib"
	//@ abs "github.com/aws/amazon-ssm-agent/agent/iospecs/abs"
)

// SkipHandshake is used to skip handshake if the plugin decides it is not necessary
// @ preserves dc != nil ==> dc.Inv()
// @ preserves log != nil ==> acc(log.Mem(), _)
// @ ensures   err == nil ==> dc != nil && dc.getState() == HandshakeSkipped
// @ ensures   err != nil ==> err.ErrorMem()
func (dc *dataChannel) SkipHandshake(log logger.T) (err error) {
	if dc == nil || log == nil { //argot:ignore diodon-agent-io-independence
		err = fmtErrorNil()
		return
	}
	if dc.getState() != Initialized {
		err = fmtErrorInvalidState(dc.getState())
		return
	}
	logInfo(log, "Skipping handshake.")
	//@ unfold dc.Inv()
	idc := dc.idc
	//@ unfold idc.Mem()
	//@ unfold idc.MemInternal(Initialized)
	idc.hs.skipped = true
	//@ unfold acc(idc.MemChannelState(), 1/2)
	idc.dataChannelState = HandshakeSkipped
	//@ fold acc(idc.MemChannelState(), 1/2)
	//@ fold idc.MemInternal(HandshakeSkipped)
	//@ fold idc.Mem()
	//@ fold dc.Inv()
	return
}

// PerformHandshake performs handshake to share version string and encryption information with clients like cli/console
// Note that sessionplugin.go first calls `NewDataChannel` followed by at most 1 call to `PerformHandshake`.
// Hence, we can require in the specification that no other handshake is currently on-going for `dataChannel` without
// restricting the current client of `DataChannel`.
// @ requires  encryptionEnabled == assumeEncryptionEnabledForVerification()
// @ preserves dc != nil ==> dc.Inv()
// @ preserves log != nil ==> acc(log.Mem(), _)
// `sessionTypeRequest` is passed by value and contains a field `Properties` that remains opaque to the DataChannel.
// Alternatively, we could move serializing of this parameter to JSON to the caller.
// @ preserves sessionTypeRequest.Mem()
// @ ensures   err == nil ==> dc != nil && dc.getState() == IODistributed
// @ ensures   err != nil ==> err.ErrorMem()
func (dc *dataChannel) PerformHandshake(log logger.T,
	kmsKeyId string,
	encryptionEnabled bool,
	sessionTypeRequest mgsContracts.SessionTypeRequest) (err error) {

	if dc == nil || log == nil {
		err = fmtErrorNil()
		return
	}

	if dc.getState() != Initialized {
		err = fmtErrorInvalidState(dc.getState())
		return
	}

	logDebug(log, "PerformHandshake")

	//@ unfold dc.Inv()
	idc := dc.idc
	//@ unfold idc.Mem()
	//@ unfold idc.MemInternal(Initialized)

	idc.blockCipher = &cryptolib.BlockCipherT{}
	//@ fold idc.blockCipher.Mem()

	idc.hs.handshakeStartTime = time.Now()
	idc.encryptionEnabled = encryptionEnabled
	//@ unfold acc(idc.MemChannelState(), 1/2)
	idc.dataChannelState = BlockCipherInitialized
	//@ fold acc(idc.MemChannelState(), 1/2)
	//@ fold idc.MemInternal(BlockCipherInitialized)
	//@ fold idc.Mem()

	logInfo(log, "Initiating Handshake")
	handshakeRequestPayload, err :=
		idc.buildHandshakeRequestPayload(log, encryptionEnabled, sessionTypeRequest)
	if err != nil { //argot:ignore diodon-agent-io-independence
		//@ fold dc.Inv()
		return errHandshake() // safe generic error
	}
	dc.idc = idc
	err = idc.sendHandshakeRequest(log, handshakeRequestPayload /*@, sessionTypeRequest @*/)
	// we no longer need `handshakeRequestPayload` and, thus, we can restore permissions to `sessionTypeRequest`:
	//@ apply (handshakeRequestPayload.Mem() && handshakeRequestPayload.ContainsSessionTypeAction(sessionTypeRequest)) --* sessionTypeRequest.Mem()
	if err != nil {
		//@ fold dc.Inv()
		return errHandshake()
	}

	// notify Go routing handling received messages that it can process a message:
	//@ unfold idc.Mem()
	//@ unfold idc.MemInternal(HandshakeRequestSent)
	startReceivingChan := idc.hs.startReceivingChan
	responseChan := idc.hs.responseChan
	//@ fold idc.MemTransfer(HandshakeRequestSent, encryptionEnabled)
	var payload MessageReceptionPayload
	if encryptionEnabled {
		payload = MessageReceptionPayload{
			status: ReceiveHandshakeResponeEncryptionEnabled,
		}
	} else {
		payload = MessageReceptionPayload{
			status: ReceiveHandshakeResponeEncryptionDisabled,
		}
	}
	//@ fold StartReceivingChanInv!<idc, _!>(payload)
	startReceivingChan <- payload

	// Block until handshake response is received or handshake times out
	res, err := idc.tryReceiveResponse(responseChan, handshakeTimeout)
	if err != nil {
		//@ unfold acc(idc.MemChannelState(), 1/2)
		idc.dataChannelState = Erroneous
		//@ fold acc(idc.MemChannelState(), 1/2)
		//@ fold idc.MemInternal(Erroneous)
		//@ fold idc.Mem()
		//@ fold dc.Inv()
		// If handshake times out here this usually means that the client does not understand handshake or something
		// failed critically when processing handshake request.
		return errors.New("Handshake timed out. Please ensure that you have the latest version of the session manager plugin.")
	}
	// we send the flag `encryptionEnabled` back via the channel such that we are able to express the data channel's
	// state. This flag is expected to be identical to `encryptionEnabled`:
	if res.encryptionEnabled != encryptionEnabled {
		//@ unfold acc(idc.MemChannelState(), 1/2)
		idc.dataChannelState = Erroneous
		//@ fold acc(idc.MemChannelState(), 1/2)
		//@ fold idc.MemInternal(Erroneous)
		//@ fold idc.Mem()
		//@ fold dc.Inv()
		return errHandshake()
	}
	//@ unfold ResponseChanInv!<idc, _!>(res)
	//@ unfold idc.MemTransfer(res.state, encryptionEnabled)
	err = idc.hs.error
	if err != nil {
		//@ unfold acc(idc.MemChannelState(), 1/2)
		idc.dataChannelState = Erroneous
		//@ fold acc(idc.MemChannelState(), 1/2)
		//@ fold idc.MemInternal(Erroneous)
		//@ fold idc.Mem()
		//@ fold dc.Inv()
		return err
	}
	logDebug(log, "Handshake response received")

	//@ assert res.state == BlockCipherReady
	//@ unfold acc(idc.MemChannelState(), 1/2)
	idc.dataChannelState = res.state
	//@ fold acc(idc.MemChannelState(), 1/2)
	idc.hs.handshakeEndTime = time.Now()
	//@ fold idc.MemInternal(res.state)
	//@ fold idc.Mem()
	handshakeCompletePayload, err := idc.buildHandshakeCompletePayload(log)
	if err != nil {
		//@ fold dc.Inv()
		return err
	}
	if err := idc.sendHandshakeComplete(log, handshakeCompletePayload); err != nil {
		//@ fold dc.Inv()
		return err
	}
	//@ unfold idc.Mem()
	//@ unfold idc.MemInternal(HandshakeCompleted)
	logInfo(log, "Handshake successfully completed.")

	//@ unfold acc(idc.MemChannelState(), 1/2)
	idc.dataChannelState = IODistributed
	// do not fold `MemChannelState` since we split the permission to `dataChannelState` for
	// the threads next.

	//@ ghost idc.ioLock = new(sync.GhostMutex)
	//@ idc.ioLockDidLocalReceive = false
	//@ idc.ioLockCanRemoteSend = false
	//@ idc.ioLockDidRemoteReceive = false
	//@ idc.ioLockCanLocalSend = false
	//@ fold IoLockInv!<idc, idc.instanceId, idc.clientId, idc.secrets.agentLTKeyARN!>()
	//@ idc.ioLock.SetInv(IoLockInv!<idc, idc.instanceId, idc.clientId, idc.secrets.agentLTKeyARN!>)

	payload = MessageReceptionPayload{
		status: ReceiveOtherResponse,
	}
	//@ fold idc.MemRecv()
	//@ fold StartReceivingChanInv!<idc, _!>(payload)
	startReceivingChan <- payload

	//@ fold acc(idc.MemInternal(IODistributed), 1/2)
	//@ fold idc.Mem()
	//@ fold dc.Inv()
	return
}

// @ requires noPerm < p
// @ preserves acc(bytes.SliceMem(s), p)
// @ ensures  bytes.SliceMem(res) && abs.Abs(s) == abs.Abs(res)
func duplicate(s []byte /*@, ghost p perm @*/) (res []byte) {
	res = make([]byte, len(s))
	//@ unfold acc(bytes.SliceMem(s), p)
	copy(res, s /*@, p/2 @*/)
	//@ fold acc(bytes.SliceMem(s), p)
	//@ fold bytes.SliceMem(res)
	// TODO: since `Abs` is not axiomatized to express that it only depends
	// on the content of a byte slice, we have to assume this equality for now:
	//@ assume abs.Abs(s) == abs.Abs(res)
	return res
}

// GetClientVersion returns version of the client
// @ preserves dc != nil ==> dc.Inv()
// @ ensures   err != nil ==> err.ErrorMem()
// @ ensures   dc != nil ==> dc.getState() == old(dc.getState())
func (dc *dataChannel) GetClientVersion() (version string, err error) {
	if dc == nil { //argot:ignore diodon-agent-io-independence
		err = fmtErrorNil()
		return
	}
	//@ unfold dc.Inv()
	version, err = dc.idc.getClientVersion()
	//@ fold dc.Inv()
	return
}

// @ preserves idc.Mem()
// @ ensures   err != nil ==> err.ErrorMem()
// @ ensures   idc.getState() == old(idc.getState())
func (idc *internalDataChannel) getClientVersion() (version string, err error) {
	if idc.getState() == Erroneous {
		err = fmtErrorInvalidState(idc.getState())
		return
	}
	return /*@ unfolding idc.Mem() in unfolding acc(idc.MemInternal(idc.dataChannelState), 1/2) in @*/ idc.hs.clientVersion, nil
}

// GetInstanceId returns id of the target
// @ preserves dc != nil ==> dc.Inv()
// @ ensures   err != nil ==> err.ErrorMem()
func (dc *dataChannel) GetInstanceId() (instanceId string, err error) {
	if dc == nil {
		err = fmtErrorNil()
		return
	}
	if dc.getState() < Initialized {
		err = fmtErrorInvalidState(dc.getState())
		return
	}
	return /*@ unfolding dc.Inv() in unfolding dc.idc.Mem() in unfolding acc(dc.idc.MemInternal(dc.idc.dataChannelState), 1/2) in @*/ dc.idc.instanceId, nil
}

// GetRegion returns aws region of the target
// @ preserves dc != nil ==> dc.Inv()
// @ ensures   err != nil ==> err.ErrorMem()
func (dc *dataChannel) GetRegion() (region string, err error) {
	if dc == nil {
		err = fmtErrorNil()
		return
	}
	if dc.getState() < Initialized {
		err = fmtErrorInvalidState(dc.getState())
		return
	}
	return /*@ unfolding dc.Inv() in unfolding dc.idc.Mem() in unfolding acc(dc.idc.MemInternal(dc.idc.dataChannelState), 1/2) in @*/ dc.idc.dataStream.GetRegion(), nil
}

// IsActive returns a boolean value indicating the datachannel is actively listening
// and communicating with service
// @ preserves dc != nil ==> dc.Inv()
// @ ensures   err != nil ==> err.ErrorMem()
func (dc *dataChannel) IsActive() (isActive bool, err error) {
	if dc == nil {
		err = fmtErrorNil()
		return
	}
	if dc.getState() < Initialized {
		err = fmtErrorInvalidState(dc.getState())
		return
	}
	return /*@ unfolding dc.Inv() in unfolding dc.idc.Mem() in unfolding acc(dc.idc.MemInternal(dc.idc.dataChannelState), 1/2) in @*/ dc.idc.dataStream.IsActive(), nil
}

// GetSeparateOutputPayload returns boolean value indicating separate
// stdout/stderr output for non-interactive session or not
// @ preserves dc != nil ==> dc.Inv()
// @ ensures   err != nil ==> err.ErrorMem()
func (dc *dataChannel) GetSeparateOutputPayload() (res bool, err error) {
	if dc == nil {
		err = fmtErrorNil()
		return
	}
	if dc.getState() == Erroneous {
		err = fmtErrorInvalidState(dc.getState())
		return
	}
	return /*@ unfolding dc.Inv() in unfolding dc.idc.Mem() in unfolding acc(dc.idc.MemInternal(dc.idc.dataChannelState), _) in @*/ dc.idc.separateOutputPayload, nil
}

// SetSeparateOutputPayload set separateOutputPayload value
// @ preserves dc != nil ==> dc.Inv()
// @ ensures   err != nil ==> err.ErrorMem()
// @ ensures   dc != nil ==> dc.getState() == old(dc.getState())
func (dc *dataChannel) SetSeparateOutputPayload(separateOutputPayload bool) (err error) {
	if dc == nil { //argot:ignore diodon-agent-io-independence
		err = fmtErrorNil()
		return
	}
	if dc.getState() == Erroneous || dc.getState() == IODistributed {
		err = fmtErrorInvalidState(dc.getState())
		return
	}
	//@ unfold dc.Inv()
	//@ unfold dc.idc.Mem()
	//@ state := dc.idc.dataChannelState
	//@ unfold dc.idc.MemInternal(state)
	dc.idc.separateOutputPayload = separateOutputPayload
	//@ fold dc.idc.MemInternal(state)
	//@ fold dc.idc.Mem()
	//@ fold dc.Inv()
	return
}

// @ preserves dc != nil ==> dc.Inv()
// @ preserves log != nil ==> acc(log.Mem(), _)
// @ ensures   err != nil ==> err.ErrorMem()
// @ ensures   dc != nil ==> dc.getState() == old(dc.getState())
func (dc *dataChannel) PrepareToCloseChannel(log logger.T) (err error) {
	if dc == nil || log == nil { //argot:ignore diodon-agent-io-independence
		err = fmtErrorNil()
		return
	}
	if dc.getState() < Initialized {
		err = fmtErrorInvalidState(dc.getState())
		return
	}
	//@ unfold dc.Inv()
	//@ unfold dc.idc.Mem()
	//@ state := dc.idc.dataChannelState
	//@ unfold acc(dc.idc.MemInternal(state), 1/4)
	dc.idc.dataStream.PrepareToCloseChannel(log /*@, perm(1/8) @*/)
	//@ fold acc(dc.idc.MemInternal(state), 1/4)
	//@ fold dc.idc.Mem()
	//@ fold dc.Inv()
	return
}

// @ preserves dc != nil ==> dc.Inv()
// @ preserves log != nil ==> acc(log.Mem(), _)
// @ ensures   err != nil ==> err.ErrorMem()
// @ ensures   dc != nil ==> dc.getState() == old(dc.getState())
func (dc *dataChannel) Close(log logger.T) (err error) {
	if dc == nil || log == nil { //argot:ignore diodon-agent-io-independence
		err = fmtErrorNil()
		return
	}
	if dc.getState() < Initialized {
		err = fmtErrorInvalidState(dc.getState())
		return
	}
	//@ unfold dc.Inv()
	//@ unfold dc.idc.Mem()
	//@ state := dc.idc.dataChannelState
	//@ unfold acc(dc.idc.MemInternal(state), 1/4)
	err = dc.idc.dataStream.Close(log /*@, perm(1/8) @*/)
	//@ fold acc(dc.idc.MemInternal(state), 1/4)
	//@ fold dc.idc.Mem()
	//@ fold dc.Inv()
	return
}
