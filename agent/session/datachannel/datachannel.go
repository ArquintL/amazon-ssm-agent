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
// @ preserves dc != nil ==> dc.Mem()
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
	//@ unfold dc.Mem()
	//@ unfold dc.MemInternal(Initialized)
	dc.hs.skipped = true
	//@ unfold acc(dc.MemChannelState(), 1/2)
	dc.dataChannelState = HandshakeSkipped
	//@ fold acc(dc.MemChannelState(), 1/2)
	//@ fold dc.MemInternal(HandshakeSkipped)
	//@ fold dc.Mem()
	return
}

// PerformHandshake performs handshake to share version string and encryption information with clients like cli/console
// Note that sessionplugin.go first calls `NewDataChannel` followed by at most 1 call to `PerformHandshake`.
// Hence, we can require in the specification that no other handshake is currently on-going for `dataChannel` without
// restricting the current client of `DataChannel`.
// @ requires  encryptionEnabled == assumeEncryptionEnabledForVerification()
// @ preserves dc != nil ==> dc.Mem()
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

	//@ unfold dc.Mem()
	//@ unfold dc.MemInternal(Initialized)

	dc.blockCipher = &cryptolib.BlockCipherT{}
	//@ fold dc.blockCipher.Mem()

	dc.hs.handshakeStartTime = time.Now()
	dc.encryptionEnabled = encryptionEnabled
	//@ unfold acc(dc.MemChannelState(), 1/2)
	dc.dataChannelState = BlockCipherInitialized
	//@ fold acc(dc.MemChannelState(), 1/2)
	//@ fold dc.MemInternal(BlockCipherInitialized)
	//@ fold dc.Mem()

	logInfo(log, "Initiating Handshake")
	handshakeRequestPayload, err :=
		dc.buildHandshakeRequestPayload(log, encryptionEnabled, sessionTypeRequest)
	if err != nil { //argot:ignore diodon-agent-io-independence
		return errHandshake() // safe generic error
	}
	err = dc.sendHandshakeRequest(log, handshakeRequestPayload /*@, sessionTypeRequest @*/)
	// we no longer need `handshakeRequestPayload` and, thus, we can restore permissions to `sessionTypeRequest`:
	//@ apply (handshakeRequestPayload.Mem() && handshakeRequestPayload.ContainsSessionTypeAction(sessionTypeRequest)) --* sessionTypeRequest.Mem()
	if err != nil {
		return errHandshake()
	}

	// notify Go routing handling received messages that it can process a message:
	//@ unfold dc.Mem()
	//@ unfold dc.MemInternal(HandshakeRequestSent)
	startReceivingChan := dc.hs.startReceivingChan
	responseChan := dc.hs.responseChan
	//@ fold dc.MemTransfer(HandshakeRequestSent, encryptionEnabled)
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
	//@ fold StartReceivingChanInv!<dc, _!>(payload)
	startReceivingChan <- payload

	// Block until handshake response is received or handshake times out
	res, err := dc.tryReceiveResponse(responseChan, handshakeTimeout)
	if err != nil {
		//@ unfold acc(dc.MemChannelState(), 1/2)
		dc.dataChannelState = Erroneous
		//@ fold acc(dc.MemChannelState(), 1/2)
		//@ fold dc.MemInternal(Erroneous)
		//@ fold dc.Mem()
		// If handshake times out here this usually means that the client does not understand handshake or something
		// failed critically when processing handshake request.
		return errors.New("Handshake timed out. Please ensure that you have the latest version of the session manager plugin.")
	}
	// we send the flag `encryptionEnabled` back via the channel such that we are able to express the data channel's
	// state. This flag is expected to be identical to `encryptionEnabled`:
	if res.encryptionEnabled != encryptionEnabled {
		//@ unfold acc(dc.MemChannelState(), 1/2)
		dc.dataChannelState = Erroneous
		//@ fold acc(dc.MemChannelState(), 1/2)
		//@ fold dc.MemInternal(Erroneous)
		//@ fold dc.Mem()
		return errHandshake()
	}
	//@ unfold ResponseChanInv!<dc, _!>(res)
	//@ unfold dc.MemTransfer(res.state, encryptionEnabled)
	err = dc.hs.error
	if err != nil {
		//@ unfold acc(dc.MemChannelState(), 1/2)
		dc.dataChannelState = Erroneous
		//@ fold acc(dc.MemChannelState(), 1/2)
		//@ fold dc.MemInternal(Erroneous)
		//@ fold dc.Mem()
		return err
	}
	logDebug(log, "Handshake response received")

	//@ assert res.state == BlockCipherReady
	//@ unfold acc(dc.MemChannelState(), 1/2)
	dc.dataChannelState = res.state
	//@ fold acc(dc.MemChannelState(), 1/2)
	dc.hs.handshakeEndTime = time.Now()
	//@ fold dc.MemInternal(res.state)
	//@ fold dc.Mem()
	handshakeCompletePayload, err := dc.buildHandshakeCompletePayload(log)
	if err != nil {
		return err
	}
	if err := dc.sendHandshakeComplete(log, handshakeCompletePayload); err != nil {
		return err
	}
	//@ unfold dc.Mem()
	//@ unfold dc.MemInternal(HandshakeCompleted)
	logInfo(log, "Handshake successfully completed.")

	//@ unfold acc(dc.MemChannelState(), 1/2)
	dc.dataChannelState = IODistributed
	// do not fold `MemChannelState` since we split the permission to `dataChannelState` for
	// the threads next.

	//@ ghost dc.ioLock = new(sync.GhostMutex)
	//@ dc.ioLockDidLocalReceive = false
	//@ dc.ioLockCanRemoteSend = false
	//@ dc.ioLockDidRemoteReceive = false
	//@ dc.ioLockCanLocalSend = false
	//@ fold IoLockInv!<dc, dc.instanceId, dc.clientId, dc.secrets.agentLTKeyARN!>()
	//@ dc.ioLock.SetInv(IoLockInv!<dc, dc.instanceId, dc.clientId, dc.secrets.agentLTKeyARN!>)

	payload = MessageReceptionPayload{
		status: ReceiveOtherResponse,
	}
	//@ fold dc.MemRecv()
	//@ fold StartReceivingChanInv!<dc, _!>(payload)
	startReceivingChan <- payload

	//@ fold acc(dc.MemInternal(IODistributed), 1/2)
	//@ fold dc.Mem()
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
// @ preserves dc != nil ==> dc.Mem()
// @ ensures   err != nil ==> err.ErrorMem()
// @ ensures   dc != nil ==> dc.getState() == old(dc.getState())
func (dc *dataChannel) GetClientVersion() (version string, err error) {
	if dc == nil { //argot:ignore diodon-agent-io-independence
		err = fmtErrorNil()
		return
	}
	if dc.getState() == Erroneous {
		err = fmtErrorInvalidState(dc.getState())
		return
	}
	return /*@ unfolding dc.Mem() in unfolding acc(dc.MemInternal(dc.dataChannelState), 1/2) in @*/ dc.hs.clientVersion, nil
}

// GetInstanceId returns id of the target
// @ preserves dc != nil ==> dc.Mem()
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
	return /*@ unfolding dc.Mem() in unfolding acc(dc.MemInternal(dc.dataChannelState), 1/2) in @*/ dc.instanceId, nil
}

// GetRegion returns aws region of the target
// @ preserves dc != nil ==> dc.Mem()
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
	return /*@ unfolding dc.Mem() in unfolding acc(dc.MemInternal(dc.dataChannelState), 1/2) in @*/ dc.dataStream.GetRegion(), nil
}

// IsActive returns a boolean value indicating the datachannel is actively listening
// and communicating with service
// @ preserves dc != nil ==> dc.Mem()
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
	return /*@ unfolding dc.Mem() in unfolding acc(dc.MemInternal(dc.dataChannelState), 1/2) in @*/ dc.dataStream.IsActive(), nil
}

// GetSeparateOutputPayload returns boolean value indicating separate
// stdout/stderr output for non-interactive session or not
// @ preserves dc != nil ==> dc.Mem()
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
	return /*@ unfolding dc.Mem() in unfolding acc(dc.MemInternal(dc.dataChannelState), _) in @*/ dc.separateOutputPayload, nil
}

// SetSeparateOutputPayload set separateOutputPayload value
// @ preserves dc != nil ==> dc.Mem()
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
	//@ unfold dc.Mem()
	//@ state := dc.dataChannelState
	//@ unfold dc.MemInternal(state)
	dc.separateOutputPayload = separateOutputPayload
	//@ fold dc.MemInternal(state)
	//@ fold dc.Mem()
	return
}

// @ preserves dc != nil ==> dc.Mem()
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
	//@ unfold dc.Mem()
	//@ state := dc.dataChannelState
	//@ unfold acc(dc.MemInternal(state), 1/4)
	dc.dataStream.PrepareToCloseChannel(log /*@, perm(1/8) @*/)
	//@ fold acc(dc.MemInternal(state), 1/4)
	//@ fold dc.Mem()
	return
}

// @ preserves dc != nil ==> dc.Mem()
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
	//@ unfold dc.Mem()
	//@ state := dc.dataChannelState
	//@ unfold acc(dc.MemInternal(state), 1/4)
	err = dc.dataStream.Close(log /*@, perm(1/8) @*/)
	//@ fold acc(dc.MemInternal(state), 1/4)
	//@ fold dc.Mem()
	return
}
