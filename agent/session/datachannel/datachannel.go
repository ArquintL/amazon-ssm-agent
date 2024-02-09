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
	"errors"
	"time"
	//@ "sync"

	logger "github.com/aws/amazon-ssm-agent/agent/log"
	mgsContracts "github.com/aws/amazon-ssm-agent/agent/session/contracts"
	"github.com/aws/amazon-ssm-agent/agent/session/datachannel/cryptolib"
)

// SkipHandshake is used to skip handshake if the plugin decides it is not necessary
// @ requires log != nil
// @ preserves dc.Mem() && acc(log.Mem(), _)
// @ ensures err == nil ==> dc.getState() == HandshakeSkipped
func (dc *dataChannel) SkipHandshake(log logger.T) (err error) {
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
// @ requires log != nil
// @ requires encryptionEnabled == assumeEncryptionEnabledForVerification()
// @ preserves dc.Mem() && acc(log.Mem(), _)
// @ ensures err == nil ==> dc.getState() == IODistributed
func (dc *dataChannel) PerformHandshake(log logger.T,
	kmsKeyId string,
	encryptionEnabled bool,
	sessionTypeRequest mgsContracts.SessionTypeRequest) (err error) {

	if dc.getState() != Initialized {
		err = fmtErrorInvalidState(dc.getState())
		return
	}

	logDebug(log, "PerformHandshake")

	//@ unfold dc.Mem()
	//@ unfold dc.MemInternal(Initialized)

	if encryptionEnabled {
		// if dc.blockCipher, err = newBlockCipher(dc.context, kmsKeyId); err != nil {
		// 	return fmtErrorf("Initializing BlockCipher failed: %s", err)
		// }
		logInfo(log, "Encryption enabled: initializing block cipher")
		// dc.blockCipher = &cryptolib.BlockCipherT{}
	}
	// initializing the block cipher independently of `encryptionEnabled` simplifies reasoning
	dc.blockCipher = &cryptolib.BlockCipherT{}
	// we inhale the permissions for the modeled ghost fields of this block cipher:
	//@ inhale dc.blockCipher.EncKeyTMem() && dc.blockCipher.DecKeyTMem()
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
	if err != nil {
		return err
	}
	if err := dc.sendHandshakeRequest(log, handshakeRequestPayload); err != nil {
		return err
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
	res, err := dc.tryReceiveResponseAlt(responseChan, handshakeTimeout)
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
		return errors.New("Unexpected result from processing handshake response")
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

	//@ dc.ioLock = &sync.Mutex{}
	//@ dc.ioLockDidLocalReceive = false
	//@ dc.ioLockCanRemoteSend = false
	//@ dc.ioLockDidRemoteReceive = false
	//@ dc.ioLockCanLocalSend = false
	//@ fold IoLockInv!<dc, dc.dataStream.GetInstanceId(), dc.dataStream.GetClientId(), dc.agentLTKeyARN!>()
	//@ dc.ioLock.SetInv(IoLockInv!<dc, dc.dataStream.GetInstanceId(), dc.dataStream.GetClientId(), dc.agentLTKeyARN!>)

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
