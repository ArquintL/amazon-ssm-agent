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
	"bytes"
	"crypto/sha512"
	"encoding/base64"
	"encoding/json"
	"errors"
	"fmt"
	"time"

	logger "github.com/aws/amazon-ssm-agent/agent/log"
	mgsContracts "github.com/aws/amazon-ssm-agent/agent/session/contracts"
	"github.com/aws/amazon-ssm-agent/agent/versionutil"
	"github.com/aws/aws-sdk-go/service/kms"
	"golang.org/x/crypto/hkdf"
	//@ abs "github.com/aws/amazon-ssm-agent/agent/iospecs/abs"
	//@ by "github.com/aws/amazon-ssm-agent/agent/iospecs/bytes"
	//@ "github.com/aws/amazon-ssm-agent/agent/iospecs/iospec"
	//@ pl "github.com/aws/amazon-ssm-agent/agent/iospecs/place"
	//@ tm "github.com/aws/amazon-ssm-agent/agent/iospecs/term"
)

// We model is function as receiving the payload with the corresponding term representation from the
// environment because we model in Tamarin that the payload is under full adversarial control.
// Conceptually, we receive an arbitrary payload from the environment and check whether it's equal to
// the tuple of duration and customer message (on the byte-level). Otherwise, we reject the message and
// return an error.
// @ trusted
// @ requires pl.token(t) && iospec.e_InFact(t, rid)
// @ ensures  err == nil ==> pl.token(old(iospec.get_e_InFact_placeDst(t, rid))) &&
// @	payloadT == old(iospec.get_e_InFact_r1(t, rid))
// @ ensures err == nil ==> by.gamma(payloadT) == by.pairB(by.durationB(handshakeDuration), by.msgB(customerMessage))
// @ ensures err != nil ==> err.ErrorMem()
// @ ensures err != nil ==> pl.token(t) && iospec.e_InFact(t, rid) &&
// @ 	iospec.get_e_InFact_placeDst(t, rid) == old(iospec.get_e_InFact_placeDst(t, rid)) &&
// @ 	iospec.get_e_InFact_r1(t, rid) == old(iospec.get_e_InFact_r1(t, rid))
func getHandshakeCompletePayload(handshakeDuration time.Duration, separateOutputPayload, encryptionEnabled bool, clientVersion string /*@, ghost t pl.Place, ghost rid tm.Term @*/) (customerMessage string, err error /*@, ghost payloadT tm.Term @*/) {
	customerMessage = ""
	if separateOutputPayload == true && versionutil.Compare(clientVersion, clientVersionWithoutOutputSeparation, true) <= 0 {
		customerMessage += "Please update session manager plugin version (minimum required version " +
			firstVersionWithOutputSeparationFeature +
			") for fully support of separate StdOut/StdErr output.\r\n"
	}

	if encryptionEnabled {
		customerMessage += "This session is encrypted using AWS KMS."
	}

	return
}

// @ trusted
// @ requires noPerm < p
// @ requires acc(handshakeCompletePayload.Mem(), p)
// @ ensures  acc(handshakeCompletePayload.Mem(), p)
// @ ensures  err == nil ==> bytes.SliceMem(handshakeCompletePayloadBytes)
// @ ensures  err == nil ==> abs.Abs(handshakeCompletePayloadBytes) == handshakeCompletePayload.Abs()
// @ ensures  err != nil ==> err.ErrorMem()
func marshalHandshakeComplete(handshakeCompletePayload *mgsContracts.HandshakeCompletePayload /*@, ghost p perm @*/) (handshakeCompletePayloadBytes []byte, err error) {
	return json.Marshal(handshakeCompletePayload /*@, p/2 @*/)
}

// @ trusted
// @ decreases
// @ pure
// @ requires acc(bytes.SliceMem(a), _) && acc(bytes.SliceMem(b), _)
// @ ensures res == (abs.Abs(a) == abs.Abs(b))
func equal(a, b []byte) (res bool) {
	return bytes.Equal(a, b)
}

// @ trusted
// @ requires noPerm < p
// @ preserves acc(bytes.SliceMem(input), p)
// @ ensures bytes.SliceMem(res) && abs.Abs(res) == by.hashB(abs.Abs(input))
func computeSHA384(input []byte /*@, ghost p perm @*/) (res []byte) {
	hash := sha512.New384()
	hash.Write(input)
	return hash.Sum(nil)
}

// @ trusted
// @ requires noPerm < p
// @ preserves acc(bytes.SliceMem(input), p)
// @ ensures err == nil ==> (bytes.SliceMem(res) &&
// @ 	(isKdf1 ? abs.Abs(res) == by.kdf1B(abs.Abs(input)) : abs.Abs(res) == by.kdf2B(abs.Abs(input))))
// @ ensures err != nil ==> err.ErrorMem()
func computeKdf(input []byte, isKdf1 bool /*@, ghost p perm @*/) (res []byte, err error) {
	hash512 := sha512.New
	hkPRK := hkdf.Extract(hash512, input, nil) //it's pretty complicated what using a salt with HKDF means, we should double check this

	const keySize = 32
	res = make([]byte, keySize)

	var ctx string
	if isKdf1 { //argot:ignore
		ctx = "S"
	} else { //argot:ignore
		ctx = "C"
	}

	bytesRead, err := hkdf.Expand(hash512, hkPRK, []byte(ctx)).Read(res)
	if err != nil { //argot:ignore
		return nil, errHandshake()
	}
	if bytesRead != keySize { //argot:ignore
		return nil, errHandshake()
	}
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
}

// GetClientVersion returns version of the client
// @ requires noPerm < p
// @ preserves acc(dc.Mem(), p)
// @ ensures  err != nil ==> err.ErrorMem()
func (dc *dataChannel) GetClientVersion( /*@ ghost p perm @*/ ) (version string, err error) {
	if dc.getState() == Erroneous {
		err = fmtErrorInvalidState(dc.getState())
		return
	}
	return /*@ unfolding acc(dc.Mem(), p) in unfolding acc(dc.MemInternal(dc.dataChannelState), p/2) in @*/ dc.hs.clientVersion, nil
}

// GetInstanceId returns id of the target
// @ requires noPerm < p
// @ preserves acc(dc.Mem(), p)
// @ ensures  err != nil ==> err.ErrorMem()
func (dc *dataChannel) GetInstanceId( /*@ ghost p perm @*/ ) (instanceId string, err error) {
	if dc.getState() < Initialized {
		err = fmtErrorInvalidState(dc.getState())
		return
	}
	return /*@ unfolding acc(dc.Mem(), p) in unfolding acc(dc.MemInternal(dc.dataChannelState), p/2) in @*/ dc.instanceId, nil
}

// GetRegion returns aws region of the target
// @ requires noPerm < p
// @ preserves acc(dc.Mem(), p)
// @ ensures  err != nil ==> err.ErrorMem()
func (dc *dataChannel) GetRegion( /*@ ghost p perm @*/ ) (region string, err error) {
	if dc.getState() < Initialized {
		err = fmtErrorInvalidState(dc.getState())
		return
	}
	return /*@ unfolding acc(dc.Mem(), p) in unfolding acc(dc.MemInternal(dc.dataChannelState), p/2) in @*/ dc.dataStream.GetRegion(), nil
}

// IsActive returns a boolean value indicating the datachannel is actively listening
// and communicating with service
// @ requires noPerm < p
// @ preserves acc(dc.Mem(), p)
// @ ensures  err != nil ==> err.ErrorMem()
func (dc *dataChannel) IsActive( /*@ ghost p perm @*/ ) (isActive bool, err error) {
	if dc.getState() < Initialized {
		err = fmtErrorInvalidState(dc.getState())
		return
	}
	return /*@ unfolding acc(dc.Mem(), p) in unfolding acc(dc.MemInternal(dc.dataChannelState), p/2) in @*/ dc.dataStream.IsActive(), nil
}

// GetSeparateOutputPayload returns boolean value indicating separate
// stdout/stderr output for non-interactive session or not
// @ requires noPerm < p
// @ preserves acc(dc.Mem(), p)
// @ ensures  err != nil ==> err.ErrorMem()
func (dc *dataChannel) GetSeparateOutputPayload( /*@ ghost p perm @*/ ) (res bool, err error) {
	if dc.getState() == Erroneous {
		err = fmtErrorInvalidState(dc.getState())
		return
	}
	return /*@ unfolding acc(dc.Mem(), _) in unfolding acc(dc.MemInternal(dc.dataChannelState), _) in @*/ dc.separateOutputPayload, nil
}

// SetSeparateOutputPayload set separateOutputPayload value
// @ preserves dc.Mem()
// @ ensures  err != nil ==> err.ErrorMem()
// @ ensures dc.getState() == old(dc.getState())
func (dc *dataChannel) SetSeparateOutputPayload(separateOutputPayload bool) (err error) {
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

// @ requires log != nil
// @ preserves dc.Mem() && acc(log.Mem(), _)
// @ ensures  err != nil ==> err.ErrorMem()
// @ ensures  dc.getState() == old(dc.getState())
func (dc *dataChannel) PrepareToCloseChannel(log logger.T) (err error) {
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

// @ requires log != nil
// @ preserves dc.Mem() && acc(log.Mem(), _)
// @ ensures  err != nil ==> err.ErrorMem()
// @ ensures  dc.getState() == old(dc.getState())
func (dc *dataChannel) Close(log logger.T) (err error) {
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

// @ trusted
// @ requires acc(log.Mem(), _) && noPerm < p
// @ preserves acc(param.Mem(), p)
func logHandshakeRequest(log logger.T, param *mgsContracts.HandshakeRequestPayload /*@, ghost p perm @*/) {
	log.Tracef("Sending HandshakeRequest message with content %v", param)
}

// @ trusted
// @ requires acc(log.Mem(), _) && noPerm < p
// @ preserves acc(param.Mem(), p)
func logHandshakeComplete(log logger.T, param *mgsContracts.HandshakeCompletePayload /*@, ghost p perm @*/) {
	log.Tracef("Sending HandshakeComplete message with content %v", param)
}

// @ trusted
// @ requires acc(log.Mem(), _)
func logDebug(log logger.T, str string) {
	log.Debug(str)
}

// @ trusted
// @ requires acc(log.Mem(), _)
func logDebugHex(log logger.T, prefix string, param string) {
	log.Debugf(prefix+": %x", param)
}

// @ requires noPerm < p
// @ requires acc(log.Mem(), _) && acc(bytes.SliceMem(param), p)
// @ ensures  acc(bytes.SliceMem(param), p)
func logDebugBytes(log logger.T, prefix string, param []byte /*@, ghost p perm @*/) {
	strParam := base64.RawStdEncoding.EncodeToString(param /*@, perm(p/2) @*/)
	logDebugHex(log, prefix, strParam)
}

// @ trusted
// @ requires acc(log.Mem(), _)
func logInfo(log logger.T, str string) {
	log.Info(str)
}

// @ trusted
// @ requires acc(log.Mem(), _)
func logInfoString(log logger.T, prefix string, param string) {
	log.Infof(prefix+": %s", param)
}

// @ trusted
// @ requires acc(log.Mem(), _)
func logUnknownActionType(log logger.T, param mgsContracts.ActionType) {
	log.Warnf("Unknown handshake client action found, %s", param)
}

// @ trusted
// @ requires acc(log.Mem(), _) && noPerm < p
// @ preserves acc(param.ErrorMem(), p)
func logError(log logger.T, param error /*@, ghost p perm @*/) {
	log.Error(param)
}

// @ trusted
// @ requires acc(log.Mem(), _) && noPerm < p
// @ preserves acc(param.ErrorMem(), p)
func logErrorf(log logger.T, prefix string, param error /*@, ghost p perm @*/) {
	log.Errorf(prefix+": %v", param)
}

// @ trusted
// @ requires noPerm < p && acc(param.ErrorMem(), p)
// @ ensures err != nil && acc(err.ErrorMem(), p)
func fmtErrorf(prefix string, param error /*@, ghost p perm @*/) (err error) {
	return fmt.Errorf(prefix+": %v", param)
}

// @ trusted
// @ ensures err != nil && err.ErrorMem()
func fmtError(str string) (err error) {
	return fmt.Errorf(str)
}

// @ trusted
// @ ensures err != nil && err.ErrorMem()
func fmtErrorInvalidState(param DataChannelState) (err error) {
	return fmt.Errorf("DataChannel is in an invalid state %d", param)
}

// @ trusted
// @ ensures err != nil && err.ErrorMem()
func fmtErrorfPayloadType(prefix string, param mgsContracts.PayloadType) (err error) {
	return fmt.Errorf(prefix+": %d", param)
}

// @ trusted
// @ ensures err != nil && err.ErrorMem()
func fmtErrorfInt64(prefix string, param1 int64) (err error) {
	return fmt.Errorf(prefix+": %d", param1)
}

// @ trusted
// @ requires noPerm < p && acc(param2.ErrorMem(), p)
// @ ensures err != nil && acc(err.ErrorMem(), p)
func fmtErrorfInt64Err(prefix string, param1 int64, param2 error /*@, ghost p perm @*/) (err error) {
	return fmt.Errorf(prefix+": %d, err: %v", param1, param2)
}

// @ trusted
// @ ensures err != nil && err.ErrorMem()
func fmtErrorActionFailure(param1 mgsContracts.ActionType, param2 mgsContracts.ActionStatus, param3 string) (err error) {
	return fmt.Errorf("%s failed on client with status %v error: %s", param1, param2, param3)
}

// @ trusted
// @ requires noPerm < p && acc(bytes.SliceMem(param1), p) && acc(bytes.SliceMem(param2), p)
// @ ensures err != nil && acc(err.ErrorMem(), p)
func fmtErrorSessionMismatch(param1 []byte, param2 []byte /*@, ghost p perm @*/) (err error) {
	return fmt.Errorf("session ID mismatch: session ID %s does not match client session ID %s", param1, param2)
}

// @ trusted
// @ requires noPerm < p && acc(param.Mem(), p)
// @ ensures err != nil && acc(err.ErrorMem(), p)
func fmtErrorfMetadata(prefix string, param *kms.KeyMetadata /*@, ghost p perm @*/) (err error) {
	return fmt.Errorf(prefix+": %+v", param)
}

// @ trusted
// @ requires noPerm < p && acc(param1.Mem(), p) && acc(param2.ErrorMem(), p)
// @ ensures err != nil && acc(err.ErrorMem(), p)
func fmtErrorSerializeHandshakeComplete(param1 *mgsContracts.HandshakeCompletePayload, param2 error /*@, ghost p perm @*/) (err error) {
	return fmt.Errorf("Could not serialize HandshakeComplete message %v, err: %s", param1, param2)
}

// @ trusted
// @ decreases
// @ ensures err != nil && err.ErrorMem()
func errHandshake() (err error) {
	return errors.New("failed to execute handshake operation")
}
