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
	"bytes"
	"crypto/elliptic"
	cryptoRand "crypto/rand"
	"crypto/rsa"
	"crypto/sha512"
	"encoding/base64"
	"encoding/json"
	"errors"
	"fmt"
	"time"

	logger "github.com/aws/amazon-ssm-agent/agent/log"
	mgsContracts "github.com/aws/amazon-ssm-agent/agent/session/contracts"
	"github.com/aws/amazon-ssm-agent/agent/session/crypto"
	"github.com/aws/amazon-ssm-agent/agent/session/datachannel/iosanitization"
	"github.com/aws/amazon-ssm-agent/agent/session/datastream"
	"github.com/aws/amazon-ssm-agent/agent/versionutil"
	"github.com/aws/aws-sdk-go/service/kms"
	"golang.org/x/crypto/hkdf"
	//@ abs "github.com/aws/amazon-ssm-agent/agent/iospecs/abs"
	//@ by "github.com/aws/amazon-ssm-agent/agent/iospecs/bytes"
	//@ "github.com/aws/amazon-ssm-agent/agent/iospecs/iospec"
	//@ pl "github.com/aws/amazon-ssm-agent/agent/iospecs/place"
	//@ pub "github.com/aws/amazon-ssm-agent/agent/iospecs/pub"
	//@ tm "github.com/aws/amazon-ssm-agent/agent/iospecs/term"
)

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
func getInitialValues(dataStream *datastream.DataStream, kmsService *crypto.KMSService /*@, ghost t pl.Place, ghost rid tm.Term @*/) (agentId string, clientId string, logReaderId string, agentLTKeyARN string, logLTPk *rsa.PublicKey, err error) {
	metadata, err := kmsService.CreateKeyAssymetric()
	if err != nil {
		err = fmtErrorf("failed to create agent LTK", err /*@, perm(1/1) @*/)
		return "", "", "", "", nil, err
	}

	agentId = dataStream.GetInstanceId()
	clientId = dataStream.GetClientId()
	logReaderId = dataStream.GetLogReaderId()

	//@ unfold metadata.Mem()
	if metadata.Arn == nil {
		err = fmtErrorfMetadata("asymmetric key ARN is nil, metadata", metadata /*@, perm(1/2) @*/)
		return "", "", "", "", nil, err
	}
	agentLTKeyARN = *metadata.Arn
	//@ cryptoRand.GetReaderMem()

	// Note that we create an RSA key pair here but throw away the secret key.
	// In a realistic deployment, the log reader's public key would be an input parameter.
	// However, for now, we generate the public key here instead of taking it as an input.
	sk, err := rsa.GenerateKey(cryptoRand.Reader, 4096 /*@, perm(1/2) @*/)
	if err != nil {
		err = fmtErrorf("failed to create log secret key", err /*@, perm(1/1) @*/)
		return "", "", "", "", nil, err
	}
	//@ unfold sk.Mem()
	logLTPk = &sk.PublicKey

	return
}

// @ trusted
// @ requires noPerm < p
// @ requires acc(handshakeRequestPayload.Mem(), p)
// @ requires handshakeRequestPayload.ContainsSecureSessionAction(secActionB)
// @ ensures  acc(handshakeRequestPayload.Mem(), p)
// @ ensures  handshakeRequestPayload.ContainsSecureSessionAction(secActionB)
// @ ensures  err == nil ==> bytes.SliceMem(handshakeRequestPayloadBytes)
// @ ensures  err == nil ==> abs.Abs(handshakeRequestPayloadBytes) == secActionB
// @ ensures  err != nil ==> err.ErrorMem()
func marshalHandshakeRequest(handshakeRequestPayload *mgsContracts.HandshakeRequestPayload /*@, ghost p perm, ghost secActionB by.Bytes @*/) (handshakeRequestPayloadBytes []byte, err error) {
	return json.Marshal(handshakeRequestPayload /*@, p/2 @*/)
}

// @ trusted
// @ requires pl.token(t0) && iospec.e_FrFact(t0, rid)
// @ ensures  err == nil ==> bytes.SliceMem(priv)
// @ ensures  err == nil ==> pl.token(t1) && t1 == old(iospec.get_e_FrFact_placeDst(t0, rid))
// @ ensures  err == nil ==> abs.Abs(priv) == by.gamma(old(iospec.get_e_FrFact_r1(t0, rid)))
// @ ensures  err == nil ==> by.msgB(encodedPk) == by.expB(by.generatorB(), abs.Abs(priv))
// @ ensures  err != nil ==> err.ErrorMem()
// @ ensures  err != nil ==> t1 == t0 && pl.token(t0) && iospec.e_FrFact(t0, rid) &&
// @ 	iospec.get_e_FrFact_placeDst(t0, rid) == old(iospec.get_e_FrFact_placeDst(t0, rid)) &&
// @    iospec.get_e_FrFact_r1(t0, rid) == old(iospec.get_e_FrFact_r1(t0, rid))
func generateAndEncodeEllipticKey( /*@ ghost t0 pl.Place, ghost rid tm.Term @*/ ) (priv []byte, encodedPk string, err error /*@, ghost t1 pl.Place @*/) {
	//@ cryptoRand.GetReaderMem()
	priv, x, y, err /*@, t1 @*/ := elliptic.GenerateKey(elliptic.P384(), cryptoRand.Reader /*@, t0, rid @*/)
	if err != nil { //argot:ignore diodon-agent-io-independence
		return nil, "", errHandshake() /*@, t0 @*/ // generic error
	}

	// Base64 encode the public part and put it in the message
	agentShare := elliptic.MarshalCompressed(elliptic.P384(), x, y /*@, perm(1/2) @*/) //argot:ignore diodon-agent-io-independence
	encodedPk = base64.StdEncoding.EncodeToString(agentShare /*@, perm(1/2) @*/)
	return
}

// @ trusted
// @ ensures err == nil ==> bytes.SliceMem(signPayloadBytes)
// @ ensures err == nil ==> abs.Abs(signPayloadBytes) == by.tuple3B(by.msgB(compressedPublic), by.msgB(logReaderId), by.msgB(clientId))
// @ ensures err != nil ==> err.ErrorMem()
func getSignAgentSharePayloadBytes(compressedPublic string, clientId string, logReaderId string) (signPayloadBytes []byte, err error) {
	signPayload := &mgsContracts.SignAgentSharePayload{
		AgentShare:  compressedPublic,
		ClientId:    clientId,
		LogReaderId: logReaderId,
	}

	//@ fold signPayload.Mem()
	return json.Marshal(signPayload /*@, perm(1/2) @*/)
}

// @ trusted
// @ requires noPerm < p
// @ preserves acc(bytes.SliceMem(payload), p)
// @ ensures  handshakeResponse.Mem()
// @ ensures  err == nil && abs.Abs(payload) == handshakeResponse.Abs()
// @ ensures  err != nil ==> err.ErrorMem()
func unmarshalHandshakeResponse(payload []byte /*@, p perm @*/) (handshakeResponse *mgsContracts.HandshakeResponsePayload, err error) {
	handshakeResponse = &mgsContracts.HandshakeResponsePayload{}
	//@ fold handshakeResponse.Mem()
	err = json.Unmarshal(payload, handshakeResponse /*@, p/2 @*/)
	return
}

// @ trusted
// @ requires noPerm < p
// @ preserves acc(bytes.SliceMem(payload), p)
// @ ensures  secureSessionResponse.Mem()
// @ ensures  err == nil && abs.Abs(payload) == secureSessionResponse.Abs()
// @ ensures  err != nil ==> err.ErrorMem()
func unmarshalSecureSessionResponse(payload []byte /*@, p perm @*/) (secureSessionResponse *mgsContracts.SecureSessionResponse, err error) {
	secureSessionResponse = &mgsContracts.SecureSessionResponse{}
	//@ fold secureSessionResponse.Mem()
	err = json.Unmarshal(payload, secureSessionResponse /*@, p/2 @*/)
	return
}

// @ trusted
// @ requires noPerm < p && p <= writePerm
// @ preserves acc(bytes.SliceMem(agentSecret), p)
// @ ensures err == nil ==> bytes.SliceMem(sharedSecret)
// the following postcondition expresses that `IsOnCurve` guarantees that `clientShare` is a valid
// DH pubic key. Instead of existentially quantifying over the corresponding private key, we assume
// `privB` is the corresponding witness
// @ ensures err == nil ==> by.msgB(clientShare) == by.expB(by.generatorB(), privB)
// @ ensures err == nil ==> abs.Abs(sharedSecret) == by.expB(by.expB(by.generatorB(), privB), abs.Abs(agentSecret))
// @ ensures err != nil ==> err.ErrorMem()
func unmarshalAndCheckClientShare(clientShare string, agentSecret []byte /*@, p perm @*/) (sharedSecret []byte, err error /*@, privB by.Bytes @*/) {
	var clientShareBytes []byte
	clientShareBytes, err = base64.StdEncoding.DecodeString(clientShare)
	if err != nil {
		err = fmtError("failed to decode server share")
		return
	}

	x, y := elliptic.UnmarshalCompressed(elliptic.P384(), clientShareBytes /*@, perm(1/2) @*/)

	// check that the client share is on the curve
	if !elliptic.P384().IsOnCurve(x, y /*@, perm(1/2) @*/) {
		err = fmtError("client share is not on the curve")
		return
	}

	ss, _ := elliptic.P384().ScalarMult(x, y, agentSecret /*@, p/2 @*/) // TODO: Double check it's fine to just use x
	sharedSecret = ss.Bytes( /*@ perm(1/2) @*/ )
	return
}

// @ trusted
// @ ensures err == nil ==> bytes.SliceMem(clientSignPayload)
// @ ensures err == nil ==> abs.Abs(clientSignPayload) == by.pairB(by.msgB(clientShare), by.msgB(agentId))
// @ ensures err != nil ==> err.ErrorMem()
func getVerifyPayloadBytes(clientShare string, agentId string) (clientSignPayload []byte, err error) {
	payload := &mgsContracts.SignClientSharePayload{
		ClientShare: clientShare,
		AgentId:     agentId,
	}

	//@ fold payload.Mem()
	return json.Marshal(payload /*@, perm(1/2) @*/)
}

// @ trusted
// @ requires noPerm < p
// @ preserves acc(bytes.SliceMem(agentReadKey), p) && acc(bytes.SliceMem(agentWriteKey), p)
// @ ensures  err == nil ==> bytes.SliceMem(sessionKeysPayload) && abs.Abs(sessionKeysPayload) == by.pairB(abs.Abs(agentWriteKey), abs.Abs(agentReadKey))
// @ ensures  err != nil ==> err.ErrorMem()
func getSessionKeysPayload(agentWriteKey, agentReadKey []byte /*@, ghost p perm @*/) (sessionKeysPayload []byte, err error) {
	encodedAgentReadKey := base64.RawStdEncoding.EncodeToString(agentReadKey /*@, p/2 @*/)
	encodedAgentWriteKey := base64.RawStdEncoding.EncodeToString(agentWriteKey /*@, p/2 @*/)

	sessionKeys := &mgsContracts.SessionKeys{
		AgentWriteKey: encodedAgentWriteKey,
		AgentReadKey:  encodedAgentReadKey,
	}
	//@ fold sessionKeys.Mem()
	return json.Marshal(sessionKeys /*@, perm(1/2) @*/)
}

// @ trusted
// @ requires noPerm < p
// @ preserves acc(bytes.SliceMem(payload), p) && acc(pk.Mem(), p)
// @ ensures  err == nil ==> by.msgB(encodedCiphertext) == by.aencB(abs.Abs(payload), pk.Abs())
// @ ensures  err != nil ==> err.ErrorMem()
func encryptAndEncode(payload []byte, pk *rsa.PublicKey /*@, ghost p perm @*/) (encodedCiphertext string, err error) {
	//@ cryptoRand.GetReaderMem()
	ciphertext, err := rsa.EncryptPKCS1v15(cryptoRand.Reader, pk, payload /*@, p > writePerm ? perm(1/1) : p/2 @*/)
	if err != nil {
		err = errHandshake()
		return
	}
	encodedCiphertext = base64.StdEncoding.EncodeToString(ciphertext /*@, perm(1/2) @*/)
	return
}

// @ trusted
// @ ensures err == nil ==> bytes.SliceMem(signPayloadBytes)
// @ ensures err == nil ==> abs.Abs(signPayloadBytes) == by.pairB(by.msgB(encryptedSessionKeys), by.msgB(clientId))
// @ ensures err != nil ==> err.ErrorMem()
func getSignSessionKeysPayloadBytes(encryptedSessionKeys string, clientId string) (signPayloadBytes []byte, err error) {
	signPayload := &mgsContracts.SignSessionKeysPayload{
		EncryptedSessionKeys: encryptedSessionKeys,
		ClientId:             clientId,
	}

	//@ fold signPayload.Mem()
	return json.Marshal(signPayload /*@, perm(1/2) @*/)
}

// @ trusted
// @ requires noPerm < p
// @ requires kmsService.Mem() && acc(bytes.SliceMem(message), p)
// @ requires m == tm.pair(tm.pubTerm(pub.const_SignRequest_pub()), tm.pair(tm.pubTerm(pub.pub_msg(keyId)), messageT))
// @ requires pl.token(t) && iospec.e_Out_KMS(t, rid, agentId, kmsId, rid, m) && by.gamma(messageT) == abs.Abs(message)
// @ requires let t1 := iospec.get_e_Out_KMS_placeDst(t, rid, agentId, kmsId, rid, m) in (
// @     iospec.e_In_KMS(t1, rid))
// @ ensures  kmsService.Mem() && acc(bytes.SliceMem(message), p)
// @ ensures  err == nil ==> by.gamma(signatureT) == by.msgB(signature)
// @ ensures  err != nil ==> err.ErrorMem()
// @ ensures  err == nil ==> let t1 := old(iospec.get_e_Out_KMS_placeDst(t, rid, agentId, kmsId, rid, m)) in (
// @     pl.token(old(iospec.get_e_In_KMS_placeDst(t1, rid))) &&
// @     kmsId == old(iospec.get_e_In_KMS_r1(t1, rid)) &&
// @     agentId == old(iospec.get_e_In_KMS_r2(t1, rid)) &&
// @     rid == old(iospec.get_e_In_KMS_r3(t1, rid)) &&
// @     tm.pair(tm.pubTerm(pub.const_SignResponse_pub()), signatureT) == old(iospec.get_e_In_KMS_r4(t1, rid)))
func signAndEncode(kmsService *crypto.KMSService, keyId string, message []byte /*@, ghost p perm, ghost t pl.Place, ghost rid tm.Term, ghost agentId tm.Term, ghost kmsId tm.Term, ghost messageT tm.Term, ghost m tm.Term @*/) (signature string, err error /*@, ghost signatureT tm.Term @*/) {
	var sig []byte
	sig, err /*@, signatureT @*/ = iosanitization.KMSSign(kmsService, keyId, message /*@, p, t, rid, agentId, kmsId, messageT, m @*/)
	if err != nil {
		err = errHandshake()
		return
	}
	signature = base64.StdEncoding.EncodeToString(sig /*@, perm(1/2)@*/)
	return
}

// @ trusted
// @ ensures  err == nil ==> by.msgB(encryptedSessionKeysPayload) == by.tuple5B(by.msgB(encodedEncryptedSessionKeys), by.msgB(encodedSigSessionKeys), by.msgB(agentId), by.msgB(agentLTKeyARN), by.msgB(clientId))
// @ ensures  err != nil ==> err.ErrorMem()
func getEncryptedSessionKeysPayload(encodedEncryptedSessionKeys, encodedSigSessionKeys, agentId, agentLTKeyARN, clientId string) (encryptedSessionKeysPayload string, err error) {
	payload := &mgsContracts.EncryptedSessionKeysPayload{
		EncryptedSessionKeys: encodedEncryptedSessionKeys,
		Signature:            encodedSigSessionKeys,
		AgentId:              agentId,
		AgentLTKeyARN:        agentLTKeyARN,
		ClientId:             clientId,
	}
	//@ fold payload.Mem()
	encryptedSessionKeysPayloadBytes, err := json.Marshal(payload /*@, perm(1/2) @*/)
	if err != nil {
		return
	}

	encryptedSessionKeysPayload = base64.StdEncoding.EncodeToString(encryptedSessionKeysPayloadBytes /*@, perm(1/2) @*/)
	return
}

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
	if isKdf1 {
		ctx = "S"
	} else {
		ctx = "C"
	}

	bytesRead, err := hkdf.Expand(hash512, hkPRK, []byte(ctx)).Read(res)
	if err != nil {
		return nil, errHandshake()
	}
	if bytesRead != keySize {
		return nil, errHandshake()
	}
	return
}

// we treat this function as being part of the APPLICATION because it does not
// depend on any secrets negotiated during the handshake. Hence, we mark it as
// `trusted` such that Gobra does not attempt to verify it.
// In particular, only the channel id and session status is sent.
// @ trusted
// @ preserves dc != nil ==> dc.Mem()
// @ preserves log != nil ==> acc(log.Mem(), _)
// @ ensures  err != nil ==> err.ErrorMem()
func (dc *dataChannel) SendAgentSessionStateMessage(log logger.T, sessionStatus mgsContracts.SessionStatus) (err error) {
	agentSessionStateContent := &mgsContracts.AgentSessionStateContent{
		SchemaVersion: schemaVersion,
		SessionState:  string(sessionStatus),
		SessionId:     dc.dataStream.GetChannelId(),
	}

	var agentSessionStateContentBytes []byte
	if agentSessionStateContentBytes, err = json.Marshal(agentSessionStateContent); err != nil {
		logErrorf(log, "Cannot serialize AgentSessionState message err", err /*@, perm(1/1) @*/)
		return err
	}

	sessionStatusStr := string(sessionStatus)
	//@ fold sessionStatusStr.Mem()
	logDebug(log, "Send AgentSessionState message with session status"+sessionStatusStr)
	if err := dc.dataStream.SendAgentMessage(log, mgsContracts.AgentSessionState, agentSessionStateContentBytes); err != nil {
		return err
	}
	return nil
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
func fmtErrorNil() (err error) {
	return errors.New("Nil parameter passed to DataChannel")
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
