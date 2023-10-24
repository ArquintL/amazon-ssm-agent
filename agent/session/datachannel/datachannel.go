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
	"crypto/aes"
	"crypto/cipher"
	"crypto/elliptic"
	cryptoRand "crypto/rand"
	"crypto/rsa"
	"crypto/sha512"
	"encoding/base64"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	stdLog "log"
	"time"

	"github.com/aws/amazon-ssm-agent/agent/context"
	"github.com/aws/amazon-ssm-agent/agent/log"
	mgsContracts "github.com/aws/amazon-ssm-agent/agent/session/contracts"
	"github.com/aws/amazon-ssm-agent/agent/session/crypto"
	"github.com/aws/amazon-ssm-agent/agent/session/datastream"
	"github.com/aws/amazon-ssm-agent/agent/task"
	"github.com/aws/amazon-ssm-agent/agent/version"
	"github.com/aws/amazon-ssm-agent/agent/versionutil"
	"golang.org/x/crypto/hkdf"
)

const (
	schemaVersion  = 1
	sequenceNumber = 0
	messageFlags   = 3
	// Timeout period before a handshake operation expires on the agent.
	handshakeTimeout                        = 1500 * time.Second
	clientVersionWithoutOutputSeparation    = "1.2.295"
	firstVersionWithOutputSeparationFeature = "1.2.312.0"
	channelStatusTimeout                    = 150 * time.Millisecond
)

type IDataChannel interface {
	Initialize(dataStream *datastream.DataStream, inputStreamMessageHandler InputStreamMessageHandler)
	// Initialize(context context.T, mgsService service.Service, sessionId string, clientId string, instanceId string, role string, cancelFlag task.CancelFlag, inputStreamMessageHandler InputStreamMessageHandler)
	// SetWebSocket(context context.T, mgsService service.Service, sessionId string, clientId string, onMessageHandler func(input []byte)) error
	// Open(log log.T) error
	Close(log log.T) error
	// Reconnect(log log.T) error
	// SendMessage(log log.T, input []byte, inputType int) error
	SendStreamDataMessage(log log.T, dataType mgsContracts.PayloadType, inputData []byte) error
	// ResendStreamDataMessageScheduler(log log.T) error
	// ProcessAcknowledgedMessage(log log.T, acknowledgeMessageContent mgsContracts.AcknowledgeContent)
	// SendAcknowledgeMessage(log log.T, agentMessage mgsContracts.AgentMessage) error
	SendAgentSessionStateMessage(log log.T, sessionStatus mgsContracts.SessionStatus) error
	// AddDataToOutgoingMessageBuffer(streamMessage datastream.StreamingMessage)
	// RemoveDataFromOutgoingMessageBuffer(streamMessageElement *list.Element)
	// AddDataToIncomingMessageBuffer(streamMessage datastream.StreamingMessage)
	// RemoveDataFromIncomingMessageBuffer(sequenceNumber int64)
	SkipHandshake(log log.T)
	PerformHandshake(log log.T, kmsKeyId string, encryptionEnabled bool, sessionTypeRequest mgsContracts.SessionTypeRequest) (err error)
	GetClientVersion() string
	GetInstanceId() string
	GetRegion() string
	IsActive() bool
	PrepareToCloseChannel(log log.T)
	// GetSeparateOutputPayload() bool
	SetSeparateOutputPayload(separateOutputPayload bool)
}

// DataChannel used for session communication between the message gateway service and the agent.
type DataChannel struct {
	//dataStream handles low-level communication incl. retransmitting and acknowledging messages
	dataStream *datastream.DataStream
	//inputStreamMessageHandler is responsible for handling plugin specific input_stream_data message
	inputStreamMessageHandler func(log log.T, streamDataMessage mgsContracts.AgentMessage) error
	//handshake captures handshake state and error
	handshake Handshake
	//blockCipher stores encrytion keys and provides interface for encryption/decryption functions
	blockCipher crypto.IBlockCipher
	// Indicates whether encryption was enabled
	encryptionEnabled     bool
	separateOutputPayload bool
	state                 AgentHandshakeState
	// agentLTKeyARN is the ARN for the KMS long-term-key used to sign and verify the handshake
	agentLTKeyARN string
	logReaderId   string
	logLTPk       *rsa.PublicKey
	// logLTKeyARN is the logReaderId's ARN for the long-term public key to decrypt session keys
	// logLTKeyARN            string
}

// AgentHandshakeState represents the state of the handshake.
type AgentHandshakeState struct {
	// kmsService is the KMS service used to sign and verify the handshake keyshare
	kmsService    *crypto.KMSService
	agentSecret   []byte
	sharedSecret  []byte
	sessionID     []byte
	agentWriteKey []byte
	agentReadKey  []byte
}

type InputStreamMessageHandler func(log log.T, streamDataMessage mgsContracts.AgentMessage) error

type MessageReceptionChannelStatus struct {
	status MessageReceptionStatus
	// dataChannel *DataChannel
}

type MessageReceptionStatus int

const (
	ReceiveHandshakeRespone    MessageReceptionStatus = 1
	ReceiveEncryptionChallenge MessageReceptionStatus = 2
	ReceiveOtherResponse       MessageReceptionStatus = 3
)

// type MessageReceptionChannelStatus struct{}

type Handshake struct {
	// Version of the client
	clientVersion string
	// Channel used to signal that a message is to be expected
	startReceivingChan chan MessageReceptionChannelStatus
	// Channel used to signal that a message has been received and successfully processed
	// receptionConfirmedChan chan MessageReceptionChannelStatus
	// Channel used to signal when handshake response is received
	responseChan chan bool
	// Random byte string used to verify encryption
	encryptionChallenge []byte
	// This indicates encryption was validated using encryption challenge exchange
	encryptionConfirmedChan chan bool
	error                   error
	// Indicates handshake is complete (Handshake Complete message sent to client)
	complete bool
	// Indiciates if handshake has been skipped
	skipped            bool
	handshakeStartTime time.Time
	handshakeEndTime   time.Time
}

// NewDataChannel constructs datachannel objects.
func NewDataChannel(context context.T,
	channelId string,
	clientId string,
	inputStreamMessageHandler InputStreamMessageHandler,
	cancelFlag task.CancelFlag) (*DataChannel, error) {

	// log.Debug("HANDSHAKE SLEEPING")
	// time.Sleep(10 * time.Second)

	dataChannel := &DataChannel{}
	dataStream, err := datastream.NewDataStream(context,
		channelId,
		clientId,
		dataChannel.processStreamDataMessage,
		cancelFlag)
	if err != nil {
		return nil, fmt.Errorf("failed to create data stream with error: %s", err)
	}

	dataChannel.Initialize(dataStream, inputStreamMessageHandler)

	return dataChannel, nil
}

// Initialize populates datachannel object.
func (dataChannel *DataChannel) Initialize(dataStream *datastream.DataStream,
	inputStreamMessageHandler InputStreamMessageHandler) {

	dataChannel.dataStream = dataStream
	dataChannel.inputStreamMessageHandler = inputStreamMessageHandler
	dataChannel.handshake = Handshake{
		startReceivingChan: make(chan MessageReceptionChannelStatus),
		// receptionConfirmedChan:  make(chan MessageReceptionChannelStatus),
		responseChan:            make(chan bool),
		encryptionConfirmedChan: make(chan bool),
		error:                   nil,
		complete:                false,
		skipped:                 false,
		handshakeEndTime:        time.Now(),
		handshakeStartTime:      time.Now(),
	}
}

// SendStreamDataMessage sends a data message in a form of AgentMessage for streaming.
func (dataChannel *DataChannel) SendStreamDataMessage(log log.T, payloadType mgsContracts.PayloadType, inputData []byte) (err error) {
	if len(inputData) == 0 {
		log.Debugf("Ignoring empty stream data payload. PayloadType: %d", payloadType)
		return nil
	}

	// If encryption has been enabled, encrypt the payload
	if dataChannel.encryptionEnabled && (payloadType == mgsContracts.Output || payloadType == mgsContracts.StdErr || payloadType == mgsContracts.ExitCode || payloadType == mgsContracts.HandshakeComplete) {
		if inputData, err = dataChannel.blockCipher.EncryptWithAESGCM(inputData); err != nil {
			return fmt.Errorf("error encrypting stream data message sequence %d, err: %v", dataChannel.dataStream.GetStreamDataSequenceNumber(), err)
		}
	}

	dataChannel.dataStream.Send(log, payloadType, inputData)
	return nil
}

// TODO: treat this function as trusted / unrelated to the security protocol because it
// does not involve any cryptography. We might have to model in Tamarin that `GetChannelId()`
// can savely be sent to the network.
// SendAgentSessionStateMessage sends agent session state to MGS
func (dataChannel *DataChannel) SendAgentSessionStateMessage(log log.T, sessionStatus mgsContracts.SessionStatus) error {
	agentSessionStateContent := &mgsContracts.AgentSessionStateContent{
		SchemaVersion: schemaVersion,
		SessionState:  string(sessionStatus),
		SessionId:     dataChannel.dataStream.GetChannelId(),
	}

	var agentSessionStateContentBytes []byte
	var err error
	if agentSessionStateContentBytes, err = json.Marshal(agentSessionStateContent); err != nil {
		log.Errorf("Cannot serialize AgentSessionState message err: %v", err)
		return err
	}

	log.Debugf("Send %s message with session status %s", mgsContracts.AgentSessionState, string(sessionStatus))
	if err := dataChannel.dataStream.SendAgentMessage(log, mgsContracts.AgentSessionState, agentSessionStateContentBytes); err != nil {
		return err
	}
	return nil
}

func tryReceive(channel chan MessageReceptionChannelStatus, timeout time.Duration) (res MessageReceptionChannelStatus, err error) {
	select {
	case res = <-channel:
	case <-time.After(timeout):
		err = fmt.Errorf("Timeout occurred waiting for receiving a message on a channel")
	}
	return
}

// processStreamDataMessage gets called for all messages of type OutputStreamDataMessage
func (dataChannel *DataChannel) processStreamDataMessage(log log.T, streamDataMessage mgsContracts.AgentMessage) (err error) {

	channelStatus, err := tryReceive(dataChannel.handshake.startReceivingChan, channelStatusTimeout)
	if err != nil {
		log.Info("Timeout while receiving channel status")
		return err
	}

	switch MessageReceptionStatus(channelStatus.status) {
	case ReceiveHandshakeRespone:
		switch mgsContracts.PayloadType(streamDataMessage.PayloadType) {
		case mgsContracts.HandshakeResponse:
			{
				// PayloadType is HandshakeResponse so we call our own handler instead of the plugin handler
				if err = dataChannel.handleHandshakeResponse(log, streamDataMessage); err != nil {
					return fmt.Errorf("processing of HandshakeResponse message failed, %v", err)
				}
			}
		default:
			return fmt.Errorf("received message with unexpected payload type")
		}
	case ReceiveEncryptionChallenge:
		switch mgsContracts.PayloadType(streamDataMessage.PayloadType) {
		case mgsContracts.EncChallengeResponse:
			{
				// PayloadType is HandshakeResponse so we call our own handler instead of the plugin handler
				if err = dataChannel.handleEncryptionChallengeResponse(log, streamDataMessage); err != nil {
					return fmt.Errorf("processing of EncryptionChallengeReponse message failed, %v", err)
				}
			}
		default:
			return fmt.Errorf("received message with unexpected payload type")
		}
	case ReceiveOtherResponse:

		if dataChannel.encryptionEnabled && streamDataMessage.PayloadType == uint32(mgsContracts.Output) {
			if streamDataMessage.Payload, err = dataChannel.blockCipher.DecryptWithAESGCM(streamDataMessage.Payload); err != nil {
				// send a message to the channel to prepare for next message reception:
				dataChannel.handshake.startReceivingChan <- MessageReceptionChannelStatus{
					status: ReceiveOtherResponse,
				}
				return fmt.Errorf("Error decrypting stream data message sequence %d, err: %v", streamDataMessage.SequenceNumber, err)
			}
		}

		// Ignore stream data message if handshake is neither skipped nor completed
		if !dataChannel.handshake.skipped && !dataChannel.handshake.complete {
			log.Tracef("Handshake still in progress, ignore stream data message sequence %d", streamDataMessage.SequenceNumber)
			// this case should provably not occur as status `ReceiveOtherResponse`
			// is supposed to be sent on the `startReceivingChan` channel AFTER the
			// handshake has completed.
			// send a message to the channel to prepare for next message reception:
			dataChannel.handshake.startReceivingChan <- MessageReceptionChannelStatus{
				status: ReceiveOtherResponse,
			}
			return nil
		}

		if err = dataChannel.inputStreamMessageHandler(log, streamDataMessage); err != nil {
			dataChannel.handshake.startReceivingChan <- MessageReceptionChannelStatus{
				status: ReceiveOtherResponse,
			}
			return err
		}
		dataChannel.handshake.startReceivingChan <- MessageReceptionChannelStatus{
			status: ReceiveOtherResponse,
		}
	}

	return nil
}

// handleHandshakeResponse is the handler for payload type HandshakeResponse
func (dataChannel *DataChannel) handleHandshakeResponse(log log.T, streamDataMessage mgsContracts.AgentMessage) error {
	log.Debug("Received Handshake Response.")
	var handshakeResponse mgsContracts.HandshakeResponsePayload
	if err := json.Unmarshal(streamDataMessage.Payload, &handshakeResponse); err != nil {
		return fmt.Errorf("Unmarshalling of HandshakeResponse message failed, %s", err)
	}

	for _, action := range handshakeResponse.ProcessedClientActions {
		var err error
		if action.ActionStatus != mgsContracts.Success {
			err = fmt.Errorf("%s failed on client with status %v error: %s",
				action.ActionType, action.ActionStatus, action.Error)
		} else {
			switch action.ActionType {
			case mgsContracts.SecureSession:
				var resp mgsContracts.SecureSessionResponse
				if err = json.Unmarshal(action.ActionResult, &resp); err != nil {
					err = fmt.Errorf("failed to unmarshal action to SecureSessionResponse: %v", err)
					break
				}

				// verify client signature
				sig, err := base64.StdEncoding.DecodeString(resp.Signature)
				if err != nil {
					panic(fmt.Errorf("failed to decode signature"))
				}

				clientSignPayload := mgsContracts.SignClientSharePayload{
					ClientShare: resp.ClientShare,
					AgentId:     dataChannel.dataStream.GetInstanceId(),
				}

				clientSignPayloadBytes, err := json.Marshal(clientSignPayload)
				if err != nil {
					err := fmt.Errorf("failed to encode client sign payload: %v", err)
					log.Error(err)
					panic(err)
				}

				ok, err := dataChannel.state.kmsService.Verify(resp.ClientLTKeyARN, clientSignPayloadBytes, sig)
				if !ok || err != nil {
					panic(fmt.Errorf("failed to verify signature: %v", err))
				}

				// decode the client share
				var clientShareBytes []byte
				clientShareBytes, err = base64.StdEncoding.DecodeString(resp.ClientShare)
				if err != nil {
					err = fmt.Errorf("failed to decode server share: %v", err)
					log.Error(err)
					break
				}

				clientx, clienty := elliptic.UnmarshalCompressed(elliptic.P384(), clientShareBytes)

				// check that the client share is on the curve
				if !elliptic.P384().IsOnCurve(clientx, clienty) {
					err = fmt.Errorf("client share is not on the curve")
					log.Error(err)
					break
				}

				// generate and store the shared secret
				ss, _ := elliptic.P384().ScalarMult(clientx, clienty, dataChannel.state.agentSecret) // TODO: Double check it's fine to just use x
				dataChannel.state.sharedSecret = ss.Bytes()

				// hash the shared secret to obtain the session identifier
				hash := sha512.New384()
				hash.Write(dataChannel.state.sharedSecret)
				dataChannel.state.sessionID = hash.Sum(nil)

				log.Debugf("agent computed session ID: %v", base64.StdEncoding.EncodeToString(dataChannel.state.sessionID))
				// decode the session ID
				var sessionIDBytes []byte
				sessionIDBytes, err = base64.StdEncoding.DecodeString(resp.SessionID)
				if err != nil {
					err = fmt.Errorf("failed to decode server session id: %v", err)
					log.Error(err)
					break
				}

				if !bytes.Equal(dataChannel.state.sessionID, sessionIDBytes) {
					err = fmt.Errorf("session ID mismatch: session ID %s does not match client session ID %s", sessionIDBytes, dataChannel.state.sessionID)
					log.Error(err)
					break
				}

				// use the shared secret to generate read and write keys
				hash512 := sha512.New
				hkPRK := hkdf.Extract(hash512, dataChannel.state.sharedSecret, nil) //it's pretty complicated what using a salt with HKDF means, we should double check this

				const keySize = 32
				dataChannel.state.agentReadKey = make([]byte, keySize)
				dataChannel.state.agentWriteKey = make([]byte, keySize)

				hkdf.Expand(hash512, hkPRK, []byte("C")).Read(dataChannel.state.agentReadKey)
				hkdf.Expand(hash512, hkPRK, []byte("S")).Read(dataChannel.state.agentWriteKey)
				agentReadKey := dataChannel.state.agentReadKey
				encodedAgentReadKey := base64.RawStdEncoding.EncodeToString(agentReadKey)
				agentWriteKey := dataChannel.state.agentWriteKey
				encodedAgentWriteKey := base64.RawStdEncoding.EncodeToString(agentWriteKey)
				log.Debugf("agent read key: %s", encodedAgentReadKey)
				log.Debugf("agent write key: %s", encodedAgentWriteKey)

				// create ciphertext containing session keys:
				sessionKeys := mgsContracts.SessionKeys{
					AgentReadKey:  encodedAgentReadKey,
					AgentWriteKey: encodedAgentWriteKey,
				}
				sessionKeysBytes, err := json.Marshal(sessionKeys)
				if err != nil {
					err := fmt.Errorf("failed to encode session keys: %v", err)
					log.Error(err)
					panic(err)
				}

				// var encryptionContext map[string]*string
				// encryptedSessionKeys, err := dataChannel.kmsService.Encrypt(resp.LogLTKeyARN, sessionKeysBytes, encryptionContext)
				encryptedSessionKeys, err := rsa.EncryptPKCS1v15(cryptoRand.Reader, dataChannel.logLTPk, sessionKeysBytes)
				if err != nil {
					panic(fmt.Errorf("failed to encrypt session keys: %v", err))
				}
				encodedEncryptedSessionKeys := base64.StdEncoding.EncodeToString(encryptedSessionKeys)
				log.Infof("encrypted base-64-encoded session keys: %s", encodedEncryptedSessionKeys)

				// sign ciphertext containing session keys using KMS:
				signSessionKeysPayload := mgsContracts.SignSessionKeysPayload{
					EncryptedSessionKeys: encodedEncryptedSessionKeys,
					ClientId:             dataChannel.dataStream.GetClientId(),
				}

				signSessionKeysPayloadBytes, err := json.Marshal(signSessionKeysPayload)
				if err != nil {
					err := fmt.Errorf("failed to encode sign session keys payload: %v", err)
					log.Error(err)
					panic(err)
				}

				sigSessionKeys, err := dataChannel.state.kmsService.Sign(dataChannel.agentLTKeyARN, signSessionKeysPayloadBytes)
				if err != nil {
					err := fmt.Errorf("failed to sign session keys payload: %v", err)
					log.Error(err)
					panic(err)
				}

				encodedSigSessionKeys := base64.StdEncoding.EncodeToString(sigSessionKeys)

				// send ciphertext containing session keys and the corresponding signature to the log server:
				encryptedSessionKeysPayload := mgsContracts.EncryptedSessionKeysPayload{
					AgentLTKeyARN:        dataChannel.agentLTKeyARN,
					ClientId:             dataChannel.dataStream.GetClientId(),
					EncryptedSessionKeys: encodedEncryptedSessionKeys,
					Signature:            encodedSigSessionKeys,
				}
				encryptedSessionKeysPayloadBytes, err := json.Marshal(encryptedSessionKeysPayload)
				if err != nil {
					err := fmt.Errorf("failed to encode encrypted session keys payload: %v", err)
					log.Error(err)
					panic(err)
				}
				encodedEncryptedSessionKeysPayloadBytes := base64.StdEncoding.EncodeToString(encryptedSessionKeysPayloadBytes)
				log.Infof("encrypted session keys payload that should be sent to log server: %s", encodedEncryptedSessionKeysPayloadBytes)

				// TODO: actually send `encodedEncryptedSessionKeysPayloadBytes` to the log server!

				// dataChannel.encryptedAgentReadKey = encodedReadKey
				// dataChannel.encryptedClientReadKey = resp.EncryptedClientReadKey
				// dataChannel.logLTKeyARN = resp.LogLTKeyARN

				dataChannel.encryptionEnabled = true

				if err := dataChannel.blockCipher.UpdateEncryptionKey(log, append(dataChannel.state.agentReadKey, dataChannel.state.agentWriteKey...), "", ""); err != nil {
					err = fmt.Errorf("failed to update block cipher: %v", err)
					log.Error(err)
					break
				}
			case mgsContracts.KMSEncryption:
				err = dataChannel.finalizeKMSEncryption(log, action.ActionResult)
				break
			case mgsContracts.SessionType:
				break
			default:
				log.Warnf("Unknown handshake client action found, %s", action.ActionType)
			}
		}
		if err != nil {
			log.Error(err)
			// Cancel the session because handshake FAILED
			dataChannel.dataStream.CancelSession()
			// Set handshake error. Initiate handshake waits on handshake.responseChan and will return this error when channel returns.
			dataChannel.handshake.error = err
		}
	}
	dataChannel.handshake.clientVersion = handshakeResponse.ClientVersion
	log.Infof("Client side session manager plugin version is: %s", handshakeResponse.ClientVersion)
	dataChannel.handshake.responseChan <- true
	return nil
}

// handleEncryptionChallengeResponse is the handler for payload type EncryptionChallengeRequest
func (dataChannel *DataChannel) handleEncryptionChallengeResponse(log log.T, streamDataMessage mgsContracts.AgentMessage) error {
	log.Debug("Received Encryption Challenge Response.")
	var encChallengeResponse mgsContracts.EncryptionChallengeResponse
	if err := json.Unmarshal(streamDataMessage.Payload, &encChallengeResponse); err != nil {
		return fmt.Errorf("Unmarshalling of EncryptionChallengeResponse message failed, %s AND %v", streamDataMessage.Payload, err)
	}

	log.Info("Verifying encryption challenge..")
	responseChallenge, err := dataChannel.blockCipher.DecryptWithAESGCM(encChallengeResponse.Challenge)
	if err != nil {
		dataChannel.handshake.error = err
		return err
	}
	if !bytes.Equal(responseChallenge, dataChannel.handshake.encryptionChallenge) {
		err = fmt.Errorf("Encryption challenge does not match!")
		dataChannel.handshake.error = err
		return err
	}
	if err != nil {
		dataChannel.handshake.encryptionConfirmedChan <- false
	} else {
		dataChannel.handshake.encryptionConfirmedChan <- true
	}
	return nil
}

// SkipHandshake is used to skip handshake if the plugin decides it is not necessary
func (dataChannel *DataChannel) SkipHandshake(log log.T) {
	log.Info("Skipping handshake.")
	dataChannel.handshake.skipped = true
}

// finalizeKMSEncryption parses encryption parameters returned from the client and sets up encryption
func (dataChannel *DataChannel) finalizeKMSEncryption(log log.T, actionResult json.RawMessage) error {
	encryptionResponse := mgsContracts.KMSEncryptionResponse{}

	if err := json.Unmarshal(actionResult, &encryptionResponse); err != nil {
		return err
	}

	sessionId := dataChannel.dataStream.GetChannelId() // ChannelId is SessionId
	if err := dataChannel.blockCipher.UpdateEncryptionKey(log, encryptionResponse.KMSCipherTextKey, sessionId, dataChannel.dataStream.GetInstanceId()); err != nil {
		return fmt.Errorf("Fetching data key failed: %s", err)
	}
	dataChannel.encryptionEnabled = true
	return nil
}

type blockCipher struct {
	cipherTextKey    []byte
	encryptionKey    []byte
	decryptionKey    []byte
	encryptionCipher cipher.AEAD
	decryptionCipher cipher.AEAD
}

var _ crypto.IBlockCipher = (*blockCipher)(nil)

func (bc *blockCipher) UpdateEncryptionKey(log log.T, cipherTextBlob []byte, _, _ string) error {
	const keyLen = 32 // key length in bytes
	bc.cipherTextKey = cipherTextBlob
	bc.decryptionKey = cipherTextBlob[:keyLen]
	bc.encryptionKey = cipherTextBlob[keyLen:]
	log.Debugf("ENCRYPTION KEY: %x", bc.encryptionKey)
	log.Debugf("DECRYPTION KEY: %x", bc.decryptionKey)
	enc, err := getAEAD(bc.encryptionKey)
	bc.encryptionCipher = enc
	if err != nil {
		return fmt.Errorf("failed to get encryption cipher: %v", err)
	}
	dec, err := getAEAD(bc.decryptionKey)
	bc.decryptionCipher = dec
	if err != nil {
		return fmt.Errorf("failed to get decryption cipher: %v", err)
	}

	return nil
}

const nonceSize = 12

// EncryptWithGCM encrypts plain text using AES block cipher GCM mode
func (blockCipher *blockCipher) EncryptWithAESGCM(plainText []byte) (cipherText []byte, err error) {
	var aesgcm = blockCipher.encryptionCipher

	cipherText = make([]byte, nonceSize+len(plainText))
	nonce := make([]byte, nonceSize)
	if _, err := io.ReadFull(cryptoRand.Reader, nonce); err != nil {
		return nil, fmt.Errorf("failed to generate nonce for encryption: %v", err)
	}

	// Encrypt plain text using given key and newly generated nonce
	cipherTextWithoutNonce := aesgcm.Seal(nil, nonce, plainText, nil)

	// Append nonce to the beginning of the cipher text to be used while decrypting
	cipherText = append(cipherText[:nonceSize], nonce...)
	cipherText = append(cipherText[nonceSize:], cipherTextWithoutNonce...)
	return cipherText, nil
}

// DecryptWithGCM decrypts cipher text using AES block cipher GCM mode
func (blockCipher *blockCipher) DecryptWithAESGCM(cipherText []byte) (plainText []byte, err error) {
	var aesgcm = blockCipher.decryptionCipher

	// Pull the nonce out of the cipherText
	nonce := cipherText[:nonceSize]
	cipherTextWithoutNonce := cipherText[nonceSize:]

	// Decrypt just the actual cipherText using nonce extracted above
	if plainText, err = aesgcm.Open(nil, nonce, cipherTextWithoutNonce, nil); err != nil {
		return nil, fmt.Errorf("failed to decrypt encrypted text: %v", err)
	}
	return plainText, nil
}

// GetCipherTextKey returns cipherTextKey from BlockCipher
func (blockCipher *blockCipher) GetCipherTextKey() []byte {
	return blockCipher.cipherTextKey
}

// GetKMSKeyId returns kmsKeyId from BlockCipher
func (blockCipher *blockCipher) GetKMSKeyId() string {
	return ""
}

// getAEAD gets AEAD which is a GCM cipher mode providing authenticated encryption with associated data
func getAEAD(plainTextKey []byte) (aesgcm cipher.AEAD, err error) {
	var block cipher.Block
	if block, err = aes.NewCipher(plainTextKey); err != nil {
		return nil, fmt.Errorf("error creating NewCipher, %v", err)
	}

	if aesgcm, err = cipher.NewGCM(block); err != nil {
		return nil, fmt.Errorf("error creating NewGCM, %v", err)
	}

	return aesgcm, nil
}

// var newBlockCipher = func(context context.T, kmsKeyId string) (blockCipher crypto.IBlockCipher, err error) {
// 	return crypto.NewBlockCipher(context, kmsKeyId)
// }

// PerformHandshake performs handshake to share version string and encryption information with clients like cli/console
func (dataChannel *DataChannel) PerformHandshake(log log.T,
	kmsKeyId string,
	encryptionEnabled bool,
	sessionTypeRequest mgsContracts.SessionTypeRequest) (err error) {
	stdLog.Printf("PerformHandshake")

	if encryptionEnabled {
		// if dataChannel.blockCipher, err = newBlockCipher(dataChannel.context, kmsKeyId); err != nil {
		// 	return fmt.Errorf("Initializing BlockCipher failed: %s", err)
		// }
		log.Info("Encryption enabled: initializing block cipher")
		dataChannel.blockCipher = &blockCipher{}
	}

	dataChannel.handshake.handshakeStartTime = time.Now()
	dataChannel.encryptionEnabled = encryptionEnabled

	log.Info("Initiating Handshake")
	stdLog.Printf("Initiating Handshake")
	handshakeRequestPayload :=
		dataChannel.buildHandshakeRequestPayload(log, dataChannel.encryptionEnabled, sessionTypeRequest)
	if err := dataChannel.sendHandshakeRequest(log, handshakeRequestPayload); err != nil {
		return err
	}

	// notify Go routing handling received messages that it can process a message:
	dataChannel.handshake.startReceivingChan <- MessageReceptionChannelStatus{
		status: ReceiveHandshakeRespone,
	}

	// Block until handshake response is received or handshake times out
	select {
	case <-dataChannel.handshake.responseChan:
		{
			if dataChannel.handshake.error != nil {
				return dataChannel.handshake.error
			}
		}
	case <-time.After(handshakeTimeout):
		{
			// If handshake times out here this usually means that the client does not understand handshake or something
			// failed critically when processing handshake request.
			return errors.New("Handshake timed out. Please ensure that you have the latest version of the session manager plugin.")
		}
	}
	stdLog.Printf("Handshake response received")

	// If encryption was enabled send encryption challenge and block until challenge is received
	if dataChannel.encryptionEnabled {
		dataChannel.sendEncryptionChallenge(log)
		// notify Go routing handling received messages that it can process a message:
		dataChannel.handshake.startReceivingChan <- MessageReceptionChannelStatus{
			status: ReceiveEncryptionChallenge,
		}
		select {
		case <-dataChannel.handshake.encryptionConfirmedChan:
			if dataChannel.handshake.error != nil {
				return dataChannel.handshake.error
			}
			log.Info("Encryption challenge confirmed.")
		case <-time.After(handshakeTimeout):
			{
				// If handshake times out here this means the cli is too old and does not understand handshake protocol.
				return errors.New("Timed out waiting for encryption challenge.")
			}
		}
	}

	dataChannel.handshake.handshakeEndTime = time.Now()
	handshakeCompletePayload := dataChannel.buildHandshakeCompletePayload(log)
	if err := dataChannel.sendHandshakeComplete(log, handshakeCompletePayload); err != nil {
		return err
	}
	dataChannel.handshake.complete = true
	log.Info("Handshake successfully completed.")
	stdLog.Printf("Handshake successfully completed.")
	return
}

// buildHandshakeRequestPayload builds payload for HandshakeRequest
func (dataChannel *DataChannel) buildHandshakeRequestPayload(log log.T,
	encryptionRequested bool,
	request mgsContracts.SessionTypeRequest) mgsContracts.HandshakeRequestPayload {

	handshakeRequest := mgsContracts.HandshakeRequestPayload{}
	handshakeRequest.AgentVersion = version.Version
	handshakeRequest.RequestedClientActions = []mgsContracts.RequestedClientAction{
		{
			ActionType:       mgsContracts.SessionType,
			ActionParameters: request,
		}}
	if encryptionRequested {
		// Generate the secret using secure randomness from rand
		agentSecret, x, y, err := elliptic.GenerateKey(elliptic.P384(), cryptoRand.Reader)
		if err != nil {
			log.Errorf("failed to generate client secret: %v", err)
			panic(err)
		}

		dataChannel.state.agentSecret = agentSecret

		// Base64 encode the public part and put it in the message
		agentShare := elliptic.MarshalCompressed(elliptic.P384(), x, y)
		compressedPublic := base64.StdEncoding.EncodeToString(agentShare)

		dataChannel.state.kmsService, err = dataChannel.dataStream.GetKMSService()
		if err != nil {
			err := fmt.Errorf("failed to initialize KMS service: %v", err)
			log.Error(err)
			panic(err)
		}

		// TODO: do this beforehand and set `dataChannel.agentLTKeyARN` and `dataChannel.logLTPk`
		metadata, err := dataChannel.state.kmsService.CreateKeyAssymetric()
		if err != nil {
			err := fmt.Errorf("failed to create agent LTK: %v", err)
			log.Error(err)
			panic(err)
		}
		if metadata.Arn == nil {
			err := fmt.Errorf("asymmetric key ARN is nil, metadata: %+v", metadata)
			log.Error(err)
			panic(err)
		}
		dataChannel.agentLTKeyARN = *metadata.Arn
		sk, err := rsa.GenerateKey(cryptoRand.Reader, 4096)
		if err != nil {
			err := fmt.Errorf("failed to create log secret key: %v", err)
			log.Error(err)
			panic(err)
		}
		dataChannel.logLTPk = &sk.PublicKey

		signPayload := mgsContracts.SignAgentSharePayload{
			AgentShare:  compressedPublic,
			ClientId:    dataChannel.dataStream.GetClientId(),
			LogReaderId: dataChannel.logReaderId,
		}

		signPayloadBytes, err := json.Marshal(signPayload)
		if err != nil {
			err := fmt.Errorf("failed to encode sign payload: %v", err)
			log.Error(err)
			panic(err)
		}

		sig, err := dataChannel.state.kmsService.Sign(dataChannel.agentLTKeyARN, signPayloadBytes)
		if err != nil {
			err := fmt.Errorf("failed to sign agent sign payload: %v", err)
			log.Error(err)
			panic(err)
		}

		log.Debugf("agent signed sign payload: %x", sig)

		req := mgsContracts.SecureSessionRequest{
			Version:        1,
			ShareAlgorithm: "P384",
			AgentShare:     compressedPublic,
			Signature:      base64.StdEncoding.EncodeToString(sig),
			AgentLTKeyARN:  dataChannel.agentLTKeyARN,
			LogReaderId:    dataChannel.logReaderId,
		}

		log.Debugf("client generated SecureSessionRequest: %+v", req)

		handshakeRequest.RequestedClientActions = append(handshakeRequest.RequestedClientActions, mgsContracts.RequestedClientAction{
			ActionType:       mgsContracts.SecureSession,
			ActionParameters: req,
		})
		// handshakeRequest.RequestedClientActions = append(handshakeRequest.RequestedClientActions,
		// 	mgsContracts.RequestedClientAction{
		// 		ActionType: mgsContracts.KMSEncryption,
		// 		ActionParameters: mgsContracts.KMSEncryptionRequest{
		// 			KMSKeyID: dataChannel.blockCipher.GetKMSKeyId(),
		// 		}})
	}

	return handshakeRequest
}

// buildHandshakeCompletePayload builds payload for HandshakeComplete
func (dataChannel *DataChannel) buildHandshakeCompletePayload(log log.T) mgsContracts.HandshakeCompletePayload {
	handshakeComplete := mgsContracts.HandshakeCompletePayload{}
	handshakeComplete.HandshakeTimeToComplete =
		dataChannel.handshake.handshakeEndTime.Sub(dataChannel.handshake.handshakeStartTime)

	clientVersion := dataChannel.GetClientVersion()
	if dataChannel.separateOutputPayload == true && versionutil.Compare(clientVersion, clientVersionWithoutOutputSeparation, true) <= 0 {
		handshakeComplete.CustomerMessage = "Please update session manager plugin version (minimum required version " +
			firstVersionWithOutputSeparationFeature +
			") for fully support of separate StdOut/StdErr output.\r\n"
	}

	if dataChannel.encryptionEnabled {
		handshakeComplete.CustomerMessage += fmt.Sprintf(
			// "This session is encrypted using AWS KMS.\nlog LTK ARN: %s\nbase-64 encoded client read key: %s\nbase-64 encoded agent read key: %s",
			"This session is encrypted using AWS KMS.",
			// dataChannel.logLTKeyARN,
			// dataChannel.encryptedClientReadKey,
			// dataChannel.encryptedAgentReadKey,
		)
	}

	return handshakeComplete
}

// sendHandshakeRequest sends handshake request
func (dataChannel *DataChannel) sendHandshakeRequest(log log.T, handshakeRequestPayload mgsContracts.HandshakeRequestPayload) (err error) {
	var handshakeRequestPayloadBytes []byte
	if handshakeRequestPayloadBytes, err = json.Marshal(handshakeRequestPayload); err != nil {
		return fmt.Errorf("Could not serialize HandshakeRequest message %v, err: %s", handshakeRequestPayload, err)
	}

	log.Debug("Sending Handshake Request.")
	log.Tracef("Sending HandshakeRequest message with content %v", handshakeRequestPayload)
	if err = dataChannel.SendStreamDataMessage(log, mgsContracts.HandshakeRequest, handshakeRequestPayloadBytes); err != nil {
		return fmt.Errorf("Failed sending of HandshakeRequest message, err: %s", err)
	}
	return nil
}

// sendHandshakeComplete sends handshake complete
func (dataChannel *DataChannel) sendHandshakeComplete(log log.T, handshakeCompletePayload mgsContracts.HandshakeCompletePayload) (err error) {
	var handshakeCompletePayloadBytes []byte
	if handshakeCompletePayloadBytes, err = json.Marshal(handshakeCompletePayload); err != nil {
		return fmt.Errorf("Could not serialize HandshakeComplete message %v, err: %s", handshakeCompletePayload, err)
	}

	log.Debug("Sending HandshakeComplete.")
	log.Tracef("Sending HandshakeComplete message with content %v", handshakeCompletePayload)
	if err = dataChannel.SendStreamDataMessage(log, mgsContracts.HandshakeComplete, handshakeCompletePayloadBytes); err != nil {
		return err
	}
	return nil
}

// sendEncryptionChallenge sends encryption challenge
func (dataChannel *DataChannel) sendEncryptionChallenge(log log.T) (err error) {
	// Build the request
	encChallengeRequest := mgsContracts.EncryptionChallengeRequest{}
	randBytes := make([]byte, 64)
	cryptoRand.Read(randBytes)
	dataChannel.handshake.encryptionChallenge = randBytes
	randBytes, err = dataChannel.blockCipher.EncryptWithAESGCM(randBytes)
	if err != nil {
		return err
	}
	encChallengeRequest.Challenge = randBytes

	// Send it
	log.Debug("Sending EncryptionChallengeRequest.")
	err = dataChannel.sendStreamDataMessageJson(log, mgsContracts.EncChallengeRequest, encChallengeRequest)
	if err != nil {
		return err
	}
	return
}

// sendStreamDataMessageJson is utility method that serializes a struct into json and sends with the given payload type
func (dataChannel *DataChannel) sendStreamDataMessageJson(log log.T,
	payloadType mgsContracts.PayloadType, serializableStruct interface{}) (err error) {
	var messageBytes []byte
	if messageBytes, err = json.Marshal(serializableStruct); err != nil {
		return fmt.Errorf("Could not serialize message %v, err: %s", serializableStruct, err)
	}
	log.Tracef("Sending message with content %v", serializableStruct)
	err = dataChannel.SendStreamDataMessage(log, payloadType, messageBytes)
	return err
}

// GetClientVersion returns version of the client
func (dataChannel *DataChannel) GetClientVersion() string {
	return dataChannel.handshake.clientVersion
}

// GetInstanceId returns id of the target
func (dataChannel *DataChannel) GetInstanceId() string {
	return dataChannel.dataStream.GetInstanceId()
}

// GetRegion returns aws region of the target
func (dataChannel *DataChannel) GetRegion() string {
	return dataChannel.dataStream.GetRegion()
}

// IsActive returns a boolean value indicating the datachannel is actively listening
// and communicating with service
func (dataChannel *DataChannel) IsActive() bool {
	return dataChannel.dataStream.IsActive()
}

// GetSeparateOutputPayload returns boolean value indicating separate
// stdout/stderr output for non-interactive session or not
func (dataChannel *DataChannel) GetSeparateOutputPayload() bool {
	return dataChannel.separateOutputPayload
}

// SetSeparateOutputPayload set separateOutputPayload value
func (dataChannel *DataChannel) SetSeparateOutputPayload(separateOutputPayload bool) {
	dataChannel.separateOutputPayload = separateOutputPayload
}

func (dataChannel *DataChannel) Close(log log.T) error {
	return dataChannel.dataStream.Close(log)
}

func (dataChannel *DataChannel) PrepareToCloseChannel(log log.T) {
	dataChannel.PrepareToCloseChannel(log)
}
