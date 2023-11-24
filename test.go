package test

//@ import "bytes"
//@ import "github.com/aws/amazon-ssm-agent/agent/iospecs/abs"
//@ import by "github.com/aws/amazon-ssm-agent/agent/iospecs/bytes"
//@ import tm "github.com/aws/amazon-ssm-agent/agent/iospecs/term"
//@ import "github.com/aws/amazon-ssm-agent/agent/iospecs/pub"

type ActionType string
type ActionStatus int
type RawMessage []byte

const SecureSession ActionType = "SecureSession"
const Success ActionStatus = 1

// The result of processing the action by the plugin
type ProcessedClientAction struct {
	ActionType   ActionType   `json:"ActionType"`
	ActionStatus ActionStatus `json:"ActionStatus"`
	ActionResult RawMessage   `json:"ActionResult"`
	Error        string       `json:"Error"`
}

/*@
pred (processedClientAction *ProcessedClientAction) Mem() {
	acc(processedClientAction) &&
	acc(bytes.SliceMem(processedClientAction.ActionResult))
}

ghost
decreases
requires acc(processedClientAction.Mem(), _)
pure func (processedClientAction *ProcessedClientAction) Type() ActionType {
	return unfolding acc(processedClientAction.Mem(), _) in processedClientAction.ActionType
}

ghost
decreases
requires acc(processedClientAction.Mem(), _)
pure func (processedClientAction *ProcessedClientAction) Status() ActionStatus {
	return unfolding acc(processedClientAction.Mem(), _) in processedClientAction.ActionStatus
}

ghost
decreases
requires acc(processedClientAction.Mem(), _)
pure func (processedClientAction *ProcessedClientAction) Adt() ProcessedClientActionAdt {
	return Action{processedClientAction.Type(), processedClientAction.Status()}
}

ghost
decreases
requires acc(processedClientAction.Mem(), _)
pure func (processedClientAction *ProcessedClientAction) Abs() by.Bytes {
	return unfolding acc(processedClientAction.Mem(), _) in
		abs.Abs(processedClientAction.ActionResult)
}
// pair(exp(pubTerm(const_g_pub()), z), pair(SigY, pair(ClientLtKeyId, hash(exp(exp(pubTerm(const_g_pub()), z), x)))))))
@*/

// Handshake Response sent by the plugin in response to the handshake request
type HandshakeResponsePayload struct {
	ClientVersion          string                  `json:"ClientVersion"`
	ProcessedClientActions []ProcessedClientAction `json:"ProcessedClientActions"`
	Errors                 []string                `json:"Errors"`
}

/*@
pred (handshakeResponsePayload *HandshakeResponsePayload) Mem() {
	acc(handshakeResponsePayload) &&
	(forall i int :: { handshakeResponsePayload.ProcessedClientActions[i] } 0 <= i && i < len(handshakeResponsePayload.ProcessedClientActions) ==> handshakeResponsePayload.ProcessedClientActions[i].Mem()) &&
	acc(handshakeResponsePayload.Errors)
}

// ghost
// requires acc(handshakeResponsePayload.Mem(), _)
// requires handshakeResponsePayload.ContainsSecureSession(i)
// pure func (handshakeResponsePayload *HandshakeResponsePayload) Abs(i int) by.Bytes {
// 	return unfolding acc(handshakeResponsePayload.Mem(), _) in
// 			by.pairB(by.gamma(tm.pubTerm(pub.const_SecureSessionResponse_pub())), handshakeResponsePayload.ProcessedClientActions[i].Abs())
// }

ghost
requires acc(handshakeResponsePayload.Mem(), _)
pure func (handshakeResponsePayload *HandshakeResponsePayload) Abs() by.Bytes {
// 	return handshakeResponsePayload.ContainsSecureSession() ?
// 		(unfolding acc(handshakeResponsePayload.Mem(), _) in
// 			by.tupleB(by.gamma(tm.pubTerm(pub.const_SecureSessionResponse_pub())), )):
// 		handshakeResponsePayload.UnknownAbs()
	return handshakeResponsePayload.ContainsSecureSession() ?
		(unfolding acc(handshakeResponsePayload.Mem(), _) in by.pairB(by.gamma(tm.pubTerm(pub.const_SecureSessionResponse_pub())), handshakeResponsePayload.ProcessedClientActions[getSecureSessionIndex(handshakeResponsePayload.ProcessedClientActions, 0)].Abs())) :
		handshakeResponsePayload.UnknownAbs()
// 		by.tupleB(by.gamma(tm.pubTerm(pub.const_SecureSessionResponse_pub())), )
// 		pair(pubTerm(const_SecureSessionResponse_pub()), pair(exp(pubTerm(const_g_pub()), z), pair(SigY, pair(ClientLtKeyId, hash(exp(exp(pubTerm(const_g_pub()), z), x)))))))
}

// used to represent an unknown byte-level representation for a given handshake response payload
ghost
decreases
requires acc(handshakeResponsePayload.Mem(), _)
pure func (handshakeResponsePayload *HandshakeResponsePayload) UnknownAbs() by.Bytes

ghost
decreases
requires acc(handshakeResponsePayload.Mem(), _)
pure func (handshakeResponsePayload *HandshakeResponsePayload) SecureSessionAtIndex(i int) bool {
	return unfolding acc(handshakeResponsePayload.Mem(), _) in
		0 <= i && i < len(handshakeResponsePayload.ProcessedClientActions) &&
			handshakeResponsePayload.ProcessedClientActions[i].Type() == SecureSession &&
			handshakeResponsePayload.ProcessedClientActions[i].Status() == Success
}

ghost
decreases
requires acc(handshakeResponsePayload.Mem(), _)
pure func (handshakeResponsePayload *HandshakeResponsePayload) ContainsSecureSession() bool {
// 	return unfolding acc(handshakeResponsePayload.Mem(), _) in
// 		exists i int :: 0 <= i && i < len(handshakeResponsePayload.ProcessedClientActions) &&
// 			handshakeResponsePayload.ProcessedClientActions[i].Type() == SecureSession &&
// 			handshakeResponsePayload.ProcessedClientActions[i].Status() == Success
	return unfolding acc(handshakeResponsePayload.Mem(), _) in
		containsSecureSession(handshakeResponsePayload.ProcessedClientActions, 0)
}

ghost
decreases
requires acc(handshakeResponsePayload.Mem(), _)
requires handshakeResponsePayload.ContainsSecureSession()
pure func (handshakeResponsePayload *HandshakeResponsePayload) GetSecureSessionIndex() int {
	// return 0 <= i && i < len(handshakeResponsePayload.ProcessedClientActions) &&
	// 		handshakeResponsePayload.ProcessedClientActions[i].Type() == SecureSession &&
	// 		handshakeResponsePayload.ProcessedClientActions[i].Status() == Success
	return unfolding acc(handshakeResponsePayload.Mem(), _) in
		getSecureSessionIndex(handshakeResponsePayload.ProcessedClientActions, 0)
}

// ghost
// requires acc(handshakeResponsePayload, _)
// requires 0 <= startIdx && startIdx <= len(handshakeResponsePayload.ProcessedClientActions)
// requires forall i int :: { handshakeResponsePayload.ProcessedClientActions[i] } startIdx <= i && i < len(handshakeResponsePayload.ProcessedClientActions) ==> acc(handshakeResponsePayload.ProcessedClientActions[i].Mem(), _)
// decreases len(handshakeResponsePayload.ProcessedClientActions) - startIdx
// pure func (handshakeResponsePayload *HandshakeResponsePayload) containsSecureSession(startIdx int) bool {
// 	// return exists i int :: startIdx <= i && i < len(handshakeResponsePayload.ProcessedClientActions) &&
// 	// 		handshakeResponsePayload.ProcessedClientActions[i].Type() == SecureSession &&
// 	// 		handshakeResponsePayload.ProcessedClientActions[i].Status() == Success
// 	return startIdx == len(handshakeResponsePayload.ProcessedClientActions) ? false :
// 		(handshakeResponsePayload.ProcessedClientActions[startIdx].Type() == SecureSession &&
// 		handshakeResponsePayload.ProcessedClientActions[startIdx].Status() == Success ?
// 			true : handshakeResponsePayload.containsSecureSession(startIdx + 1))
// }

ghost
requires 0 <= startIdx && startIdx <= len(actions)
requires forall i int :: { actions[i] } startIdx <= i && i < len(actions) ==> acc(actions[i].Mem(), _)
decreases len(actions) - startIdx
pure func containsSecureSession(actions []ProcessedClientAction, startIdx int) bool {
	// return exists i int :: startIdx <= i && i < len(actions) &&
	// 		actions[i].Type() == SecureSession &&
	// 		actions[i].Status() == Success
	return startIdx == len(actions) ? false :
		(actions[startIdx].Type() == SecureSession &&
		actions[startIdx].Status() == Success ?
			true : containsSecureSession(actions, startIdx + 1))
}

// ghost
// requires acc(handshakeResponsePayload, _)
// requires 0 <= startIdx && startIdx <= len(handshakeResponsePayload.ProcessedClientActions)
// requires forall i int :: { handshakeResponsePayload.ProcessedClientActions[i] } startIdx <= i && i < len(handshakeResponsePayload.ProcessedClientActions) ==> acc(handshakeResponsePayload.ProcessedClientActions[i].Mem(), _)
// requires handshakeResponsePayload.containsSecureSession(startIdx)
// ensures  startIdx <= res && res < len(handshakeResponsePayload.ProcessedClientActions)
// ensures  handshakeResponsePayload.ProcessedClientActions[res].Type() == SecureSession
// ensures  handshakeResponsePayload.ProcessedClientActions[res].Status() == Success
// decreases len(handshakeResponsePayload.ProcessedClientActions) - startIdx
// pure func (handshakeResponsePayload *HandshakeResponsePayload) getSecureSessionIndex(startIdx int) (res int) {
// 	return handshakeResponsePayload.ProcessedClientActions[startIdx].Type() == SecureSession &&
// 		handshakeResponsePayload.ProcessedClientActions[startIdx].Status() == Success ?
// 			startIdx : handshakeResponsePayload.getSecureSessionIndex(startIdx + 1)
// }

ghost
requires 0 <= startIdx && startIdx <= len(actions)
requires forall i int :: { actions[i] } startIdx <= i && i < len(actions) ==> acc(actions[i].Mem(), _)
requires containsSecureSession(actions, startIdx)
ensures  startIdx <= res && res < len(actions)
ensures  actions[res].Type() == SecureSession
ensures  actions[res].Status() == Success
decreases len(actions) - startIdx
pure func getSecureSessionIndex(actions []ProcessedClientAction, startIdx int) (res int) {
	return actions[startIdx].Type() == SecureSession &&
		actions[startIdx].Status() == Success ?
			startIdx : getSecureSessionIndex(actions, startIdx + 1)
}

type ProcessedClientActionAdt adt {
	Action {
		ActionType ActionType
		ActionStatus ActionStatus
	}
}

ghost
requires acc(handshakeResponsePayload.Mem(), _)
requires 0 <= startIdx && startIdx <= unfolding acc(handshakeResponsePayload.Mem(), _) in len(handshakeResponsePayload.ProcessedClientActions)
decreases unfolding acc(handshakeResponsePayload.Mem(), _) in len(handshakeResponsePayload.ProcessedClientActions) - startIdx
pure func (handshakeResponsePayload *HandshakeResponsePayload) Adt(startIdx int) (res seq[ProcessedClientActionAdt]) {
	return unfolding acc(handshakeResponsePayload.Mem(), _) in
		len(handshakeResponsePayload.ProcessedClientActions) - startIdx == 0 ? seq[ProcessedClientActionAdt]{} :
			seq[ProcessedClientActionAdt]{ handshakeResponsePayload.ProcessedClientActions[startIdx].Adt() } ++ handshakeResponsePayload.Adt(startIdx + 1)
}
@*/
