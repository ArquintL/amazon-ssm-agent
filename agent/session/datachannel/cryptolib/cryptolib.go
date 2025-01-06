package cryptolib

import (
	"crypto/aes"
	"crypto/cipher"
	cryptoRand "crypto/rand"
	"fmt"
	"io"
	//@ "bytes"
	//@ abs "github.com/aws/amazon-ssm-agent/agent/iospecs/abs"
	//@ by "github.com/aws/amazon-ssm-agent/agent/iospecs/bytes"
	//@ tm "github.com/aws/amazon-ssm-agent/agent/iospecs/term"
)

type BlockCipherT struct {
	ready            bool
	cipherTextKey    []byte
	encryptionKey    []byte
	decryptionKey    []byte
	encryptionCipher cipher.AEAD
	decryptionCipher cipher.AEAD
	//@ ghost encKeyT tm.Term
	//@ ghost decKeyT tm.Term
}

/*@
pred (bc *BlockCipherT) Mem() {
	acc(bc) &&
	(bc.ready ==>
		bytes.SliceMem(bc.cipherTextKey) &&
		bytes.SliceMem(bc.encryptionKey) &&
		by.gamma(bc.encKeyT) == abs.Abs(bc.encryptionKey) &&
		bytes.SliceMem(bc.decryptionKey) &&
		by.gamma(bc.decKeyT) == abs.Abs(bc.decryptionKey) &&
		bc.encryptionCipher.Mem() &&
		bc.decryptionCipher.Mem())
}

ghost
decreases
requires acc(bc.Mem(), _)
ensures  bc.IsReady() ==> by.gamma(res) == bc.GetEncKeyB()
pure func (bc *BlockCipherT) GetEncKeyT() (res tm.Term) {
	return unfolding acc(bc.Mem(), _) in bc.encKeyT
}

ghost
decreases
requires acc(bc.Mem(), _) && bc.IsReady()
pure func (bc *BlockCipherT) GetEncKeyB() by.Bytes {
	return unfolding acc(bc.Mem(), _) in abs.Abs(bc.encryptionKey)
}

ghost
decreases
requires acc(bc.Mem(), _)
pure func (bc *BlockCipherT) GetDecKeyT() tm.Term {
	return unfolding acc(bc.Mem(), _) in bc.decKeyT
}

ghost
decreases
requires acc(bc.Mem(), _) && bc.IsReady()
pure func (bc *BlockCipherT) GetDecKeyB() by.Bytes {
	return unfolding acc(bc.Mem(), _) in abs.Abs(bc.decryptionKey)
}
@*/

// @ decreases
// @ requires acc(bc.Mem(), _)
// @ pure
func (bc *BlockCipherT) IsReady() bool {
	return /*@ unfolding acc(bc.Mem(), _) in @*/ bc.ready
}

// @ trusted
// @ requires noPerm < p
// @ requires bc.Mem() && acc(bytes.SliceMem(readKey), p) && acc(bytes.SliceMem(writeKey), p)
// @ requires by.gamma(readKeyT) == abs.Abs(readKey) && by.gamma(writeKeyT) == abs.Abs(writeKey)
// @ ensures  bc.Mem() && acc(bytes.SliceMem(readKey), p) && acc(bytes.SliceMem(writeKey), p)
// @ ensures  err == nil ==> bc.IsReady() && bc.GetEncKeyT() == writeKeyT && bc.GetDecKeyT() == readKeyT
// @ ensures  err != nil ==> err.ErrorMem()
func (bc *BlockCipherT) UpdateEncryptionKeys(readKey, writeKey []byte /*@, ghost p perm, ghost readKeyT tm.Term, ghost writeKeyT tm.Term @*/) (err error) {
	if len(readKey) != 32 || len(writeKey) != 32 {
		return fmt.Errorf("read or write key have invalid length")
	}
	newEncryptionKey := make([]byte, 2*32)
	copy(newEncryptionKey[:32], readKey)
	copy(newEncryptionKey[32:], writeKey)
	//@ bc.decKeyT = readKeyT
	//@ bc.encKeyT = writeKeyT
	return bc.UpdateEncryptionKey(newEncryptionKey, "", "" /*@, p @*/)
}

// @ trusted
// @ requires noPerm < p
// @ requires acc(bytes.SliceMem(cipherTextBlob), p)
// @ preserves bc.Mem()
// @ ensures err != nil ==> err.ErrorMem()
func (bc *BlockCipherT) UpdateEncryptionKey(cipherTextBlob []byte, _, _ string /*@, ghost p perm @*/) (err error) {
	const keyLen = 32 // key length in bytes
	bc.cipherTextKey = cipherTextBlob
	bc.decryptionKey = cipherTextBlob[:keyLen]
	bc.encryptionKey = cipherTextBlob[keyLen:]
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
// @ trusted
// @ requires noPerm < p
// @ requires acc(blockCipher.Mem(), p) && blockCipher.IsReady()
// @ preserves acc(bytes.SliceMem(plainText), p)
// @ ensures  acc(blockCipher.Mem(), p) && blockCipher.IsReady()
// @ ensures  err == nil ==> bytes.SliceMem(cipherText)
// @ ensures  err != nil ==> err.ErrorMem()
// @ ensures  err == nil ==> abs.Abs(cipherText) == by.sencB(abs.Abs(plainText), blockCipher.GetEncKeyB())
func (blockCipher *BlockCipherT) EncryptWithAESGCM(plainText []byte /*@, ghost p perm @*/) (cipherText []byte, err error) {
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
// @ trusted
// @ requires noPerm < p
// @ preserves acc(blockCipher.Mem(), p) && blockCipher.IsReady()
// @ preserves acc(bytes.SliceMem(cipherText), p)
// @ ensures err == nil ==> bytes.SliceMem(plainText)
// @ ensures err != nil ==> err.ErrorMem()
// @ ensures err == nil ==> abs.Abs(cipherText) == by.sencB(abs.Abs(plainText), blockCipher.GetDecKeyB())
func (blockCipher *BlockCipherT) DecryptWithAESGCM(cipherText []byte /*@, ghost p perm @*/) (plainText []byte, err error) {
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
// @ requires false
func (blockCipher *BlockCipherT) GetCipherTextKey() []byte {
	return blockCipher.cipherTextKey
}

// GetKMSKeyId returns kmsKeyId from BlockCipher
func (blockCipher *BlockCipherT) GetKMSKeyId() string {
	return ""
}

// getAEAD gets AEAD which is a GCM cipher mode providing authenticated encryption with associated data
// @ trusted
// @ requires noPerm < p
// @ preserves acc(bytes.SliceMem(plainTextKey), p)
// @ ensures err == nil ==> aesgcm.Mem()
func getAEAD(plainTextKey []byte /*@, ghost p perm @*/) (aesgcm cipher.AEAD, err error) {
	var block cipher.Block
	if block, err = aes.NewCipher(plainTextKey); err != nil {
		return nil, fmt.Errorf("error creating NewCipher, %v", err)
	}

	if aesgcm, err = cipher.NewGCM(block); err != nil {
		return nil, fmt.Errorf("error creating NewGCM, %v", err)
	}

	return aesgcm, nil
}
