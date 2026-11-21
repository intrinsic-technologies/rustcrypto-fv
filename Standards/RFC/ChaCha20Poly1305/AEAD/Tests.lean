import Lean.Data.Json
import Standards.RFC.ChaCha20Poly1305.ChaCha20.Tests

/-!
# RFC 8439 AEAD tests

The Poly1305 key generation and AEAD_CHACHA20_POLY1305 against the unmodified RFC 8439 text from
https://www.rfc-editor.org/rfc/rfc8439.txt, kept in `../Vectors/rfc8439.txt`:

* §2.6.2, one vector: the state setup with block counter zero, the printed "state after 20
  rounds", which is the state after the final addition of `chacha20_block` (its serialization is
  the printed output), and `poly1305KeyGen`;
* Appendix A.4, 3 vectors: `poly1305KeyGen`;
* §2.8.2, one vector: the nonce as the 32-bit fixed-common part followed by the IV, the setup and
  the final state of the one-time key's block, `poly1305KeyGen`, `aeadMacData` against the
  printed "AEAD Construction for Poly1305", and `chacha20AeadEncrypt`; then
  `chacha20AeadDecrypt` of the result, and its rejection of the same ciphertext with one bit of
  the tag, the AAD or the ciphertext changed;
* Appendix A.5, one vector: the key setup, the printed "state after 20 rounds" (again after the
  final addition), `poly1305KeyGen` against the printed out bytes and one-time key, `aeadMacData`
  against the printed Poly1305 input, and `chacha20AeadDecrypt` against the printed plaintext.

The expected values of these vectors are the RFC's. Their AADs are 12 bytes long and their
ciphertexts 114 and 265 bytes, so `pad16` adds 4, 14 and 7 zero bytes, and none has an empty AAD
or plaintext or an AAD or ciphertext whose length is a multiple of 16. Those cases come from:

* Project Wycheproof's `testvectors_v1/chacha20_poly1305_test.json` at commit
  `e0df04e0c033f2d25c5051dd06230336c7822358`, kept unmodified in
  `../Vectors/chacha20_poly1305_test.json` (SHA-256
  `fe61d25f90e1bde4461d00eafe61049e5f29bd999f36b766df9cda90906ad53d`), from
  https://github.com/C2SP/wycheproof/tree/e0df04e0c033f2d25c5051dd06230336c7822358.
  The count of its 325 tests is pinned. The 316 with a 96-bit nonce are checked: each of the 256
  valid ones by `chacha20AeadEncrypt` against the file's ciphertext and tag and by
  `chacha20AeadDecrypt` against its plaintext, and each of the 60 invalid ones, all with a
  modified tag, by `chacha20AeadDecrypt` returning `none`. The other 9, each marked invalid for a
  nonce of 0, 8, 11, 13, 14, 16, 20, 24 or 32 bytes, have no counterpart here, since the functions
  take a 12-byte nonce; they are only checked to be invalid and counted. Also pinned, among the
  valid ones: 45 have an empty AAD, 56 a non-empty AAD of a multiple of 16 bytes, 2 an empty
  ciphertext and 167 a non-empty ciphertext of a multiple of 16 bytes, so both branches of
  `pad16` are reached on both inputs. Every expected value is Wycheproof's.
-/

namespace Standards.RFC.ChaCha20Poly1305.AEAD.Tests

open Standards.Tests
open Standards.RFC.ChaCha20Poly1305
open Standards.RFC.ChaCha20Poly1305.Tests (pageLines dump octets)
open Standards.RFC.ChaCha20Poly1305.ChaCha20.Tests (textSection stateAfter toVector)

/-- §2.6.2: the Poly1305 key generation example -/
def keyGenerationExample (text : String) : IO Unit := do
  let part ← textSection text "2.6.2.  Poly1305 Key Generation Test Vector\n" "2.7.  "
  let lines := pageLines part
  let key ← toVector 32 (← dump lines "Key:") "§2.6.2 key"
  let nonce ← toVector 12 (← dump lines "Nonce:") "§2.6.2 nonce"
  let setup := initialState key 0 nonce
  check "§2.6.2: state setup" (setup ==
    (← stateAfter lines "The ChaCha state setup with key, nonce, and block counter zero:"))
  expect "§2.6.2: the printed state after 20 rounds, which includes the final addition"
    ⟨(chacha20Block key 0 nonce).toArray⟩
    ⟨(serialize (← stateAfter lines "The ChaCha state after 20 rounds:")).toArray⟩
  expect "§2.6.2: poly1305_key_gen" ⟨(poly1305KeyGen key nonce).toArray⟩
    (← dump lines "Output bytes:")

/-- Appendix A.4: the Poly1305 key generation test vectors; returns their number -/
def appendixKeyGeneration (text : String) : IO Nat := do
  let part ← textSection text "A.4.  Poly1305 Key Generation Using ChaCha20\n" "A.5.  "
  let mut count := 0
  for vector in (part.splitOn "Test Vector #").drop 1 do
    let label := s!"A.4 #{(vector.splitOn ":").head!}"
    let lines := pageLines vector
    let keyMarker := if (vector.splitOn "The ChaCha20 Key:").length > 1 then "The ChaCha20 Key:"
      else "The ChaCha20 Key"
    let key ← toVector 32 (← dump lines keyMarker) label
    let nonce ← toVector 12 (← dump lines "The nonce:") label
    expect s!"{label}: poly1305_key_gen" ⟨(poly1305KeyGen key nonce).toArray⟩
      (← dump lines "Poly1305 one-time key:")
    count := count + 1
  return count

/-- `bytes` with the lowest bit of byte `index` flipped -/
def flipBit (bytes : ByteArray) (index : Nat) : ByteArray := bytes.set! index (bytes[index]! ^^^ 1)

/-- §2.8.2: the AEAD example, its decryption, and three rejections -/
def aeadExample (text : String) : IO Unit := do
  let part ← textSection text "2.8.2.  Example and Test Vector for AEAD_CHACHA20_POLY1305\n"
    "3.  Implementation Advice"
  let lines := pageLines part
  let plaintext ← dump lines "Plaintext:"
  let aad ← dump lines "AAD:"
  let key ← toVector 32 (← dump lines "Key:") "§2.8.2 key"
  let nonce ← toVector 12 ((← dump lines "32-bit fixed-common part:") ++ (← dump lines "IV:"))
    "§2.8.2 nonce"
  check "§2.8.2: one-time key setup" (initialState key 0 nonce ==
    (← stateAfter lines "Setup for generating Poly1305 one-time key (sender id=7):"))
  expect "§2.8.2: state after generating the one-time key" ⟨(chacha20Block key 0 nonce).toArray⟩
    ⟨(serialize (← stateAfter lines "After generating Poly1305 one-time key:")).toArray⟩
  expect "§2.8.2: poly1305_key_gen" ⟨(poly1305KeyGen key nonce).toArray⟩
    (← dump lines "Poly1305 Key:")
  let ciphertext ← dump lines "Ciphertext:"
  let macData ← dump lines "AEAD Construction for Poly1305:"
  let tag ← toVector 16 (← octets part "Tag:\n") "§2.8.2 tag"
  check "§2.8.2: plaintext, AAD and ciphertext sizes"
    ((plaintext.size, aad.size, ciphertext.size, macData.size) == (114, 12, 114, 160))
  expect "§2.8.2: mac_data" (aeadMacData aad ciphertext) macData
  let (actualCiphertext, actualTag) := chacha20AeadEncrypt aad key nonce plaintext
  expect "§2.8.2: ciphertext" actualCiphertext ciphertext
  check "§2.8.2: tag" (actualTag == tag)
  expectSome "§2.8.2: decryption" (chacha20AeadDecrypt aad key nonce ciphertext tag) plaintext
  let flippedTag ← toVector 16 (flipBit ⟨tag.toArray⟩ 0) "§2.8.2 flipped tag"
  check "§2.8.2: changed tag rejected"
    ((chacha20AeadDecrypt aad key nonce ciphertext flippedTag).isNone)
  check "§2.8.2: changed AAD rejected"
    ((chacha20AeadDecrypt (flipBit aad 0) key nonce ciphertext tag).isNone)
  check "§2.8.2: changed ciphertext rejected"
    ((chacha20AeadDecrypt aad key nonce (flipBit ciphertext 113) tag).isNone)

/-- Appendix A.5: the AEAD decryption example -/
def decryptionExample (text : String) : IO Unit := do
  let part ← textSection text "A.5.  ChaCha20-Poly1305 AEAD Decryption\n" "Appendix B.  "
  let lines := pageLines part
  let key ← toVector 32 (← dump lines "The ChaCha20 Key") "A.5 key"
  let ciphertext ← dump lines "Ciphertext:"
  let nonce ← toVector 12 (← dump lines "The nonce:") "A.5 nonce"
  let aad ← dump lines "The AAD:"
  let tag ← toVector 16 (← dump lines "Received Tag:") "A.5 tag"
  check "A.5: key setup" (initialState key 0 nonce ==
    (← stateAfter lines "ChaCha state with key setup"))
  expect "A.5: the printed state after 20 rounds, which includes the final addition"
    ⟨(chacha20Block key 0 nonce).toArray⟩
    ⟨(serialize (← stateAfter lines "ChaCha state after 20 rounds")).toArray⟩
  expect "A.5: out bytes" ⟨(poly1305KeyGen key nonce).toArray⟩ (← octets part "out bytes:\n")
  expect "A.5: one-time key" ⟨(poly1305KeyGen key nonce).toArray⟩
    (← dump lines "Poly1305 one-time key:")
  expect "A.5: Poly1305 input" (aeadMacData aad ciphertext) (← dump lines "Poly1305 Input:")
  let plaintext ← dump lines "Plaintext::"
  check "A.5: AAD, ciphertext and plaintext sizes"
    ((aad.size, ciphertext.size, plaintext.size) == (12, 265, 265))
  expectSome "A.5: decryption" (chacha20AeadDecrypt aad key nonce ciphertext tag) plaintext

/-- A hex string field of a Wycheproof test as bytes -/
private def hexField (test : Lean.Json) (field : String) : IO ByteArray := do
  hex (← IO.ofExcept (test.getObjValAs? String field))

/--
Project Wycheproof's ChaCha20-Poly1305 tests: encryption and decryption of each valid test with a
96-bit nonce, rejection of each invalid one, and the pinned counts of the module doc
-/
def wycheproof : IO Unit := do
  let text ← IO.FS.readFile "Standards/RFC/ChaCha20Poly1305/Vectors/chacha20_poly1305_test.json"
  let json ← IO.ofExcept (Lean.Json.parse text)
  check "Wycheproof: algorithm" ((json.getObjValAs? String "algorithm").toOption ==
    some "CHACHA20-POLY1305")
  check "Wycheproof: numberOfTests" ((json.getObjValAs? Nat "numberOfTests").toOption == some 325)
  let mut total := 0
  let mut otherNonces := 0
  let mut valid := 0
  let mut invalid := 0
  let mut emptyAad := 0
  let mut blockAad := 0
  let mut emptyCiphertext := 0
  let mut blockCiphertext := 0
  for group in ← IO.ofExcept (json.getObjValAs? (Array Lean.Json) "testGroups") do
    let ivSize ← IO.ofExcept (group.getObjValAs? Nat "ivSize")
    check "Wycheproof: key and tag sizes" ((group.getObjValAs? Nat "keySize").toOption ==
      some 256 && (group.getObjValAs? Nat "tagSize").toOption == some 128)
    for test in ← IO.ofExcept (group.getObjValAs? (Array Lean.Json) "tests") do
      total := total + 1
      let id ← IO.ofExcept (test.getObjValAs? Nat "tcId")
      let label := s!"Wycheproof #{id}"
      let result ← IO.ofExcept (test.getObjValAs? String "result")
      if ivSize ≠ 96 then
        check s!"{label}: a nonce of {ivSize} bits is invalid" (result == "invalid")
        otherNonces := otherNonces + 1
        continue
      let key ← toVector 32 (← hexField test "key") label
      let nonce ← toVector 12 (← hexField test "iv") label
      let aad ← hexField test "aad"
      let plaintext ← hexField test "msg"
      let ciphertext ← hexField test "ct"
      let tag ← toVector 16 (← hexField test "tag") label
      if result == "valid" then
        let (actualCiphertext, actualTag) := chacha20AeadEncrypt aad key nonce plaintext
        expect s!"{label}: ciphertext" actualCiphertext ciphertext
        check s!"{label}: tag" (actualTag == tag)
        expectSome s!"{label}: decryption" (chacha20AeadDecrypt aad key nonce ciphertext tag)
          plaintext
        valid := valid + 1
        if aad.size = 0 then emptyAad := emptyAad + 1
        else if aad.size % 16 = 0 then blockAad := blockAad + 1
        if ciphertext.size = 0 then emptyCiphertext := emptyCiphertext + 1
        else if ciphertext.size % 16 = 0 then blockCiphertext := blockCiphertext + 1
      else
        check s!"{label}: result" (result == "invalid")
        check s!"{label}: rejected"
          ((chacha20AeadDecrypt aad key nonce ciphertext tag).isNone)
        invalid := invalid + 1
  check s!"Wycheproof: expected 325 tests, 9 with another nonce size, 256 valid and 60 invalid, \
    parsed {total}, {otherNonces}, {valid} and {invalid}"
    ((total, otherNonces, valid, invalid) == (325, 9, 256, 60))
  check s!"Wycheproof: expected 45, 56, 2 and 167 valid tests with an empty AAD, a block-multiple \
    AAD, an empty ciphertext and a block-multiple ciphertext, parsed {emptyAad}, {blockAad}, \
    {emptyCiphertext} and {blockCiphertext}"
    ((emptyAad, blockAad, emptyCiphertext, blockCiphertext) == (45, 56, 2, 167))

def run : IO Unit := do
  let text ← IO.FS.readFile "Standards/RFC/ChaCha20Poly1305/Vectors/rfc8439.txt"
  keyGenerationExample text
  let keys ← appendixKeyGeneration text
  check s!"A.4: expected 3 test vectors, parsed {keys}" (keys == 3)
  aeadExample text
  decryptionExample text
  wycheproof
  IO.println ("RFC8439 AEAD: the §2.6.2 and §2.8.2 examples, all 3 Appendix A.4 vectors, " ++
    "the Appendix A.5 decryption and the 316 Wycheproof tests with a 96-bit nonce passed")

end Standards.RFC.ChaCha20Poly1305.AEAD.Tests
