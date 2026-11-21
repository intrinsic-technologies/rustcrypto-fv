import Standards.RFC.ChaCha20Poly1305.Tests

/-!
# RFC 8439 ChaCha20 tests

ChaCha20 against the unmodified RFC 8439 text from https://www.rfc-editor.org/rfc/rfc8439.txt, kept
in `../Vectors/rfc8439.txt`, the file the Poly1305 tests read:

* §2.1, the example of the fourth line of the quarter round: `leftRoll` of `0x7998bfda` by 7;
* §2.1.1, one vector: `quarterRound`;
* §2.2.1, one vector: `qround` with indices 2, 7, 8 and 13 on the sample state, which changes only
  those four words;
* §2.3.2, one vector: `initialState`, ten iterations of `innerBlock`, the state after the final
  addition through `serialize`, and `chacha20Block`;
* §2.4.2, one vector: both block setups, both blocks after the block operation, the 114-byte
  keystream, and `chacha20Encrypt` of the 114-byte plaintext from initial counter 1;
* Appendix A.1, 5 vectors: `chacha20Block` and the state at the end, with block counters 0, 1
  and 2 and nonzero key and nonce bytes;
* Appendix A.2, 3 vectors: `chacha20Encrypt` of 64, 375 and 127 bytes from initial counters 0, 1
  and 42, and decryption by the same function.

Every expected value is the RFC's. The vectors cover plaintexts of one block, of several blocks,
and ending with a partial block, but no empty plaintext and no counter that wraps past 2^32 - 1;
those cases rest on the definitions alone.
-/

namespace Standards.RFC.ChaCha20Poly1305.ChaCha20.Tests

open Standards.Tests
open Standards.RFC.ChaCha20Poly1305
open Standards.RFC.ChaCha20Poly1305.Tests (pageLines dump octets)

/-- The text of the RFC section that starts with `start`, up to the heading `stop` -/
def textSection (text start stop : String) : IO String := do
  return ((← after text start).splitOn stop).head!

/--
The 16 words of the state printed as four rows of four hexadecimal words on the first non-blank
lines after the line ending with `marker`; asterisks that mark changed words are dropped
-/
def stateAfter (lines : List String) (marker : String) : IO (Vector UInt32 16) := do
  let rest := (lines.dropWhile fun line => !line.endsWith marker).drop 1
  let rows := (rest.dropWhile (·.trimAscii.isEmpty)).take 4
  let tokens := rows.flatMap fun row =>
    ((row.replace "*" " ").splitOn " ").filter fun token => !token.isEmpty
  check s!"{marker}: expected 16 words of 8 digits" (tokens.length == 16 &&
    tokens.all fun token => token.length == 8)
  let words ← tokens.mapM fun token =>
    token.toList.foldlM (fun word c => return 16 * word + (← hexDigit c)) 0
  return Vector.ofFn fun i => (words[i.val]!).toUInt32

/-- The value of the hexadecimal number `0x…` that ends the first line containing `marker` -/
def hexNumberAfter (lines : List String) (marker : String) : IO Nat := do
  let some line := lines.find? fun line => (line.splitOn marker).length > 1
    | throw (IO.userError s!"missing line with {marker}")
  let token := (((line.splitOn " ").filter (· ≠ "")).getLast!).replace "0x" ""
  token.toList.foldlM (fun value c => return 16 * value + (← hexDigit c)) 0

/-- The natural number that ends the first line starting with `marker` after trimming -/
def numberAfter (lines : List String) (marker : String) : IO Nat := do
  let some line := lines.find? fun line => line.trimAscii.toString.startsWith marker
    | throw (IO.userError s!"missing line {marker}")
  let some number := ((line.splitOn " ").filter (· ≠ "")).getLast!.toNat?
    | throw (IO.userError s!"no number on line {marker}")
  return number

/-- The colon-separated octets after `marker`, across lines, up to the first period -/
def octetsToPeriod (text marker : String) : IO ByteArray := do
  let digits := ((← after text marker).splitOn ".").head!
  hex (String.ofList ((digits.replace ":" "").toList.filter fun c => !c.isWhitespace))

/-- `bytes` as a vector of `n` bytes, failing with `label` on another length -/
def toVector (n : Nat) (bytes : ByteArray) (label : String) : IO (Vector UInt8 n) := do
  if h : bytes.data.size = n then return ⟨bytes.data, h⟩
  throw (IO.userError s!"{label}: expected {n} bytes, got {bytes.size}")

/-- §2.1's example of the fourth line and §2.1.1's quarter round test vector -/
def quarterRoundVectors (text : String) : IO Unit := do
  let example21 := pageLines (← textSection text "2.1.  The ChaCha Quarter Round\n" "2.1.1.  ")
  let rolled ← hexNumberAfter example21 "b = b <<< 7 ="
  check "§2.1: 0x7998bfda <<< 7" (leftRoll 0x7998bfda 7 == rolled.toUInt32)
  let lines := pageLines (← textSection text "2.1.1.  Test Vector for the ChaCha Quarter Round\n"
    "2.2.  ")
  let numbered := lines.filterMap fun line =>
    match (line.trimAscii.toString.splitOn " = 0x") with
    | [name, digits] => if ["a", "b", "c", "d"].contains name then some digits else none
    | _ => none
  check "§2.1.1: expected 8 values" (numbered.length == 8)
  let values ← numbered.mapM fun digits =>
    digits.toList.foldlM (fun value c => return 16 * value + (← hexDigit c)) 0
  let word (i : Nat) := (values[i]!).toUInt32
  check "§2.1.1: quarter round" (quarterRound (word 0) (word 1) (word 2) (word 3) ==
    (word 4, word 5, word 6, word 7))

/-- §2.2.1: QUARTERROUND(2, 7, 8, 13) on the sample state -/
def stateQuarterRoundVector (text : String) : IO Unit := do
  let lines := pageLines (← textSection text
    "2.2.1.  Test Vector for the Quarter Round on the ChaCha State\n" "2.3.  ")
  let sample ← stateAfter lines "Sample ChaCha State"
  let expected ← stateAfter lines "After applying QUARTERROUND(2, 7, 8, 13)"
  check "§2.2.1: QUARTERROUND(2, 7, 8, 13)" (qround sample 2 7 8 13 == expected)
  check "§2.2.1: only words 2, 7, 8 and 13 change" ((List.range 16).all fun i =>
    [2, 7, 8, 13].contains i || sample[i]! == expected[i]!)

/-- §2.3.2: the block function on its test vector, step by step -/
def blockVector (text : String) : IO Unit := do
  let part ← textSection text "2.3.2.  Test Vector for the ChaCha20 Block Function\n" "2.4.  "
  let lines := pageLines part
  let key ← toVector 32 (← octetsToPeriod part "Key = ") "§2.3.2 key"
  let nonce ← toVector 12 (← hex (((← after part "Nonce = (").splitOn ")").head!.replace ":" ""))
    "§2.3.2 nonce"
  let setup := initialState key 1 nonce
  check "§2.3.2: state setup" (setup == (← stateAfter lines "ChaCha state with the key setup."))
  let rounds := Nat.repeat innerBlock 10 setup
  check "§2.3.2: state after 20 rounds"
    (rounds == (← stateAfter lines "ChaCha state after 20 rounds"))
  let final ← stateAfter lines "ChaCha state at the end of the ChaCha20 operation"
  check "§2.3.2: state at the end" ((Vector.ofFn fun i => rounds[i] + setup[i]) == final)
  let block ← dump lines "Serialized Block:"
  expect "§2.3.2: serialized state" ⟨(serialize final).toArray⟩ block
  expect "§2.3.2: chacha20_block" ⟨(chacha20Block key 1 nonce).toArray⟩ block

/-- §2.4.2: the encryption example from initial counter 1 -/
def encryptionExample (text : String) : IO Unit := do
  let part ← textSection text "2.4.2.  Example and Test Vector for the ChaCha20 Cipher\n" "2.5.  "
  let lines := pageLines part
  let key ← toVector 32 (← octetsToPeriod part "Key = ") "§2.4.2 key"
  let nonce ← toVector 12 (← hex (((← after part "Nonce = (").splitOn ")").head!.replace ":" ""))
    "§2.4.2 nonce"
  check "§2.4.2: first block setup" (initialState key 1 nonce ==
    (← stateAfter lines "First block setup:"))
  check "§2.4.2: second block setup" (initialState key 2 nonce ==
    (← stateAfter lines "Second block setup:"))
  expect "§2.4.2: first block after block operation" ⟨(chacha20Block key 1 nonce).toArray⟩
    ⟨(serialize (← stateAfter lines "First block after block operation:")).toArray⟩
  expect "§2.4.2: second block after block operation" ⟨(chacha20Block key 2 nonce).toArray⟩
    ⟨(serialize (← stateAfter lines "Second block after block operation:")).toArray⟩
  let plaintext ← dump lines "Plaintext Sunscreen:"
  check "§2.4.2: 114-byte plaintext" (plaintext.size == 114)
  let keystream ← octets part "Keystream:\n"
  expect "§2.4.2: keystream" (chacha20Encrypt key 1 nonce ⟨Array.replicate 114 0⟩) keystream
  let ciphertext ← dump lines "Ciphertext Sunscreen:"
  expect "§2.4.2: chacha20_encrypt" (chacha20Encrypt key 1 nonce plaintext) ciphertext
  expect "§2.4.2: decryption" (chacha20Encrypt key 1 nonce ciphertext) plaintext

/-- Appendix A.1: the block function test vectors; returns their number -/
def appendixBlocks (text : String) : IO Nat := do
  let part ← textSection text "A.1.  The ChaCha20 Block Functions\n" "A.2.  ChaCha20 Encryption"
  let mut count := 0
  for vector in (part.splitOn "Test Vector #").drop 1 do
    let label := s!"A.1 #{(vector.splitOn ":").head!}"
    let lines := pageLines vector
    let key ← toVector 32 (← dump lines "Key:") label
    let nonce ← toVector 12 (← dump lines "Nonce:") label
    let counter ← numberAfter lines "Block Counter = "
    let keystream ← dump lines "Keystream:"
    expect s!"{label}: chacha20_block" ⟨(chacha20Block key counter.toUInt32 nonce).toArray⟩
      keystream
    expect s!"{label}: state at the end" ⟨(serialize (← stateAfter lines
      "ChaCha state at the end")).toArray⟩ keystream
    count := count + 1
  return count

/-- The plaintext lengths of Appendix A.2's test vectors #1–#3, counted from the printed data -/
def encryptionLengths : List Nat := [64, 375, 127]

/-- Appendix A.2: the encryption test vectors; returns their number -/
def appendixEncryption (text : String) : IO Nat := do
  let part ← textSection text "A.2.  ChaCha20 Encryption\n" "A.3.  Poly1305 Message Authentication"
  let mut count := 0
  for vector in (part.splitOn "Test Vector #").drop 1 do
    let label := s!"A.2 #{(vector.splitOn ":").head!}"
    let lines := pageLines vector
    let key ← toVector 32 (← dump lines "Key:") label
    let nonce ← toVector 12 (← dump lines "Nonce:") label
    let counter ← numberAfter lines "Initial Block Counter = "
    let plaintext ← dump lines "Plaintext:"
    let ciphertext ← dump lines "Ciphertext:"
    check s!"{label}: plaintext length" (some plaintext.size == encryptionLengths[count]?)
    expect s!"{label}: chacha20_encrypt" (chacha20Encrypt key counter.toUInt32 nonce plaintext)
      ciphertext
    expect s!"{label}: decryption" (chacha20Encrypt key counter.toUInt32 nonce ciphertext) plaintext
    count := count + 1
  return count

def run : IO Unit := do
  let text ← IO.FS.readFile "Standards/RFC/ChaCha20Poly1305/Vectors/rfc8439.txt"
  quarterRoundVectors text
  stateQuarterRoundVector text
  blockVector text
  encryptionExample text
  let blocks ← appendixBlocks text
  check s!"A.1: expected 5 test vectors, parsed {blocks}" (blocks == 5)
  let encryptions ← appendixEncryption text
  check s!"A.2: expected 3 test vectors, parsed {encryptions}" (encryptions == 3)
  IO.println ("RFC8439 ChaCha20: the §§2.1–2.4 examples, all 5 Appendix A.1 and all 3 " ++
    "Appendix A.2 vectors passed")

end Standards.RFC.ChaCha20Poly1305.ChaCha20.Tests
