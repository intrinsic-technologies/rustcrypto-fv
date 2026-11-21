import Standards.RFC.ChaCha20Poly1305
import Standards.Tests.Utilities

/-!
# RFC 8439 tests

Poly1305 against the unmodified RFC 8439 text from https://www.rfc-editor.org/rfc/rfc8439.txt,
kept in `Vectors/rfc8439.txt`.

* §2.5.2, one vector: `clamp` and `leBytesToNum` of `r` and `s`, `numTo16LeBytes` of the 130-bit
  `Acc + s`, and `poly1305Mac` of the 34-byte message;
* Appendix A.3, 11 vectors: `poly1305Mac`, test vectors #1–#4 from hex dumps and #5–#11 from `R`,
  `S`, `data`, and `tag`;
* §2.8.2 and Appendix A.5, two vectors: `poly1305Mac` of the Poly1305 input printed in the AEAD
  examples ("AEAD Construction for Poly1305" and "Poly1305 Input") under the printed one-time key;
  for A.5, also that the received tag equals the calculated one.

The vectors cover messages of 16, 34, 48, 64, 127, 160, 304, and 375 bytes, including messages
that end with a partial block, but no empty message and none shorter than one block. Each
expected value is the RFC's.

No vector here reaches `a + s ≥ p` in the last step of `poly1305Mac`, so these tests would not
notice `a + s` reduced modulo `p` before `num_to_16_le_bytes` takes it modulo 2^128.
-/

namespace Standards.RFC.ChaCha20Poly1305.Tests

open Standards.Tests

/-- The lines of the text without page footers, page headers, and form feeds -/
def pageLines (text : String) : List String :=
  (text.splitOn "\n").filter fun line =>
    !(line.startsWith "Nir & Langley" || line.startsWith "RFC 8439 " || line.startsWith "\x0c")

/--
The bytes of a hex dump line such as `  016  6f 20 ...  ascii`, indented by two or more spaces: the
48 columns after the three-digit offset and its two spaces
-/
private def dumpLine (line : String) : Option String :=
  let chars := line.toList.dropWhile (· == ' ')
  if line.startsWith "  " && chars.length ≥ 7 && (chars.take 3).all Char.isDigit &&
      (chars.drop 3).take 2 == [' ', ' ']
    then some (String.ofList ((chars.drop 5).take 48))
  else none

/-- The bytes of the hex dump that starts on the first non-blank line after `marker` -/
def dump (lines : List String) (marker : String) : IO ByteArray := do
  let rest := (lines.dropWhile fun line => !line.endsWith marker).drop 1
  let body := (rest.dropWhile (·.trimAscii.isEmpty)).takeWhile fun line => (dumpLine line).isSome
  check s!"empty dump after {marker}" (!body.isEmpty)
  hex (String.join (body.filterMap dumpLine))

/-- The bytes of the lines of plain hex after the line `marker`, up to the next non-hex line -/
private def hexLines (lines : List String) (marker : String) : IO ByteArray := do
  let rest := (lines.dropWhile fun line => line.trimAscii.toString != marker).drop 1
  let isHexLine := fun (line : String) => !line.trimAscii.isEmpty &&
    (line.trimAscii.toString.splitOn " ").all fun token => token.length == 2 &&
      token.toList.all fun c => c.isDigit || ('A' ≤ c && c ≤ 'F')
  let body := rest.takeWhile isHexLine
  check s!"empty hex after {marker}" (!body.isEmpty)
  hex (String.join body)

/-- The bytes of a colon-separated octet string that may continue on the next line -/
def octets (text marker : String) : IO ByteArray := do
  let tail ← after text marker
  let joined := String.ofList ((tail.splitOn "\n\n").head!.toList.filter fun c => !c.isWhitespace)
  hex (joined.replace ":" "")

private def toKey (bytes : ByteArray) (label : String) : IO (Vector UInt8 32) := do
  if h : bytes.data.size = 32 then return ⟨bytes.data, h⟩
  throw (IO.userError s!"{label}: expected 32 key bytes, got {bytes.size}")

/-- §2.5.2: the clamped `r`, `s`, the final number, and the tag of the 34-byte message -/
private def example252 (text : String) : IO Unit := do
  let part ← after text "2.5.2.  Poly1305 Example and Test Vector\n"
  let part := (part.splitOn "2.6.  Generating the Poly1305 Key Using ChaCha20").head!
  let key ← toKey (← octets part "Key Material:") "§2.5.2"
  let r := leBytesToNum ⟨key.toArray.extract 0 16⟩
  let s := leBytesToNum ⟨key.toArray.extract 16 32⟩
  let number (marker : String) : IO Nat := do
    let digits := ((← after part marker).trimAscii.toString.splitOn "\n").head!
    check s!"§2.5.2: no number after {marker}" (!digits.trimAscii.isEmpty)
    digits.trimAscii.toString.toList.foldlM (fun value c => return 16 * value + (← hexDigit c)) 0
  check "§2.5.2: clamped r" (clamp r == (← number "Clamped r as a number:"))
  check "§2.5.2: s" (s == (← number "s as a 128-bit number:"))
  let message ← dump (pageLines part) "Message to be Authenticated:"
  check "§2.5.2: 34-byte message" (message.size == 34)
  let tag ← octets part "Tag:"
  expect "§2.5.2: num_to_16_le_bytes of Acc + s" ⟨(numTo16LeBytes (← number "Acc + s =")).toArray⟩
    tag
  expect "§2.5.2: poly1305_mac" ⟨(poly1305Mac message key).toArray⟩ tag

/--
The message lengths in bytes of Appendix A.3's test vectors #1–#11, counted from the printed data:
the RFC prints no lengths, so these pin the parse of each message against truncation
-/
private def appendixLengths : List Nat := [64, 375, 375, 127, 16, 16, 48, 48, 16, 64, 48]

/--
Appendix A.3: test vectors #1–#11, each with its message length counted from the printed data;
returns their number
-/
private def appendix (text : String) : IO Nat := do
  let part ← after text "A.3.  Poly1305 Message Authentication Code\n"
  let part := (part.splitOn "A.4.  Poly1305 Key Generation Using ChaCha20").head!
  let vectors := (part.splitOn "Test Vector #").drop 1
  let mut count := 0
  for vector in vectors do
    let lines := pageLines vector
    let number := (vector.splitOn ":").head!
    let (key, message, tag) ← if vector.contains '=' then do
        pure (← dump lines "One-time Poly1305 Key:", ← dump lines "Text to MAC:",
          ← dump lines "Tag:")
      else do
        let key := (← hexLines lines "R:") ++ (← hexLines lines "S:")
        pure (key, ← hexLines lines "data:", ← hexLines lines "tag:")
    check s!"A.3 #{number}: message length" (some message.size == appendixLengths[count]?)
    expect s!"A.3 #{number}" ⟨(poly1305Mac message (← toKey key s!"A.3 #{number}")).toArray⟩ tag
    count := count + 1
  return count

/--
A Poly1305 computation printed in an AEAD example: the one-time key, the AAD, the ciphertext, the
Poly1305 input the RFC prints (the AAD and ciphertext zero-padded to whole blocks, then their
lengths as eight-byte little-endian numbers), and the tag
-/
structure AeadVector where
  label : String
  key : Vector UInt8 32
  aad : ByteArray
  ciphertext : ByteArray
  macData : ByteArray
  tag : ByteArray

/--
The AEAD examples of §2.8.2 and Appendix A.5, with the AAD, ciphertext, and Poly1305 input sizes
counted from the printed data checked (the RFC prints no sizes)
-/
def aeadVectors (text : String) : IO (List AeadVector) := do
  let part ← after text "2.8.2.  Example and Test Vector for AEAD_CHACHA20_POLY1305\n"
  let lines := pageLines (part.splitOn "3.  Implementation Advice").head!
  let example282 : AeadVector := {
    label := "§2.8.2"
    key := ← toKey (← dump lines "Poly1305 Key:") "§2.8.2"
    aad := ← dump lines "AAD:"
    ciphertext := ← dump lines "Ciphertext:"
    macData := ← dump lines "AEAD Construction for Poly1305:"
    tag := ← octets part "Tag:" }
  let part ← after text "A.5.  ChaCha20-Poly1305 AEAD Decryption\n"
  let lines := pageLines (part.splitOn "Appendix B.  Performance Measurements").head!
  let appendixA5 : AeadVector := {
    label := "A.5"
    key := ← toKey (← dump lines "Poly1305 one-time key:") "A.5"
    aad := ← dump lines "The AAD:"
    ciphertext := ← dump lines "Ciphertext:"
    macData := ← dump lines "Poly1305 Input:"
    tag := ← dump lines "Calculated Tag:" }
  expect "A.5: received tag equals calculated tag" (← dump lines "Received Tag:") appendixA5.tag
  for (vector, sizes) in [(example282, (12, 114, 160)), (appendixA5, (12, 265, 304))] do
    check s!"{vector.label}: AAD, ciphertext, and Poly1305 input sizes"
      ((vector.aad.size, vector.ciphertext.size, vector.macData.size) == sizes &&
        vector.tag.size == 16)
  return [example282, appendixA5]

def run : IO Unit := do
  let text ← IO.FS.readFile "Standards/RFC/ChaCha20Poly1305/Vectors/rfc8439.txt"
  example252 text
  let count ← appendix text
  check s!"A.3: expected 11 test vectors, parsed {count}" (count == 11)
  let vectors ← aeadVectors text
  for vector in vectors do
    expect s!"{vector.label}: poly1305_mac of the Poly1305 input"
      ⟨(poly1305Mac vector.macData vector.key).toArray⟩ vector.tag
  check s!"AEAD examples: expected 2, parsed {vectors.length}" (vectors.length == 2)
  IO.println ("RFC8439: the §2.5.2 example, all 11 Appendix A.3 vectors, and the Poly1305 " ++
    "inputs of the §2.8.2 and A.5 AEAD examples passed")

end Standards.RFC.ChaCha20Poly1305.Tests
