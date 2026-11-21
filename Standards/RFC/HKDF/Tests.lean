import Lean.Data.Json
import Standards.RFC.HKDF
import Standards.Tests.Utilities

/-!
# RFC 5869 tests

HKDF at SHA-256 against the unmodified RFC 5869 text from https://www.rfc-editor.org/ and the
unmodified Wycheproof file from
https://github.com/C2SP/wycheproof/tree/d17cc89fa5c8f4f4d378b5385ebf75da5d0926c9/testvectors_v1.

| Source              | Vectors     | Checks                                                     |
| ------------------- | ----------- | ---------------------------------------------------------- |
| RFC 5869, A.1–A.3   | 3           | SHA-256 PRK and OKM                                        |
| Wycheproof SHA-256  | 86          | OKM; 3 invalid, each above the limit of 255 * HashLen      |
| Length boundary     | SHA-256     | zero length; the limit; first length past the limit        |
-/

namespace Standards.RFC.HKDF.Tests

open Standards.Tests

/-- One `= 0x…` field of an RFC 5869 test case, empty for `(0 octets)` -/
private def octets (testCase marker : String) : IO ByteArray := do
  let tail := (← after testCase marker).trimAscii.toString
  if tail.startsWith "(0 octets)" then return ByteArray.empty
  rfcField ("=" ++ (tail.drop 2).toString) "="

private def rfcVectors : IO Unit := do
  let document ← IO.FS.readFile "Standards/RFC/HKDF/Vectors/rfc5869.txt"
  for i in [1:4] do
    let tail ← after document s!"\nA.{i}.  Test Case {i}\n"
    let testCase := (tail.splitOn s!"\nA.{i+1}.").head!
    check s!"RFC5869 A.{i} hash" ((testCase.splitOn "Hash = SHA-256").length == 2)
    let ikm ← octets testCase "IKM  = "
    let salt ← octets testCase "salt = "
    let info ← octets testCase "info = "
    let prk ← octets testCase "PRK  = "
    let okm ← octets testCase "OKM  = "
    expect s!"RFC5869 A.{i} PRK" (extract .sha256 salt ikm) prk
    expectSome s!"RFC5869 A.{i} OKM" (expand .sha256 prk info okm.size) okm
  IO.println "RFC5869 A.1-A.3: all three SHA-256 cases passed"

private def wycheproof (H : Hash) (name : String) (count : Nat) : IO Unit := do
  let text ← IO.FS.readFile s!"Standards/RFC/HKDF/Vectors/hkdf_{name}_test.json"
  let json ← IO.ofExcept (Lean.Json.parse text)
  let field (object : Lean.Json) (key : String) : IO String :=
    IO.ofExcept (object.getObjValAs? String key)
  let groups ← IO.ofExcept (json.getObjValAs? (Array Lean.Json) "testGroups")
  let mut (seen, invalid) := (0, 0)
  for group in groups do
    for test in ← IO.ofExcept (group.getObjValAs? (Array Lean.Json) "tests") do
      let id ← IO.ofExcept (test.getObjValAs? Nat "tcId")
      let size ← IO.ofExcept (test.getObjValAs? Nat "size")
      let ikm ← hex (← field test "ikm")
      let salt ← hex (← field test "salt")
      let info ← hex (← field test "info")
      let okm ← hex (← field test "okm")
      let actual := expand H (extract H salt ikm) info size
      seen := seen + 1
      if (← field test "result") == "valid" then
        expectSome s!"Wycheproof {name} {id}" actual okm
      else
        invalid := invalid + 1
        check s!"Wycheproof {name} {id} rejected" (actual.isNone && size > 255 * H.hashLen)
  check s!"Wycheproof {name} count" (seen == count && invalid == 3)
  IO.println s!"Wycheproof HKDF {name}: {seen} vectors passed, {invalid} of them invalid"

private def lengthBoundary (H : Hash) : IO Unit := do
  let prk := ByteArray.mk (Array.replicate H.hashLen 7)
  expectSome "Zero length" (expand H prk .empty 0) .empty
  check "Length limit" (((expand H prk .empty (255 * H.hashLen)).map (·.size)) ==
    some (255 * H.hashLen))
  check "First rejected length" (expand H prk .empty (255 * H.hashLen + 1)).isNone

def run : IO Unit := do
  rfcVectors
  wycheproof .sha256 "sha256" 86
  lengthBoundary .sha256
  IO.println "HKDF length boundaries passed"

end Standards.RFC.HKDF.Tests
