import Standards.RFC.HMAC
import Standards.NIST.SHA2
import Standards.Tests.Utilities

/-!
# RFC 2104 tests

HMAC-SHA-256 against the unmodified RFC 4231 text from https://www.rfc-editor.org/.

| Source             | Vectors | Checks                                     |
| ------------------ | ------- | ------------------------------------------ |
| RFC 4231 §§4.2–4.8 | 7       | HMAC-SHA-256; case 5 truncated to 128 bits |
-/

namespace Standards.RFC.HMAC.Tests

open Standards.Tests Standards.NIST.SHA2 Standards.RFC

def run : IO Unit := do
  let document ← IO.FS.readFile "Standards/RFC/HMAC/Vectors/rfc4231.txt"
  for i in [1:8] do
    let tail ← after document s!"\n4.{i+1}.  Test Case {i}\n"
    let vector := (tail.splitOn (if i < 7 then s!"\n4.{i+2}." else "\n5. ")).head!
    -- The published case 3 omits the equals sign after Key.
    let key ← rfcField vector (if i == 3 then "Key            " else "Key =")
    let message ← rfcField vector "Data ="
    let expected ← rfcField vector "HMAC-SHA-256 ="
    let actual := HMAC.hmac SHA256.hashBytes 64 key message
    expect s!"RFC4231 case {i}" (actual.extract 0 expected.size) expected
  IO.println "RFC4231: all seven HMAC-SHA-256 vectors passed (case 5 truncates to 128 bits)"

end Standards.RFC.HMAC.Tests
