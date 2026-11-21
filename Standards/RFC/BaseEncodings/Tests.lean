import Standards.RFC.BaseEncodings
import Standards.Tests.Utilities

/-!
# RFC 4648 tests

Base 16 against the unmodified RFC 4648 text from https://www.rfc-editor.org/. Unpadded and
lowercase expectations are derived from the published ones by removing `=` (§3.2) or lowering
letters (§3.4).

| Source      | Vectors | Checks                                                                |
| ----------- | ------- | --------------------------------------------------------------------- |
| Tables      | 1       | alphabets equal Table 5 (also lowercased)                             |
| §10 BASE16  | 7       | upper- and lowercase encode; upper, lower, and mixed-case decode      |
| Synthetic   | —       | bad characters, bad padding, bad lengths                              |
| Synthetic   | —       | round trips                                                           |
-/

namespace Standards.RFC.BaseEncodings.Tests

open Standards.Tests

private def ascii (text : String) : ByteArray := text.toUTF8

private def text (bytes : ByteArray) : String := String.fromUTF8! bytes

private def withoutPad (text : String) : String := String.ofList (text.toList.filter (· != '='))

private def readDocument : IO String :=
  IO.FS.readFile "Standards/RFC/BaseEncodings/Vectors/rfc4648.txt"

/-- The §10 lines `   NAME("input") = "output"`, as `(input, output)` -/
private def sectionTenVectors (document name : String) : IO (List (String × String)) := do
  let section10 := ((← after document "\n10.  Test Vectors\n").splitOn "\n11.  ").head!
  let prefix_ := s!"   {name}(\""
  let lines := (section10.splitOn "\n").filter (·.startsWith prefix_)
  let vectors ← lines.mapM fun line => do
    match ((line.drop prefix_.length).toString.splitOn "\") = \"") with
    | [input, output] => pure (input, (output.dropEnd 1).toString)
    | _ => throw (IO.userError s!"Malformed RFC 4648 vector: {line}")
  check s!"RFC4648 §10 {name}: seven vectors" (vectors.length == 7)
  pure vectors

/-- `(value, character)` pairs of a table row such as `   62 - (minus)   (pad) =` -/
private def rowEntries : List String → List (Nat × String)
  | value :: character :: rest =>
    if value.all Char.isDigit && character.length == 1 then
      (value.toNat!, character) :: rowEntries rest
    else
      rowEntries (character :: rest)
  | _ => []

/-- The characters of the table titled `title`, in value order -/
private def rfcTable (document title : String) : IO (List UInt8) := do
  let lines := ((← after document s!"{title}\n").splitOn "\n").takeWhile fun line =>
    line.isEmpty || line.startsWith "    "
  let entries := lines.flatMap fun line =>
    rowEntries ((line.splitOn " ").filter (!·.isEmpty))
  (List.range entries.length).mapM fun value =>
    match entries.find? (·.1 == value) with
    | some (_, character) => pure character.toList.head!.toUInt8
    | none => throw (IO.userError s!"{title}: no character for value {value}")

private def alphabetTables (document : String) : IO Unit := do
  let base16 ← rfcTable document "Table 5: The Base 16 Alphabet"
  let tables := [
    ("base16Upper", Alphabet.base16Upper, base16),
    ("base16Lower", .base16Lower,
      base16.map fun c => if 'A'.toUInt8 ≤ c && c ≤ 'Z'.toUInt8 then c + 0x20 else c)]
  for (name, alphabet, table) in tables do
    check s!"{name} is its RFC 4648 table" (alphabet.characters == table)
  IO.println "RFC4648 Table 5: alphabets match"

/-- Encoding and decoding `input` as `expected`, padded and with the pad characters removed -/
private def checkVector (label : String) (alphabet : Alphabet) (input : ByteArray)
    (expected : String) : IO Unit := do
  for (padding, encoded) in [(Padding.padded, expected), (.unpadded, withoutPad expected)] do
    let label := s!"{label} {repr padding}"
    check s!"{label} encode" (text (encode alphabet padding input) == encoded)
    expectSome s!"{label} decode" (decode alphabet padding (ascii encoded)) input
    expectSome s!"{label} decodeIgnoringCase"
      (decodeIgnoringCase alphabet padding (ascii encoded)) input
  if expected.contains '=' then
    check s!"{label}: padded data rejected when unpadded"
      (decode alphabet .unpadded (ascii expected) == none)
    check s!"{label}: unpadded data rejected when padded"
      (decode alphabet .padded (ascii (withoutPad expected)) == none)

private def base16Vectors (document : String) : IO Unit := do
  for (input, expected) in ← sectionTenVectors document "BASE16" do
    let lower := expected.toLower
    let mixed := String.ofList (expected.toList.zipIdx.map fun (c, i) =>
      if i % 2 == 0 then c else c.toLower)
    checkVector s!"BASE16(\"{input}\")" .base16Upper (ascii input) expected
    checkVector s!"base16 lower(\"{input}\")" .base16Lower (ascii input) lower
    for encoded in [expected, lower, mixed] do
      for alphabet in [Alphabet.base16Upper, .base16Lower] do
        expectSome s!"BASE16(\"{input}\") {encoded} decodeIgnoringCase"
          (decodeIgnoringCase alphabet .padded (ascii encoded)) (ascii input)
    if lower != expected then
      check s!"BASE16(\"{input}\") lowercase rejected by Table 5"
        (decode .base16Upper .padded (ascii lower) == none)
      check s!"BASE16(\"{input}\") uppercase rejected by the lowercase alphabet"
        (decode .base16Lower .padded (ascii expected) == none)
    if mixed != expected && mixed != lower then
      check s!"BASE16(\"{input}\") mixed case rejected by either single case"
        (decode .base16Upper .padded (ascii mixed) == none &&
          decode .base16Lower .padded (ascii mixed) == none)
  IO.println "RFC4648 §10: base 16 vectors passed"

/-- Data that every decoder rejects, under both padding choices unless `padding` is given -/
private def rejected : List (Alphabet × Option Padding × String) := [
  -- Characters outside the alphabet (§3.3), line feeds (§3.1) included
  (.base16Upper, none, "6G"), (.base16Upper, none, "6\n6F"), (.base16Upper, none, "66 "),
  (.base16Upper, none, "66=="), (.base16Lower, none, "6g"),
  -- Numbers of characters that no input encodes to (§§4, 6, 8)
  (.base16Upper, none, "666"), (.base16Lower, none, "6")
]

/-- Data with a single octet 0x80 or above, outside every alphabet (§3.3) -/
private def rejectedOctets : List (Alphabet × Option Padding × ByteArray) := [
  (.base16Upper, none, ⟨#[0x36, 0xb6]⟩), (.base16Lower, none, ⟨#[0x80, 0x36]⟩)
]

private def negative : IO Unit := do
  let cases := rejected.map (fun (a, p, e) => (a, p, ascii e)) ++ rejectedOctets
  for (alphabet, padding?, encoded) in cases do
    for padding in padding?.elim [Padding.padded, .unpadded] ([·]) do
      let label := s!"{repr encoded.data} {repr padding}"
      check s!"{label}: decode rejects" (decode alphabet padding encoded == none)
      check s!"{label}: decodeIgnoringCase rejects"
        (decodeIgnoringCase alphabet padding encoded == none)
  IO.println "RFC4648: bad characters, padding, and lengths rejected"

private def alphabets : List (String × Alphabet) :=
  [("base16Upper", .base16Upper), ("base16Lower", .base16Lower)]

/-- Round trips over inputs of every length up to 40 -/
private def properties : IO Unit := do
  for (name, alphabet) in alphabets do
    for padding in [Padding.padded, .unpadded] do
      for length in [0:41] do
        let input : ByteArray := ⟨(Array.range length).map fun i => UInt8.ofNat (151 * i + 7)⟩
        let encoded := encode alphabet padding input
        let label := s!"{name} {repr padding} length {length}"
        expectSome s!"{label} round trip" (decode alphabet padding encoded) input
        expectSome s!"{label} round trip ignoring case"
          (decodeIgnoringCase alphabet padding encoded) input
        if padding == .padded then
          check s!"{label} whole quanta" (encoded.size % alphabet.quantum == 0)
  IO.println "RFC4648: round trips passed"

def run : IO Unit := do
  let document ← readDocument
  alphabetTables document
  base16Vectors document
  negative
  properties

end Standards.RFC.BaseEncodings.Tests
