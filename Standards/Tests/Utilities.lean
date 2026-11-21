/-!
# Test utilities

Checks and hex and RFC-text parsers shared by the `Standards` and crate tests. `rustByteString`
reads the byte string literals of Rust test files, whose escapes the Rust Reference defines.

Source: https://doc.rust-lang.org/reference/tokens.html#byte-string-literals
-/

namespace Standards.Tests

def check (label : String) (condition : Bool) : IO Unit := do
  unless condition do throw (IO.userError label)

def hexDigit (c : Char) : IO Nat := do
  if '0' ≤ c && c ≤ '9' then return c.toNat - '0'.toNat
  if 'A' ≤ c && c ≤ 'F' then return c.toNat - 'A'.toNat + 10
  if 'a' ≤ c && c ≤ 'f' then return c.toNat - 'a'.toNat + 10
  throw (IO.userError s!"Invalid hex digit: {c}")

def hex (input : String) : IO ByteArray := do
  let chars := (input.toList.filter fun c => !c.isWhitespace).toArray
  check "Odd hex length" (chars.size % 2 == 0)
  let mut bytes := ByteArray.empty
  for i in [:chars.size / 2] do
    bytes := bytes.push (UInt8.ofNat (16 * (← hexDigit chars[2*i]!) + (← hexDigit chars[2*i+1]!)))
  return bytes

def after (input marker : String) : IO String := do
  match input.splitOn marker with
  | _ :: rest :: _ => return rest
  | _ => throw (IO.userError s!"Missing vector marker: {marker}")

def value (input marker : String) : IO ByteArray := do
  let tail := (← after input marker).trimAscii.toString
  hex ((tail.splitOn "\n").head!)

def expect (label : String) (actual expected : ByteArray) : IO Unit :=
  check s!"{label}: byte mismatch" (actual == expected)

def expectSome (label : String) (actual : Option ByteArray) (expected : ByteArray) : IO Unit :=
  check s!"{label}: result mismatch" (actual == some expected)

private def isHex (c : Char) : Bool :=
  ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

def rfcField (input marker : String) : IO ByteArray := do
  let tail ← after input marker
  let mut text := ""
  for line in tail.trimAscii.toString.splitOn "\n" do
    let token := (line.trimAscii.toString.splitOn " ").head!
    if token.isEmpty || !token.toList.all isHex then break
    text := text ++ token
  check s!"Missing RFC hex field: {marker}" (!text.isEmpty)
  hex text

/--
The whitespace-separated two-digit hex tokens that follow `marker`, across lines, up to the first other
token, skipping the page footers and headers of an RFC text
-/
def rfcHexTokens (input marker : String) : IO ByteArray := do
  let tail ← after input marker
  let mut text := ""
  for line in tail.splitOn "\n" do
    if (line.splitOn "[Page ").length > 1 || line.startsWith "RFC " || line.startsWith "\x0c" then
      continue
    let tokens := line.trimAscii.toString.splitOn " " |>.filter (· ≠ "")
    let pair := tokens.span fun token => token.length == 2 && token.toList.all isHex
    text := text ++ String.join pair.1
    unless pair.2.isEmpty do break
  check s!"Missing RFC hex tokens: {marker}" (!text.isEmpty)
  hex text

/--
The bytes of the body of a Rust byte string literal `b"…"`, starting just after the opening quote:
plain characters, the escapes `\xHH`, `\0`, `\n`, `\r`, `\t`, `\\`, `\"` and `\'`, and a
backslash at the end of a line, which skips the line break and the next line's leading whitespace.
Returns the bytes and the characters after the closing quote.
-/
partial def rustByteString (chars : List Char) (bytes : ByteArray := .empty) :
    IO (ByteArray × List Char) :=
  match chars with
  | '"' :: rest => pure (bytes, rest)
  | '\\' :: 'x' :: high :: low :: rest => do
    rustByteString rest (bytes.push (UInt8.ofNat (16 * (← hexDigit high) + (← hexDigit low))))
  | '\\' :: '\n' :: rest => rustByteString (rest.dropWhile Char.isWhitespace) bytes
  | '\\' :: c :: rest => do
    let byte ← match c with
      | '0' => pure 0 | 'n' => pure 10 | 'r' => pure 13 | 't' => pure 9
      | '\\' => pure 92 | '"' => pure 34 | '\'' => pure 39
      | _ => throw (IO.userError s!"Unsupported Rust escape: \\{c}")
    rustByteString rest (bytes.push byte)
  | c :: rest => rustByteString rest (bytes.push c.toNat.toUInt8)
  | [] => throw (IO.userError "Unterminated Rust byte string")

/--
The `TestVector { raw: b"…", b64: "…" }` entries of a Rust test file, in order, as `(raw, b64)`
-/
def rustTestVectors (source : String) : IO (List (ByteArray × String)) :=
  ((source.splitOn "TestVector {").drop 1).mapM fun entry => do
    let (raw, rest) ← rustByteString (← after entry "raw: b\"").toList
    let text := (← after (String.ofList rest) "b64: \"").takeWhile (· != '"')
    pure (raw, text.toString)

end Standards.Tests
