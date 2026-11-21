import Lean.Data.Json
import Standards.Tests.Utilities
import P256.Spec.Ecdsa
import P256.Spec.Ecdh
import P256.Tests.Functions

/-!
# ECDSA tests

The specifications of the ECDSA entry points (`P256.Spec.Ecdsa`) against:

- RFC 6979 §A.2.5, SHA-256 (`Standards/RFC/DeterministicSigning/Vectors/rfc6979.txt`): 1 key,
  2 messages, their `r`, `s`: `Signer::try_sign`, `Verifier::verify`, `Signature::from_slice`.
- `Tests/Generated/D-ecdsa-cases.txt`, from `D-ecdsa-generator.py`, an independent Python
  computation (SEC 1, RFC 6979 §3.2, DER): 5 values; the DER encoding of RFC 6979's `sample`
  signature, which `Signature::from_slice` must reject, and, for recovery IDs 2 and 3, a signature
  `(r, 7)` with `r + n < p` and the key that ID recovers from it, under which `u₁G + u₂Q` has
  `x = r + n`, so `Verifier::verify` accepts the signature only by reducing that `x` mod `n`. Its
  other values, for key recovery, are not checked.
- `Tests/Generated/D-ecdsa-native.txt`, which `D-ecdsa-native-generator/generate.sh` writes byte for
  byte from `D-ecdsa-native-generator/cases.txt` by running each case natively through the wrappers
  (x86-64 Linux, release): its 30 cases of the 5 entry points with a theorem among them,
  `Signer::try_sign`, `Verifier::verify`, `Signature::from_slice`, `SigningKey::generate_from_rng`
  and `ecdh::diffie_hellman`, labelled `host` (a call outside an entry's contract is not in the
  table): a success with its control, each crate failure, a raw signature of 0, 63, 65 and 72
  bytes, with `r` or `s` zero or `n`, all bytes `FF`, and the smallest and largest accepted,
  `r = s = 1` and `r = s = n − 1`, random bytes whose first block is or is not a key, among them a
  zero block then RFC 6979 §A.2.5's key, whose result holds that key's public key, and ECDH with
  the identity and with a compact point; each case meets its entry's argument premise, and each
  `SigningKey::generate_from_rng` case the premise of enough random bytes. Its cases of
  `Signature::from_der` and `VerifyingKey::recover_from_msg` are not checked.
- `Signature::from_slice` on raw `r ‖ s`: RFC 6979 §A.2.5's two signatures, accepted and written
  back unchanged; each rejection, by the crate's docs (64 bytes, ecdsa 0.17.0 `src/lib.rs:207-211`)
  and SEC 1 v2.0 §4.1.4 step 1 (`1 ≤ r, s < n`): 0, 32, 63, 65, 72 (the RFC's `sample` signature,
  DER-encoded) and 128 bytes, `r` or `s` zero, `r` or `s` equal to `n`, `r` of all bytes `FF`, each
  with its control; and the smallest and largest accepted, `r = s = 1` and `r = s = n − 1`. The
  expected values of these checks rest on SEC 1's range and the crate's docs, and the native runs
  above check the same cases against the crate. Wycheproof's raw-signature vectors (next) are
  published signatures of other lengths and with `r` or `s` zero, `n` and above `n`; their verdict
  is that of `from_slice` then `verify`, so on its own it does not say which of the two rejects.
- Wycheproof's raw-signature vectors for P-256 with SHA-256
  (`Tests/Vectors/ecdsa_secp256r1_sha256_p1363_test.json`, unmodified, from
  https://github.com/C2SP/wycheproof/tree/d17cc89fa5c8f4f4d378b5385ebf75da5d0926c9/testvectors_v1):
  262 signatures in IEEE P1363's `r ‖ s` form, the form the crate's `Signature` docs name, under
  111 keys; `Signature::from_slice` then `Verifier::verify`, each valid exactly when the vector is
  (173). `from_slice` writes each signature it accepts back unchanged, and accepts exactly those of
  64 bytes with `1 ≤ r, s < n` (SEC 1 v2.0 §4.1.4 step 1, checked here on each vector's halves):
  191; it rejects the other 71, all invalid vectors, 21 of 2 to 82 bytes and 50 with `r` or `s`
  zero or at least `n`.

The argument checks of the calls (`isVerifyingKey`, `isSignature`) are checked on values they
reject, each with its control. RFC 6979's retry (a candidate `k ≥ n` or a zero `r` or `s`) has no
published P-256 vector; its coverage rests on the shared RFC 6979 specification's own tests.
-/

namespace P256.Tests.Signatures

open Standards.Tests P256.Spec P256.Spec.Ecdsa Standards.SECG.ECC

/-- `result` is exactly the success `expected` -/
def expectOk (label : String) (result : Option ByteArray) (expected : ByteArray) : IO Unit :=
  check label (result == some expected)

/-- `result` is the crate's failure -/
def expectFailure (label : String) (result : Option ByteArray) : IO Unit :=
  check label result.isNone

/-- The first RFC 6979 candidate's result is the signature `expected` -/
def expectSigned (label : String) (result : Option (Option ByteArray)) (expected : ByteArray) :
    IO Unit := check label (result == some (some expected))

private def rfcVectors : IO String := do
  let document ← IO.FS.readFile "Standards/RFC/DeterministicSigning/Vectors/rfc6979.txt"
  return ((← after document "\nA.2.5.  ECDSA, 256 Bits (Prime Field)\n").splitOn "\nA.2.6.").head!

/--
The values of `Tests/Generated/D-ecdsa-cases.txt` (`D-ecdsa-generator.py`) these tests check, by
label: the DER encoding of the `sample` signature, and the signatures and keys with `x = r + n`;
the file's other values are not checked
-/
private def generatedCases : IO (List (String × ByteArray)) := do
  let text ← IO.FS.readFile "P256/Tests/Generated/D-ecdsa-cases.txt"
  let lines := (text.splitOn "\n").filter fun line =>
    let label := (line.splitOn " ").head!
    label == "rfc6979-sample-der" || label.startsWith "recover-small-r-"
  check "D-ecdsa-cases.txt: 5 values" (lines.length == 5)
  lines.mapM fun line => do
    let [label, digits] := line.splitOn " " | throw (IO.userError s!"D-ecdsa-cases.txt: {line}")
    return (label, ← hex digits)

/-- The generated value labelled `label` -/
private def generated (label : String) : IO ByteArray := do
  let some bytes := (← generatedCases).lookup label
    | throw (IO.userError s!"D-ecdsa-cases.txt: no {label}")
  return bytes

/-- RFC 6979 A.2.5 with SHA-256 through the specifications of `try_sign` and `verify` -/
private def rfc6979 : IO Unit := do
  let vectors ← rfcVectors
  let secret ← value vectors "\n   x = "
  let key := ⟨#[4]⟩ ++ (← value vectors "\n   Ux = ") ++ (← value vectors "\n   Uy = ")
  for message in ["sample", "test"] do
    let vector ← after vectors s!"With SHA-256, message = \"{message}\":"
    let signature := (← value vector "\n   r = ") ++ (← value vector "\n   s = ")
    let bytes := message.toUTF8
    expectSigned s!"RFC 6979 {message}: try_sign" (signMessageWithin 1 #[secret, bytes]) signature
    expectOk s!"RFC 6979 {message}: verify" (verifyMessage #[key, signature, bytes])
      ByteArray.empty
    expectFailure s!"RFC 6979 {message} control: another message fails"
      (verifyMessage #[key, signature, "wrong".toUTF8])
  IO.println "RFC 6979 A.2.5: try_sign and verify passed"

/-- The argument checks, each with its control, and `verify` where `u₁G + u₂Q` has `x = r + n` -/
private def rejections : IO Unit := do
  let vectors ← rfcVectors
  let key := ⟨#[4]⟩ ++ (← value vectors "\n   Ux = ") ++ (← value vectors "\n   Uy = ")
  let vector ← after vectors "With SHA-256, message = \"sample\":"
  let signature := (← value vector "\n   r = ") ++ (← value vector "\n   s = ")
  let message := "sample".toUTF8
  check "verifying key: a compressed key is not one" (!isVerifyingKey (⟨#[2]⟩ ++ key.extract 1 33))
  check "verifying key: an off-curve key is not one" (!isVerifyingKey (key.extract 0 64 ++ ⟨#[0]⟩))
  check "verifying key: the identity is not one" (!isVerifyingKey ⟨#[0]⟩)
  check "control: the RFC's key is one" (isVerifyingKey key)
  check "signature: s = 0 is not one"
    (!isSignature (signature.extract 0 32 ++ Encoding.natToOctets 32 0))
  check "signature: r = n is not one"
    (!isSignature (Encoding.natToOctets 32 order ++ signature.extract 32 64))
  check "signature: 63 bytes are not one" (!isSignature (signature.extract 0 63))
  check "control: the RFC's signature is one" (isSignature signature)
  check "try_sign takes a secret key in 1..n"
    (!Functions.admits "signingKeyTrySign" #[Encoding.natToOctets 32 0, message])
  check "control: 1" (Functions.admits "signingKeyTrySign" #[Encoding.natToOctets 32 1, message])
  -- x = r + n under the keys of recovery IDs 2 and 3, from the independent computation
  -- (D-ecdsa-cases.txt): verify must reduce it mod n
  for recoveryId in [2, 3] do
    let small ← generated s!"recover-small-r-id{recoveryId}-signature"
    let recovered ← generated s!"recover-small-r-id{recoveryId}-key"
    expectOk s!"verify: x = r + n under the key of recovery ID {recoveryId}"
      (verifyMessage #[recovered, small, message]) ByteArray.empty
  IO.println "Argument checks, their controls and verify with x = r + n passed"

/--
`Signature::from_slice` on raw `r ‖ s`: the published RFC 6979 §A.2.5 signatures, the length the
crate's docs require (64 bytes) and the range SEC 1 v2.0 §4.1.4 step 1 requires (`1 ≤ r, s < n`),
each rejection with its control, and the smallest and largest accepted values
-/
private def fromSlice : IO Unit := do
  let vectors ← rfcVectors
  for message in ["sample", "test"] do
    let vector ← after vectors s!"With SHA-256, message = \"{message}\":"
    let signature := (← value vector "\n   r = ") ++ (← value vector "\n   s = ")
    check s!"RFC 6979 {message}: r ‖ s is 64 bytes" (signature.size == 64)
    expectOk s!"RFC 6979 {message}: from_slice accepts r ‖ s and writes it back"
      (signatureFromSlice #[signature]) signature
  let vector ← after vectors "With SHA-256, message = \"sample\":"
  let r ← value vector "\n   r = "
  let s ← value vector "\n   s = "
  let zero := Encoding.natToOctets 32 0
  let one := Encoding.natToOctets 32 1
  let n := Encoding.natToOctets 32 order
  let nMinus1 := Encoding.natToOctets 32 (order - 1)
  let ff := Encoding.natToOctets 32 (2 ^ 256 - 1)
  -- length: exactly 64 bytes; the control is the RFC's r ‖ s above
  for bytes in [ByteArray.empty, r, (r ++ s).extract 0 63, r ++ s ++ ⟨#[0]⟩, r ++ s ++ s ++ r] do
    expectFailure s!"from_slice: {bytes.size} bytes are no Signature" (signatureFromSlice #[bytes])
  expectFailure "from_slice: the RFC's 72-byte DER signature is no r ‖ s"
    (signatureFromSlice #[← generated "rfc6979-sample-der"])
  -- range: 1 ≤ r, s < n, each with its control
  expectFailure "from_slice: r = 0" (signatureFromSlice #[zero ++ s])
  expectFailure "from_slice: s = 0" (signatureFromSlice #[r ++ zero])
  expectFailure "from_slice: r = n" (signatureFromSlice #[n ++ s])
  expectFailure "from_slice: s = n" (signatureFromSlice #[r ++ n])
  expectFailure "from_slice: r = 2^256 − 1" (signatureFromSlice #[ff ++ s])
  expectOk "control: r = n − 1 with the RFC's s" (signatureFromSlice #[nMinus1 ++ s]) (nMinus1 ++ s)
  expectOk "control: s = n − 1 with the RFC's r" (signatureFromSlice #[r ++ nMinus1]) (r ++ nMinus1)
  expectOk "control: r = 1 with the RFC's s" (signatureFromSlice #[one ++ s]) (one ++ s)
  expectOk "control: s = 1 with the RFC's r" (signatureFromSlice #[r ++ one]) (r ++ one)
  -- the smallest and largest accepted values
  expectOk "from_slice: r = s = 1" (signatureFromSlice #[one ++ one]) (one ++ one)
  expectOk "from_slice: r = s = n − 1" (signatureFromSlice #[nMinus1 ++ nMinus1])
    (nMinus1 ++ nMinus1)
  IO.println "Signature::from_slice: RFC 6979 signatures, length and the range of r and s passed"

/--
Wycheproof's raw-signature vectors for P-256 with SHA-256 (C2SP/wycheproof `testvectors_v1` at
`d17cc89f`, unmodified): an IEEE P1363 `r ‖ s` signature of a message under a key, which must
verify exactly when the vector is valid, through `Signature::from_slice` then `Verifier::verify`;
a signature `from_slice` rejects counts as not verifying. `from_slice` also writes an accepted
signature back unchanged, and accepts exactly a signature of 64 bytes whose halves, read
big-endian, are in `1..n` (SEC 1 v2.0 §4.1.4 step 1, restated here). The counts are pinned
-/
private def wycheproofP1363 : IO Unit := do
  let text ← IO.FS.readFile "P256/Tests/Vectors/ecdsa_secp256r1_sha256_p1363_test.json"
  let json ← IO.ofExcept (Lean.Json.parse text)
  let field (object : Lean.Json) (key : String) : IO String :=
    IO.ofExcept (object.getObjValAs? String key)
  check "Wycheproof P1363: 262 tests declared"
    ((← IO.ofExcept (json.getObjValAs? Nat "numberOfTests")) == 262)
  let groups ← IO.ofExcept (json.getObjValAs? (Array Lean.Json) "testGroups")
  let mut (seen, valid, accepted, otherLength) := (0, 0, 0, 0)
  for group in groups do
    let publicKey ← IO.ofExcept (group.getObjVal? "publicKey")
    check "Wycheproof P1363: a secp256r1 key and SHA-256"
      ((← field publicKey "curve") == "secp256r1" && (← field group "sha") == "SHA-256")
    let key ← hex (← field publicKey "uncompressed")
    check "Wycheproof P1363: the group's key is a verifying key" (isVerifyingKey key)
    for test in ← IO.ofExcept (group.getObjValAs? (Array Lean.Json) "tests") do
      let id ← IO.ofExcept (test.getObjValAs? Nat "tcId")
      let message ← hex (← field test "msg")
      let signature ← hex (← field test "sig")
      let result ← field test "result"
      check s!"Wycheproof P1363 {id}: valid or invalid" (result == "valid" || result == "invalid")
      let r := Encoding.octetsToNat (signature.extract 0 32)
      let s := Encoding.octetsToNat (signature.extract 32 64)
      let inRange := signature.size == 64 && 1 ≤ r && r < order && 1 ≤ s && s < order
      let mut verified := false
      match signatureFromSlice #[signature] with
      | some fixed =>
        check s!"Wycheproof P1363 {id}: from_slice writes the signature back" (fixed == signature)
        check s!"Wycheproof P1363 {id}: an accepted signature is a Signature argument"
          (isSignature fixed)
        accepted := accepted + 1
        verified := (verifyMessage #[key, fixed, message]).isSome
      | none => pure ()
      check s!"Wycheproof P1363 {id}: from_slice accepts exactly 64 bytes with 1 ≤ r, s < n"
        ((signatureFromSlice #[signature]).isSome == inRange)
      check s!"Wycheproof P1363 {id}, from_slice then verify" (verified == (result == "valid"))
      seen := seen + 1
      if result == "valid" then valid := valid + 1
      if signature.size != 64 then otherLength := otherLength + 1
  check "Wycheproof P1363: 112 groups, 262 vectors, 173 valid, 191 accepted, 21 not 64 bytes"
    (groups.size == 112 && seen == 262 && valid == 173 && accepted == 191 && otherLength == 21)
  IO.println s!"Wycheproof P1363: {seen} vectors passed ({valid} valid, {accepted} accepted)"

/-- The octets of hexadecimal text, `-` for none -/
private def unhexField (text : String) : ByteArray :=
  let digit (c : Char) : Nat := if c.isDigit then c.toNat - 48 else c.toLower.toNat - 87
  let rec go : List Char → List UInt8
    | high :: low :: rest => UInt8.ofNat (16 * digit high + digit low) :: go rest
    | _ => []
  if text == "-" then ByteArray.empty else ⟨(go text.toList).toArray⟩

/--
`Tests/Generated/D-ecdsa-native.txt`: every case of an entry point with a theorem meets its entry's
argument premise and gives the status and result bytes of the native run of the wrapper; the counts
of those cases and their entries are pinned, and the table's other cases are not checked
-/
private def nativeTable : IO Unit := do
  let lines := (← IO.FS.readFile "P256/Tests/Generated/D-ecdsa-native.txt").splitOn "\n" |>.filter
    fun line => !line.startsWith "case " ||
      Functions.all.any fun (entry, _) => line.startsWith s!"case {entry} "
  let mut pool : List (String × ByteArray) := []
  let mut count := 0
  let mut reached : List String := []
  for line in lines do
    match line.splitOn " " with
    | ["input", name, text] => pool := (name, unhexField text) :: pool
    | ["case", entry, names, status, "host", result] =>
      count := count + 1
      let inputs ← (names.splitOn "+").mapM fun name =>
        match pool.lookup name with
        | some bytes => pure bytes
        | none => throw (IO.userError s!"D-ecdsa-native.txt: unknown input {name}")
      check s!"{entry} on {names}: the arguments meet its premise"
        (Functions.admits entry inputs.toArray)
      if entry == "signingKeyGenerateFromRng" then
        check s!"{entry} on {names}: enough random bytes"
          (Ecdh.hasRandomNonZeroScalar inputs.toArray)
      let got := match Functions.model entry inputs.toArray with
        | some (some bytes) => some (0, bytes)
        | some none => some (1, ByteArray.empty)
        | none => none
      check s!"{entry} on {names} (host)" (got == some (status.toNat!, unhexField result))
      if !reached.contains entry then reached := entry :: reached
    | [""] => pure ()
    | _ => throw (IO.userError s!"D-ecdsa-native.txt: bad line {line}")
  check "D-ecdsa-native.txt: 30 cases, 5 entries with a theorem"
    (count == 30 && reached.length == 5)
  IO.println s!"D-ecdsa-native.txt: {count} native wrapper cases passed"

/-- Runs this module's tests, throwing on the first failure -/
def run : IO Unit := do
  nativeTable
  rfc6979
  rejections
  fromSlice
  wycheproofP1363

end P256.Tests.Signatures
