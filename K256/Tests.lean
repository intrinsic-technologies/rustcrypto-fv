import K256.Spec.Secp256k1
import K256.Spec.Ecdsa
import Standards.Tests.Utilities

/-!
# `k256` tests

Executable checks of the specification against published test vectors and the real crate, run
by `cd K256 && lake test`: `K256` is its own Lake package, which the repository root's `lake test`
does not run. The crate's vector files are kept unmodified under `K256/Tests/Vectors/`, at their
paths under k256 0.14.0's `src/`; `K256/Tests/Generated/vectors.txt` holds values the real crate
computes on the host, written by `K256/Tests/Generated/generate-vectors` (its `main.rs` says how).
These tests import the specifications only, not the program image.

| Source                                   | Vectors       | Checks                                       |
| ---------------------------------------- | ------------- | -------------------------------------------- |
| k256 0.14.0 `src/test_vectors/group.rs`  | 45 points `kG` | public keys, ECDH with `G`                  |
| k256 0.14.0 `src/test_vectors/ecdsa.rs`  | 1 signature   | ECDSA with the vector's nonce, verification  |
| k256 0.14.0 `src/ecdsa.rs`               | 2 normalizations | low-`s` normalization                     |
| k256 0.14.0 `src/test_vectors/data/wycheproof-p1316.blb` | 208 | `from_slice`, low `s`, `verify`     |
| `Tests/Generated/vectors.txt` (crate)    | 670 calls     | the result of every entry point with a theorem, exactly |
| `Tests/Generated/low-s-bound.txt` (OpenSSL, BIP 62) | 4 signatures | `verify` at the low-`s` bound, exactly |
| python-ecdsa 0.19.2 tests (secondary)    | 6 nonces      | RFC 6979 nonces, `Ecdsa.signature` with them |
| Synthetic                                | —             | boundaries, rejections and their controls    |

No standards body publishes a vector that signs a SHA-256 digest of a message on secp256k1 with RFC
6979 nonces. The python-ecdsa library's tests publish six such nonces (`rfc6979Nonces`), a secondary
source: the specification's first nonce candidate equals each, and `Ecdsa.signature` is the low-`s`
SEC 1 signature made with it.

`vectors.txt` also holds inputs built to reach each branch of the crate's own specification code:
ECDH with the identity and a compact point (`Secp256k1.sharedSecret`), SEC 1's hybrid tags `06` and
`07` and coordinates equal to `p`, which `from_sec1_bytes` refuses, and, for `Signature::from_slice`
(`Ecdsa.signatureScalars`), each way it refuses bytes, beside a control it accepts: another length,
`r` or `s` of 0, `r` or `s` of `n` or `2^256 − 1`, and `r` and `s` of `n − 1`, the largest accepted,
then the signatures of Wycheproof's 208 P1363 vectors, whose own verdicts `wycheproof` checks
(`fromSliceVectors` pins how often each reason is reached).

Elsewhere, `verify`'s specification sees BIP 62's bound `s = ⌊n / 2⌋` only in Wycheproof vector 131,
and `s = ⌊n / 2⌋ + 1` never: the crate's high-`s` forms in `vectors.txt` are `n − s` of a low `s`,
and the Wycheproof test normalizes `s` before verifying, so vector 132, whose `s` is
`⌊n / 2⌋ + 1`, reaches it as `⌊n / 2⌋`. `low-s-bound.txt` holds four SEC 1 signatures built at the
bound by choosing the key (`low-s-bound.py`): `s = ⌊n / 2⌋`, which `verify` accepts, and
`s = ⌊n / 2⌋ + 1`, which it refuses, each also in its form `n − s` under the same key, which swaps
the two. Their expected statuses come from OpenSSL's SEC 1 verdict and BIP 62's published bound,
not from the specification or the crate.

One part of the specification agrees with a simpler specification on every input anyone can build,
so no test can tell them apart, and only a proof ties it to the code: `Ecdsa.signature` searches up
to `2^512` RFC 6979 candidates; on every input here, and on every input anyone knows how to build,
the first candidate signs, so a specification making one attempt gives the same signatures.

Two checks are properties of the specification's own output, with no outside value to compare: the
low `s` of `Ecdsa.signature` and its search succeeding within ten candidates (`synthetic`). Every
other expected value comes from a published vector, the real crate, OpenSSL, or a constant the
standard states.
-/

namespace K256.Tests

open Standards.Tests Standards.SECG.ECC Standards.SECG.DomainParameters Standards.NIST.SHA2
open K256.Spec

private def scalarBytes (value : Nat) : ByteArray := Encoding.natToOctets 32 value

private def zeros (count : Nat) : ByteArray := ⟨Array.replicate count 0⟩

/-- The hex strings of the `hex!("…")` literals in a Rust source, in order, blanks removed -/
private def hexLiterals (source : String) : IO (List ByteArray) :=
  ((source.splitOn "hex!(").drop 1).mapM fun tail => do
    let literal := ((tail.splitOn ")").head!).replace "\"" ""
    hex (String.ofList (literal.toList.filter fun c => c.isDigit ||
      ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')))

/-- The uncompressed SEC 1 encoding of a point -/
private def uncompressed (point : Curve.Point) : ByteArray :=
  Points.encodePoint Secp256k1.domain false point

/--
The wrapper's status and output for a specification result: 0 and the bytes, or 1 and nothing
-/
private def statusOf : Option ByteArray → String × ByteArray
  | some bytes => ("0", bytes)
  | none => ("1", ByteArray.empty)

/-- A verdict as the wrapper's status: 0 for valid, 1 for invalid -/
private def verdict (valid : Bool) : String × ByteArray :=
  (if valid then "0" else "1", ByteArray.empty)

/-- The specification's status and output for one generated call -/
private def model (entry : String) (inputs : List ByteArray) : Option (String × ByteArray) :=
  match entry, inputs with
  | "signing_key_try_sign", [secret, message] => some ("-", Ecdsa.signature secret message)
  | "verifying_key_verify", [publicKey, message, signature] =>
    some (verdict (Ecdsa.verifies publicKey message signature))
  | "signature_from_slice", [bytes] =>
    some (statusOf ((Ecdsa.signatureScalars bytes).map fun (r, s) => Ecdsa.signatureBytes r s))
  | "ecdh_diffie_hellman", [secret, publicKey] =>
    some ("-", Secp256k1.sharedSecret secret publicKey)
  | "public_key_from_sec1_bytes", [bytes] =>
    some (statusOf ((Secp256k1.decodePublicKey bytes).map uncompressed))
  | "signing_key_generate_from_rng", [random] =>
    (Secp256k1.randomSecret random).map fun _ => ("-", Secp256k1.generatedSigningKey random)
  | _, _ => none

/--
Lines per entry point with a theorem in `vectors.txt`, pinned so a truncated file fails; the
file's lines for the other entry points are not checked
-/
private def lineCounts : List (String × Nat) := [
  ("ecdh_diffie_hellman", 120), ("public_key_from_sec1_bytes", 69), ("signature_from_slice", 235),
  ("signing_key_generate_from_rng", 6), ("signing_key_try_sign", 60), ("verifying_key_verify", 180)]

/-- Hex, with `-` for empty -/
private def field (text : String) : IO ByteArray :=
  if text == "-" then pure ByteArray.empty else hex text

/--
Every generated call of an entry point with a theorem, against the specification: exact status and
bytes
-/
private def generated : IO Unit := do
  let document ← IO.FS.readFile "K256/Tests/Generated/vectors.txt"
  let lines := (document.splitOn "\n").filter fun line =>
    lineCounts.any fun (entry, _) => line.startsWith (entry ++ " ")
  for (entry, count) in lineCounts do
    check s!"vectors.txt: {count} lines of {entry}"
      ((lines.filter fun line => line.startsWith (entry ++ " ")).length == count)
  for line in lines do
    let words := line.splitOn " "
    let entry := words.head!
    let inputs ← (words.drop 1 |>.take (words.length - 3)).mapM field
    let status := words[words.length - 2]!
    let output ← field words.getLast!
    match model entry inputs with
    | some (expectedStatus, expected) =>
      check s!"crate: {(line.take 60).toString}" (status == expectedStatus && output == expected)
    | none => throw (IO.userError s!"vectors.txt: no specification for {(line.take 60).toString}")
  IO.println s!"k256 crate values: {lines.length} calls of the {lineCounts.length} entry points \
    with a theorem match the specification"

/-- k256's group vectors: `kG` for `k` from 1 to 20, and 25 products -/
private def groupVectors : IO Unit := do
  let source ← IO.FS.readFile "K256/Tests/Vectors/test_vectors/group.rs"
  let additions ← hexLiterals ((source.splitOn "pub const MUL_TEST_VECTORS").head!)
  let products ← hexLiterals (← after source "pub const MUL_TEST_VECTORS")
  let rec pairs : List ByteArray → List (ByteArray × ByteArray)
    | x :: y :: rest => (x, y) :: pairs rest
    | _ => []
  let rec triples : List ByteArray → List (ByteArray × ByteArray × ByteArray)
    | k :: x :: y :: rest => (k, x, y) :: triples rest
    | _ => []
  let multiples := (pairs additions).zipIdx.map fun ((x, y), i) => (scalarBytes (i + 1), x, y)
  let vectors := multiples ++ triples products
  check "group.rs: 20 multiples of G" (multiples.length == 20)
  check "group.rs: 45 vectors" (vectors.length == 45)
  let generator := Points.encodePoint Secp256k1.domain true Secp256k1.domain.G
  for (k, x, y) in vectors do
    let point := Curve.Point.affine (Encoding.octetsToNat x) (Encoding.octetsToNat y)
    expect "group.rs: public key of k" (Secp256k1.publicKeyOf k) (⟨#[4]⟩ ++ x ++ y)
    expect "group.rs: ECDH of k with G" (Secp256k1.sharedSecret k generator) x
    expectSome "group.rs: the point decodes from SEC 1"
      ((Secp256k1.decodePublicKey (Points.encodePoint Secp256k1.domain true point)).map
        uncompressed) (⟨#[4]⟩ ++ x ++ y)
  IO.println "k256 group vectors: 45 public keys and ECDH passed"

/-- k256's ECDSA vector and its normalization vectors -/
private def ecdsaVectors : IO Unit := do
  let source ← IO.FS.readFile "K256/Tests/Vectors/test_vectors/ecdsa.rs"
  let some [d, qx, qy, k, m, r, s] := some ((← hexLiterals source).take 7)
    | throw (IO.userError "ecdsa.rs vector")
  let point := Curve.Point.affine (Encoding.octetsToNat qx) (Encoding.octetsToNat qy)
  expect "ecdsa.rs: public key" (Secp256k1.publicKeyOf d) (uncompressed point)
  check "ecdsa.rs: SEC 1 signature with the vector's nonce"
    (ECDSA.signWithNonce Secp256k1.domain (Encoding.octetsToNat d) (Encoding.octetsToNat k) m ==
      some (Encoding.octetsToNat r, Encoding.octetsToNat s))
  check "ecdsa.rs: the vector's s is low, so low-s normalization keeps it"
    (Ecdsa.normalizeS (Encoding.octetsToNat r) (Encoding.octetsToNat s) == r ++ s)
  check "ecdsa.rs: SEC 1 verification of the prehash"
    (ECDSA.verifyDigest Secp256k1.domain point m (Encoding.octetsToNat r, Encoding.octetsToNat s))
  let crateTests ← IO.FS.readFile "K256/Tests/Vectors/ecdsa.rs"
  let normalize := ((← after crateTests "fn s_high()").splitOn "fn s_low()").head!
  let byteOf := fun (b : String) =>
    let digits := (b.trimAscii.toString.drop 2).toString.toList
    digits.foldl (fun v c => v * 16 + (if c.isDigit then c.toNat - 48 else c.toLower.toNat - 87)) 0
  let bytes := ((normalize.splitOn "[").drop 1).map fun list =>
    (((list.splitOn "]").head!.splitOn ",").filter (·.trimAscii.toString.startsWith "0x")).map
      fun b => (byteOf b).toUInt8
  let some [high, low] := some (bytes.take 2) | throw (IO.userError "normalize vectors")
  let some (r, s) := Ecdsa.signatureScalars ⟨high.toArray⟩
    | throw (IO.userError "normalize vector scalars")
  expect "ecdsa.rs: low-s normalization of the high-s vector" (Ecdsa.normalizeS r s) ⟨low.toArray⟩
  let lowList := ((← after (← after crateTests "fn s_low()") "try_from([").splitOn "]").head!
  let lowBytes := ((lowList.splitOn ",").map (·.trimAscii.toString)).filter (!·.isEmpty)
  let lowVector : ByteArray := ⟨(lowBytes.map fun b => b.toNat!.toUInt8).toArray⟩
  check "ecdsa.rs: the s_low vector has 64 bytes" (lowVector.size == 64)
  let some (r, s) := Ecdsa.signatureScalars lowVector
    | throw (IO.userError "s_low vector scalars")
  expect "ecdsa.rs: low-s normalization keeps the low-s vector" (Ecdsa.normalizeS r s) lowVector
  IO.println "k256 ECDSA vectors: signing, verification, 2 normalizations passed"

open Standards.RFC.DeterministicSigning in
/--
python-ecdsa's RFC 6979 nonces on secp256k1 with SHA-256, a secondary source (a library's tests, not
a standards body's): `src/ecdsa/test_pyecdsa.py` at the tag `python-ecdsa-0.19.2`, class `RFC6979`,
`test_SECP256k1` to `test_SECP256k1_6` (lines 1950-2015; the file's SHA-256 begins `db3a167d1ff1`),
https://github.com/tlsfuzzer/python-ecdsa/blob/python-ecdsa-0.19.2/src/ecdsa/test_pyecdsa.py#L1950,
copied here as the secret `d`, the message whose SHA-256 digest is signed, and the expected nonce
`k` that `rfc6979.generate_k` returns. The specification's first candidate must be `k` (RFC 6979
§3.2), and `Ecdsa.signature` the low-`s` SEC 1 signature with that `k`.
-/
private def rfc6979Nonces : IO Unit := do
  let n := Secp256k1.domain.n
  let vectors : List (Nat × String × Nat) := [
    (0x9d0219792467d7d37b4d43298a7d0c05, "sample",
      0x8fa1f95d514760e498f28957b824ee6ec39ed64826ff4fecc2b5739ec45b91cd),
    (0xcca9fbcc1b41e5a95d369eaa6ddcff73b61a4efaa279cfc6567e8daa39cbaf50, "sample",
      0x2df40ca70e639d89528a6b670d9d48d9165fdc0febc0974056bdce192b8e16a3),
    (0x1, "Satoshi Nakamoto",
      0x8F8A276C19F4149656B280621E358CCE24F5F52542772691EE69063B74F15D15),
    (0x1, "All those moments will be lost in time, like tears in rain. Time to die...",
      0x38AA22D72376B4DBC472E06C3BA403EE0A394DA63FC58D88686C611ABA98D6B3),
    (0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364140, "Satoshi Nakamoto",
      0x33A19B60E25FB6F4435AF53A3D42D493644827367E6453928554F43E49AA6F90),
    (0xF8B8AF8CE3C7CCA5E300D33939540C10D45CE001B8F252BFBC57BA0342904181, "Alan Turing",
      0x525A82B70E67874398067543FD84C83D30C175FDC45FDEEE082FE13B1D7CFDF1)]
  check "python-ecdsa: 6 secp256k1 vectors" (vectors.length == 6)
  for ((d, message, k), i) in vectors.zipIdx do
    let digest := SHA256.hashBytes message.toUTF8
    let (first, _) := Nonce.candidate SHA256.hashBytes 64 32 n
      (Nonce.initialState SHA256.hashBytes 64 32 n d digest)
    check s!"python-ecdsa vector {i + 1}: the first RFC 6979 nonce candidate" (first == k)
    let some (r, s) := ECDSA.signWithNonce Secp256k1.domain d k digest
      | throw (IO.userError s!"python-ecdsa vector {i + 1}: no signature with its nonce")
    expect s!"python-ecdsa vector {i + 1}: try_sign's signature is the one with that nonce"
      (Ecdsa.signature (scalarBytes d) message.toUTF8) (Ecdsa.normalizeS r s)
  IO.println "python-ecdsa secp256k1 RFC 6979 vectors: 6 nonces and signatures passed"

/-- Reads a `blobby` variable-length quantity: big-endian 7-bit groups, continuations adding one -/
private def readVlq (data : ByteArray) (position : Nat) : Nat × Nat := Id.run do
  let mut position := position
  let mut byte := data.get! position
  let mut value := (byte &&& 0x7f).toNat
  position := position + 1
  for _ in [0:3] do
    if byte &&& 0x80 == 0 then break
    byte := data.get! position
    value := ((value + 1) <<< 7) + (byte &&& 0x7f).toNat
    position := position + 1
  return (value, position)

/--
The blobs of a `blobby` file, as ecdsa 0.17.0's `dev::blobby::parse_into_structs!` reads the
crate's Wycheproof data: a header of blob and dedup counts, the dedup table, the blobs; and the
position after the last
-/
private def blobs (data : ByteArray) : Array ByteArray × Nat := Id.run do
  let (count, position) := readVlq data 0
  let (dedupCount, position) := readVlq data position
  let mut position := position
  let mut dedup := #[]
  for _ in [0:dedupCount] do
    let (length, next) := readVlq data position
    dedup := dedup.push (data.extract next (next + length))
    position := next + length
  let mut result := #[]
  for _ in [0:count] do
    let (value, next) := readVlq data position
    if value % 2 == 1 then
      result := result.push (dedup.getD (value / 2) .empty)
      position := next
    else
      result := result.push (data.extract next (next + value / 2))
      position := next + value / 2
  return (result, position)

/-- A Wycheproof coordinate as the crate's test reads it: 32 bytes, left-padded or unpadded -/
private def coordinate (bytes : ByteArray) : Option ByteArray :=
  if 32 ≤ bytes.size then
    if (bytes.extract 0 (bytes.size - 32)).data.all (· == 0) then
      some (bytes.extract (bytes.size - 32) bytes.size)
    else none
  else some (zeros (32 - bytes.size) ++ bytes)

/--
The crate's Wycheproof test (`src/ecdsa.rs:263-386`) on its P1363 vectors: the key `04 ‖ x ‖ y`,
the signature through `Signature::from_slice` (`Ecdsa.signatureScalars`), then `normalize_s`, then
`Verifier::verify` (`Ecdsa.verifies`); the verdict must be the vector's
-/
private def wycheproof (path : String) (vectors valid : Nat) : IO Unit := do
  let data ← IO.FS.readBinFile path
  let (all, finish) := blobs data
  check s!"{path}: the blobs fill the file" (finish == data.size)
  check s!"{path}: five blobs per vector" (all.size == 5 * vectors)
  let mut passing := 0
  for i in [0:vectors] do
    let field := fun (k : Nat) => all[5 * i + k]!
    let pass := field 4 == ⟨#[1]⟩
    if pass then passing := passing + 1
    let some x := coordinate (field 0) | throw (IO.userError s!"{path} {i}: x too large")
    let some y := coordinate (field 1) | throw (IO.userError s!"{path} {i}: y too large")
    let key := ⟨#[4]⟩ ++ x ++ y
    let accepted := match Ecdsa.signatureScalars (field 3) with
      | none => false
      | some (r, s) => Ecdsa.verifies key (field 2) (Ecdsa.normalizeS r s)
    check s!"{path} vector {i}: verdict {pass}" (accepted == pass)
  check s!"{path}: {valid} valid vectors" (passing == valid)
  IO.println s!"k256 Wycheproof {path}: {vectors} vectors passed, {valid} valid"

/--
`Signature::from_slice` in `vectors.txt`, by the reason the bytes are refused, read from the bytes
themselves: each refused for its reason by the crate (status 1), each other 64-byte input with `r`
and `s` in `[1, n − 1]` accepted (status 0) and written back unchanged, the largest of them
included, and the last 208 inputs the signatures of Wycheproof's P1363 vectors, in order; the
count of each reason pinned, so a regenerated file keeps them all
-/
private def fromSliceVectors : IO Unit := do
  let n := Secp256k1.domain.n
  let document ← IO.FS.readFile "K256/Tests/Generated/vectors.txt"
  let lines := (document.splitOn "\n").filter (·.startsWith "signature_from_slice ")
  check "vectors.txt: 235 from_slice lines" (lines.length == 235)
  let mut inputs : Array ByteArray := #[]
  let mut counts : List (String × Nat) := []
  let count := fun (counts : List (String × Nat)) (reason : String) =>
    (reason, (counts.lookup reason).getD 0 + 1) :: counts.filter (·.1 != reason)
  for line in lines do
    let some [_, inputHex, status, outputHex] := some (line.splitOn " ")
      | throw (IO.userError s!"vectors.txt: {(line.take 60).toString}")
    let bytes ← field inputHex
    let output ← field outputHex
    inputs := inputs.push bytes
    let r := Encoding.octetsToNat (bytes.extract 0 32)
    let s := Encoding.octetsToNat (bytes.extract 32 64)
    let mut reasons : List String := []
    if bytes.size != 64 then reasons := ["another length"] else
      if r == 0 then reasons := "r = 0" :: reasons
      if s == 0 then reasons := "s = 0" :: reasons
      if n ≤ r then reasons := "r ≥ n" :: reasons
      if n ≤ s then reasons := "s ≥ n" :: reasons
    if reasons.isEmpty then
      check s!"crate: from_slice accepts r and s in [1, n − 1], written back unchanged, \
        {(line.take 60).toString}" (status == "0" && output == bytes)
      counts := count counts "accepted"
      if r == n - 1 || s == n - 1 then counts := count counts "accepted, r or s of n − 1"
    else
      check s!"crate: from_slice refuses {reasons}, {(line.take 60).toString}"
        (status == "1" && output.isEmpty)
      for reason in reasons do counts := count counts reason
  for (reason, expected) in [("another length", 10), ("r = 0", 9), ("s = 0", 10), ("r ≥ n", 32),
      ("s ≥ n", 31), ("accepted", 169), ("accepted, r or s of n − 1", 6)] do
    check s!"vectors.txt: {expected} from_slice inputs with {reason}"
      ((counts.lookup reason).getD 0 == expected)
  let data ← IO.FS.readBinFile "K256/Tests/Vectors/test_vectors/data/wycheproof-p1316.blb"
  let (all, _) := blobs data
  let signatures := (List.range 208).map fun i => all[5 * i + 3]!
  check "vectors.txt: the last 208 from_slice inputs are Wycheproof's P1363 signatures, in order"
    (inputs.toList.drop (inputs.size - 208) == signatures)
  IO.println s!"k256 from_slice: {lines.length} crate results, each refusal reason reached"

/--
`Verifier::verify` at BIP 62's low-`s` bound (`Tests/Generated/low-s-bound.txt`): four SEC 1
signatures with `s` equal to BIP 62's largest low `s` or one more, built by choosing the key
(`low-s-bound.py`). Each line's expected status is the generator's, 0 when OpenSSL finds the
signature valid and `s` is at most BIP 62's bound, and its SEC 1 verdict is OpenSSL's
-/
private def lowSBound : IO Unit := do
  -- BIP 62, "Low S values in signatures": "between 0x1 and 0x7FFFFFFF FFFFFFFF FFFFFFFF FFFFFFFF
  -- 5D576E73 57A4501D DFE92F46 681B20A0 (inclusive)"
  let largest := 0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF5D576E7357A4501DDFE92F46681B20A0
  check "BIP 62: the largest low s is n / 2" (largest == Secp256k1.domain.n / 2)
  let document ← IO.FS.readFile "K256/Tests/Generated/low-s-bound.txt"
  let lines := (document.splitOn "\n").filter fun line => !line.isEmpty
  check "low-s-bound.txt: 4 signatures" (lines.length == 4)
  let mut values : List Nat := []
  for line in lines do
    let some [label, keyHex, messageHex, signatureHex, openssl, status] := some (line.splitOn " ")
      | throw (IO.userError s!"low-s-bound.txt: {(line.take 60).toString}")
    let publicKey ← hex keyHex
    let message ← hex messageHex
    let signature ← hex signatureHex
    let some point := Secp256k1.decodePublicKey publicKey
      | throw (IO.userError s!"low-s-bound.txt {label}: no public key")
    let some (r, s) := Ecdsa.signatureScalars signature
      | throw (IO.userError s!"low-s-bound.txt {label}: no signature")
    values := s :: values
    check s!"low-s-bound.txt {label}: SEC 1 verification gives OpenSSL's verdict, {openssl}"
      (ECDSA.verify Secp256k1.domain SHA256.hashBytes point message (r, s) == (openssl == "valid"))
    check s!"low-s-bound.txt {label}: verify gives status {status}"
      (Ecdsa.verifies publicKey message signature == (status == "0"))
  check "low-s-bound.txt: s is the bound in two lines and one more in two"
    (values.count largest == 2 && values.count (largest + 1) == 2)
  IO.println "k256 low-s bound: 4 verify results at s = n / 2 and n / 2 + 1 passed"

/--
Boundaries, rejections with their controls, and each branch of the crate's own specification code;
the point `5 · G` they expect is k256's `src/test_vectors/group.rs` vector
-/
private def synthetic : IO Unit := do
  let n := Secp256k1.domain.n
  let generator := Points.encodePoint Secp256k1.domain true Secp256k1.domain.G
  let identity := zeros 33
  let group ← IO.FS.readFile "K256/Tests/Vectors/test_vectors/group.rs"
  let some [_, _, _, _, _, _, _, _, x5] := some ((← hexLiterals group).take 9)
    | throw (IO.userError "group.rs: 2G and 5G")
  -- secret keys: the smallest and largest accepted, the first rejected
  check "from_bytes: 1 accepted" (Keys.decodeSecret Secp256k1.domain (scalarBytes 1) == some 1)
  check "from_bytes: n - 1 accepted"
    (Keys.decodeSecret Secp256k1.domain (scalarBytes (n - 1)) == some (n - 1))
  check "from_bytes: 0 rejected" (Keys.decodeSecret Secp256k1.domain (scalarBytes 0) == none)
  check "from_bytes: n rejected" (Keys.decodeSecret Secp256k1.domain (scalarBytes n) == none)
  -- key generation: blocks below n, a zero block, and too few bytes
  check "random: first block valid" (Secp256k1.randomSecret (scalarBytes 5) == some 5)
  check "random: a zero block is skipped"
    (Secp256k1.randomSecret (scalarBytes 0 ++ scalarBytes 7) == some 7)
  check "random: a block of n is skipped"
    (Secp256k1.randomSecret (scalarBytes n ++ scalarBytes 7) == some 7)
  check "random: a partial block is not drawn"
    (Secp256k1.randomSecret (scalarBytes 0 ++ (scalarBytes 7).extract 0 31) == none)
  check "random: no bytes" (Secp256k1.randomSecret ByteArray.empty == none)
  -- public key decoding: each form, the identity and a non-point
  let keyG := uncompressed Secp256k1.domain.G
  let compressedG := Points.encodePoint Secp256k1.domain true Secp256k1.domain.G
  check "from_sec1_bytes: uncompressed G"
    (Secp256k1.decodePublicKey keyG == some Secp256k1.domain.G)
  check "from_sec1_bytes: compressed G"
    (Secp256k1.decodePublicKey compressedG == some Secp256k1.domain.G)
  check "from_sec1_bytes: compact G, whose y is even"
    (Secp256k1.decodePublicKey (⟨#[5]⟩ ++ compressedG.extract 1 33) == some Secp256k1.domain.G)
  check "from_sec1_bytes: the compact form of -G decodes to G"
    (Secp256k1.decodePublicKey (⟨#[5]⟩ ++ (Points.encodePoint Secp256k1.domain true
      (Curve.neg Secp256k1.domain Secp256k1.domain.G)).extract 1 33) == some Secp256k1.domain.G)
  check "from_sec1_bytes: the identity 00 is not a public key"
    (Secp256k1.decodePublicKey ⟨#[0]⟩ == none)
  check "from_sec1_bytes: x = 0 is not on the curve"
    (Secp256k1.decodePublicKey (⟨#[2]⟩ ++ scalarBytes 0) == none)
  -- group encoding: the identity, and a 33-byte string that is neither form
  check "GroupEncoding: 33 zero bytes are the identity" (Secp256k1.groupPoint identity ==
    some .infinity)
  check "GroupEncoding: 00 then a nonzero byte is refused"
    (Secp256k1.groupPoint (zeros 32 ++ ⟨#[1]⟩) == none)
  check "GroupEncoding: G" (Secp256k1.groupPoint generator == some Secp256k1.domain.G)
  -- ECDH: the identity, as the crate gives it (vectors.txt), a control, a compact point, no point
  check "ECDH: the identity gives 32 zero bytes"
    (Secp256k1.sharedSecret (scalarBytes 5) identity == zeros 32)
  check "ECDH: control, G gives the x-coordinate of 5 · G, as group.rs gives it"
    (Secp256k1.sharedSecret (scalarBytes 5) generator == x5)
  check "ECDH: the compact form of G, whose y is even, gives the x-coordinate of 5 · G"
    (Secp256k1.sharedSecret (scalarBytes 5) (⟨#[5]⟩ ++ generator.extract 1 33) == x5)
  check "ECDH: 00 then a nonzero byte is no point"
    (Secp256k1.sharedSecret (scalarBytes 5) (zeros 32 ++ ⟨#[1]⟩) == ByteArray.empty)
  -- ECDSA: low s, and SEC 1 alone accepting high s; the crate's verdicts on its signatures, their
  -- high-s forms and another message are in `vectors.txt`
  for (d, message) in [(1, ""), (2, "abc"), (n - 1, "k256"), (0xc0ffee, "low s")] do
    let secret := scalarBytes d
    let publicKey := Secp256k1.publicKeyOf secret
    let signature := Ecdsa.signature secret message.toUTF8
    let some (r, s) := Ecdsa.signatureScalars signature | throw (IO.userError "ECDSA signature")
    check "ECDSA: s ≤ n / 2" (s ≤ n / 2)
    let some point := Secp256k1.decodePublicKey publicKey | throw (IO.userError "public key")
    check "ECDSA: SEC 1 alone accepts high s"
      (ECDSA.verify Secp256k1.domain SHA256.hashBytes point message.toUTF8 (r, n - s))
    check "ECDSA: the search succeeds within one candidate or more"
      ((Ecdsa.signatureWithin d message.toUTF8 10).isSome)
  check "low s: s = n / 2 stays"
    (Ecdsa.normalizeS 1 (n / 2) == Ecdsa.signatureBytes 1 (n / 2))
  check "low s: s = n / 2 + 1 becomes n / 2"
    (Ecdsa.normalizeS 1 (n / 2 + 1) == Ecdsa.signatureBytes 1 (n / 2))
  check "signature: r = 0 refused" (Ecdsa.signatureScalars (scalarBytes 0 ++ scalarBytes 1) == none)
  check "signature: s = n refused" (Ecdsa.signatureScalars (scalarBytes 1 ++ scalarBytes n) == none)
  check "signature: control, r = s = 1" (Ecdsa.signatureScalars (scalarBytes 1 ++ scalarBytes 1) ==
    some (1, 1))
  IO.println "k256 synthetic boundary, rejection and branch checks passed"

/-- Runs every `k256` test, throwing on the first failure -/
def run : IO Unit := do
  generated
  groupVectors
  ecdsaVectors
  rfc6979Nonces
  wycheproof "K256/Tests/Vectors/test_vectors/data/wycheproof-p1316.blb" 208 141
  fromSliceVectors
  lowSBound
  synthetic

end K256.Tests
