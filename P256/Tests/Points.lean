import Standards.Tests.Utilities
import P256.Spec.Points
import P256.Spec.Functions

/-!
# Tests of `ProjectivePoint::add`

The specification `Points.pointAdd`, run by `cd P256 && lake test`, against:

| Source | Checks |
|---|---|
| p256 0.14.0 `src/test_vectors/group.rs` (`Tests/Vectors/p256-0.14.0-test_vectors-group.rs`, unmodified): `ADD_TEST_VECTORS`, `kG` for `k` = 1 to 20 | `iG + jG = (i + j)G` for 30 pairs, each with `i + j ≤ 20`, doubling `kG + kG` for `k` = 1 to 10, and `kG + (−kG)` |
| RFC 9380 §J.1.1 (`P256/Tests/Vectors/rfc9380.txt`), all 5 vectors | `Q0 + Q1 = P` |
| the group law (SEC 1 v2.0 §2.2.1) | the identity `00` as either operand, a point plus its negation, operands in compressed and compact form |
| `Tests/Generated/B-points.txt`: 16 calls of `p256_projective_point_add` run natively on p256 0.14.0 by `B-points-generator/` (`generate.sh` reproduces the file) | each call meets the argument premise (`Functions.projectivePointAddArguments`) and agrees with the specification; calls outside the contract, an operand off the curve, are not in the table |

An operand off the curve is no value of `ProjectivePoint` (`Points.isAffineEncoding`), with `G`
as the control.
-/

namespace P256.Tests.Points

open Standards.Tests P256.Spec Standards.SECG.ECC

private def identity : ByteArray := ⟨#[0]⟩

/-- The `hex!` values of the part of p256's `group.rs` from `marker` to the end of its array -/
private def groupValues (source marker : String) : IO (List ByteArray) := do
  let part := ((← after source marker).splitOn "\n];").head!
  ((part.splitOn "hex!(\"").drop 1).mapM fun piece => hex (piece.takeWhile (· ≠ '"')).toString

/-- `ADD_TEST_VECTORS` as uncompressed points, `kG` at index `k − 1` -/
def addVectors : IO (Array ByteArray) := do
  let source ← IO.FS.readFile "P256/Tests/Vectors/p256-0.14.0-test_vectors-group.rs"
  let values ← groupValues source "pub const ADD_TEST_VECTORS"
  check "ADD_TEST_VECTORS has 20 points" (values.length == 40)
  return ((List.range 20).map fun i => ⟨#[4]⟩ ++ values[2 * i]! ++ values[2 * i + 1]!).toArray

/-- `MUL_TEST_VECTORS` as pairs of the scalar `k` and the uncompressed point `kG` -/
def mulVectors : IO (List (ByteArray × ByteArray)) := do
  let source ← IO.FS.readFile "P256/Tests/Vectors/p256-0.14.0-test_vectors-group.rs"
  let values ← groupValues source "pub const MUL_TEST_VECTORS"
  check "MUL_TEST_VECTORS has 32 vectors" (values.length == 96)
  return (List.range 32).map fun i =>
    (values[3 * i]!, ⟨#[4]⟩ ++ values[3 * i + 1]! ++ values[3 * i + 2]!)

/-- A field of `B-points.txt`: `~` the empty slice or result -/
private def bytesOf (field : String) : IO ByteArray :=
  if field = "~" then pure ByteArray.empty else hex field

private def generated : IO Unit := do
  let lines :=
    (← IO.FS.readFile "P256/Tests/Generated/B-points.txt").splitOn "\n" |>.filter (· ≠ "")
  check "B-points.txt has 16 vectors" (lines.length == 16)
  let mut checked := 0
  for line in lines do
    let [entry, inputs, expectedStatus, output] := line.splitOn " "
      | throw (IO.userError s!"bad vector line: {line}")
    let args ← if inputs = "-" then pure #[] else (inputs.splitOn ",").toArray.mapM bytesOf
    check s!"projectivePointAdd only: {line}" (entry == "projectivePointAdd")
    check s!"arguments the call admits: {line}" (Functions.projectivePointAddArguments args)
    check s!"status 0: {line}" (expectedStatus = "0")
    check s!"output: {line}" (Points.pointAdd args == (← bytesOf output))
    checked := checked + 1
  check "B-points.txt: 16 calls within the contract" (checked == 16)
  IO.println "B-points.txt: 16 calls agree with the specification and meet the argument premise"

private def groupVectors : IO Unit := do
  let kG ← addVectors
  let point (k : Nat) : ByteArray := kG[k - 1]!
  for k in [1:11] do
    expect s!"ADD_TEST_VECTORS: {k}G + {k}G = {2 * k}G" (Points.pointAdd #[point k, point k])
      (point (2 * k))
  for i in [1:6] do
    for j in [1:6] do
      expect s!"ADD_TEST_VECTORS: {i}G + {j}G" (Points.pointAdd #[point i, point j])
        (point (i + j))
  for (i, j) in [(7, 13), (19, 1), (3, 17), (10, 10), (11, 9)] do
    expect s!"ADD_TEST_VECTORS: {i}G + {j}G" (Points.pointAdd #[point i, point j]) (point (i + j))
  IO.println "p256 group.rs: ADD_TEST_VECTORS sums and doublings passed"

private def groupLaw : IO Unit := do
  let kG ← addVectors
  let g := kG[0]!
  let p := Operations.domain.p
  let negate (point : ByteArray) : ByteArray :=
    point.extract 0 33 ++ Encoding.natToOctets 32 (p - Encoding.octetsToNat (point.extract 33 65))
  for k in [1, 2, 7, 20] do
    expect s!"{k}G + (−{k}G) is the identity" (Points.pointAdd #[kG[k - 1]!, negate kG[k - 1]!])
      identity
  expect "identity + G = G" (Points.pointAdd #[identity, g]) g
  expect "G + identity = G" (Points.pointAdd #[g, identity]) g
  expect "identity + identity" (Points.pointAdd #[identity, identity]) identity
  -- compressed operands: `03 ‖ x(G)` is `G`, `02 ‖ x(G)` is `−G` (SEC 1 v2.0 §2.3.4)
  let compressed := ⟨#[3]⟩ ++ g.extract 1 33
  expect "compressed G + G = 2G" (Points.pointAdd #[compressed, g]) kG[1]!
  expect "02 ‖ x(G) is −G: G + it is the identity"
    (Points.pointAdd #[g, ⟨#[2]⟩ ++ g.extract 1 33]) identity
  -- the compact form of p256 0.14.0 `tests/affine.rs`: `05 ‖ x` decodes to the point with that `x`
  -- and the smaller of `y` and `p − y`
  let compact ← hex "05 8e38fc4ffe677662dde8e1a63fbcd45959d2a4c3004d27e98c4fedf2d0c14c01"
  let uncompact ← hex
    "04 8e38fc4ffe677662dde8e1a63fbcd45959d2a4c3004d27e98c4fedf2d0c14c0
        13ca9d8667de0c07aa71d98b3c8065d2e97ab7bb9cb8776bcc0577a7ac58acd4e"
  expect "compact operand: compact + identity is the uncompacted point (tests/affine.rs)"
    (Points.pointAdd #[compact, identity]) uncompact
  expect "compact + uncompacted = uncompacted + uncompacted"
    (Points.pointAdd #[compact, uncompact]) (Points.pointAdd #[uncompact, uncompact])
  let offCurve := g.set! 64 (g.get! 64 ^^^ 1)
  check "a point off the curve is no ProjectivePoint argument"
    (!Functions.projectivePointAddArguments #[offCurve, g])
  check "control: G and the identity are" (Functions.projectivePointAddArguments #[g, identity])
  check "two slices exactly" (!Functions.projectivePointAddArguments #[g])
  -- RFC 9380 §J.1.1: the two mapped points of each vector add to its result
  let rfc9380 ← IO.FS.readFile "P256/Tests/Vectors/rfc9380.txt"
  let suite := ((← after rfc9380 "\nJ.1.1.  P256_XMD:SHA-256_SSWU_RO_\n").splitOn "\nJ.1.2.").head!
  let vectors := (suite.splitOn "\n   msg     =").drop 1
  check "RFC 9380 J.1.1 has 5 vectors" (vectors.length == 5)
  for vector in vectors do
    let point (name : String) : IO ByteArray := do
      let pad := "".pushn ' ' (6 - name.length)
      return ⟨#[4]⟩ ++ (← rfcField vector s!"{name}.x{pad}= ") ++
        (← rfcField vector s!"{name}.y{pad}= ")
    expect "RFC 9380 J.1.1: Q0 + Q1 = P" (Points.pointAdd #[← point "Q0", ← point "Q1"])
      (← point "P")
  IO.println "Group law, operand forms and RFC 9380 J.1.1 sums passed"

/-- Runs this module's tests, throwing on the first failure -/
def run : IO Unit := do
  generated
  groupVectors
  groupLaw

end P256.Tests.Points
