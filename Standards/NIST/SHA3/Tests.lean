import Standards.NIST.SHA3
import Standards.Tests.Utilities

/-!
# FIPS 202 tests

The vectors are the unmodified contents of NIST's `sha-3bytetestvectors.zip` and
`sha-3bittestvectors.zip` from the CAVP SHA-3 suite:
https://csrc.nist.gov/projects/cryptographic-algorithm-validation-program/secure-hashing

| Algorithm | Byte short | Byte long | Byte Monte Carlo | Bit short | Bit long | Bit Monte Carlo |
| --------- | ---------: | --------: | ---------------: | --------: | -------: | --------------: |
| SHA3-224  |        145 |       100 |              100 |      1153 |      100 |             100 |
| SHA3-256  |        137 |       100 |              100 |      1089 |      100 |             100 |
| SHA3-384  |        105 |       100 |              100 |       833 |      100 |             100 |
| SHA3-512  |         73 |       100 |              100 |       577 |      100 |             100 |

Byte-oriented vectors check the hash functions through the byte conversions of Appendix B.1
(`Digest.ofBits (SHA3_256 (bytesToBits m))`, ...); bit-oriented vectors check the bit-string
functions (`SHA3_256`, ...) on messages of any length. Each Monte Carlo suite performs 100,000
hashes, checking every 1,000th digest (SHA3VS §6.2.3).

The permutations KECCAK-f[200], KECCAK-f[400], KECCAK-f[800], and KECCAK-f[1600] are checked
against the unmodified `KeccakF-<b>-IntermediateValues.txt` files of the designers' eXtended
Keccak Code Package (XKCP), `tests/TestVectors/` at commit
`5585d0213203c0c5b2dfdf3b34f5da9275abc3e7`:
https://github.com/XKCP/XKCP/tree/5585d0213203c0c5b2dfdf3b34f5da9275abc3e7/tests/TestVectors
Each file permutes the all-zero state twice, printing the state after every step of every round.
For both examples of each file the tests check each step mapping on its printed input at every
round index, 5 × 18, 20, 22, or 24 checks; `keccakF` from the input to the output; and, since the
rounds of KECCAK-p[b, nr] are the last `nr` rounds of KECCAK-f[b] (§3.4), `keccakP` for every `nr`
from 0 to `11 + 2ℓ`, from the state after round `11 + 2ℓ − nr` to the output, and for
`nr = 12 + 2ℓ` from the input.
-/

namespace Standards.NIST.SHA3.Tests

open Standards.Tests Standards.NIST.SHA3

/-- A SHA-3 hash function under test, in both of its forms -/
private structure Algorithm where
  digestBits : Nat
  rateBits : Nat
  bits : Array Bool → Array Bool
  bytes : ByteArray → ByteArray

private def Algorithm.name (alg : Algorithm) : String := s!"SHA3_{alg.digestBits}"

private def algorithms : Array Algorithm := #[
  ⟨224, 1152, fun m => (SHA3_224 m).toArray,
    fun m => (Digest.ofBits (byteCount := 28) (SHA3_224 (bytesToBits m))).toBytes⟩,
  ⟨256, 1088, fun m => (SHA3_256 m).toArray,
    fun m => (Digest.ofBits (byteCount := 32) (SHA3_256 (bytesToBits m))).toBytes⟩,
  ⟨384, 832, fun m => (SHA3_384 m).toArray,
    fun m => (Digest.ofBits (byteCount := 48) (SHA3_384 (bytesToBits m))).toBytes⟩,
  ⟨512, 576, fun m => (SHA3_512 m).toArray,
    fun m => (Digest.ofBits (byteCount := 64) (SHA3_512 (bytesToBits m))).toBytes⟩]

/-- Key-value lines of a response file, without comments and the `[L = ...]` header -/
private def fields (path : System.FilePath) (alg : Algorithm) : IO (Array (String × String)) := do
  let mut result := #[]
  for line in (← IO.FS.readFile path).splitOn "\n" do
    let line := line.trimAscii.toString
    if line.isEmpty || line.startsWith "#" || line == s!"[L = {alg.digestBits}]" then continue
    match line.splitOn " = " with
    | [key, value] => result := result.push (key, value)
    | _ => throw (IO.userError s!"{path}: invalid line: {line}")
  return result

private def field (data : Array (String × String)) (i : Nat) (key : String) : IO String := do
  let some (actual, value) := data[i]? | throw (IO.userError s!"Missing {key}")
  unless actual == key do throw (IO.userError s!"Expected {key}, got {actual}")
  return value

private def number (value : String) : IO Nat := do
  let some n := value.toNat? | throw (IO.userError s!"Invalid number: {value}")
  return n

/-- Compares a digest computed by `bytes` with the expected bytes -/
private def checkBytes (alg : Algorithm) (actual expected : ByteArray) (label : String) :
    IO Unit := do
  unless expected.size * 8 == alg.digestBits && actual.data == expected.data do
    throw (IO.userError s!"{label}: {alg.name} mismatch")

/-- Compares a digest computed by `bits` with the expected bytes, as bits (Appendix B.1) -/
private def checkBits (alg : Algorithm) (actual : Array Bool) (expected : ByteArray)
    (label : String) : IO Unit := do
  unless expected.size * 8 == alg.digestBits && actual == bytesToBits expected do
    throw (IO.userError s!"{label}: {alg.name} mismatch")

/-- Short and long message vectors: byte-oriented files through `bytes`, bit-oriented through `bits` -/
private def messages (path : System.FilePath) (alg : Algorithm) (count : Nat)
    (byteOriented : Bool) : IO Unit := do
  let data ← fields path alg
  unless data.size == 3 * count do throw (IO.userError s!"{path}: incorrect vector count")
  for i in [:count] do
    let length ← number (← field data (3 * i) "Len")
    let message ← hex (← field data (3 * i + 1) "Msg")
    unless message.size == max 1 ((length + 7) / 8) && (!byteOriented || length % 8 == 0) do
      throw (IO.userError s!"{path}: invalid message length")
    let expected ← hex (← field data (3 * i + 2) "MD")
    let label := s!"{path}, Len = {length}"
    if byteOriented then
      checkBytes alg (alg.bytes (message.extract 0 (length / 8))) expected label
    else
      checkBits alg (alg.bits ((bytesToBits message).extract 0 length)) expected label
  IO.println s!"{path}: {count} passed"

/-- Monte Carlo vectors: `MDᵢ = SHA3(MDᵢ₋₁)`, checking every 1,000th digest (SHA3VS §6.2.3) -/
private def monteCarlo (path : System.FilePath) (alg : Algorithm) (byteOriented : Bool) :
    IO Unit := do
  let data ← fields path alg
  unless data.size == 201 do throw (IO.userError s!"{path}: incorrect checkpoint count")
  let seed ← hex (← field data 0 "Seed")
  unless seed.size * 8 == alg.digestBits do throw (IO.userError s!"{path}: invalid seed length")
  let mut digest := seed
  let mut digestBits := bytesToBits seed
  for j in [:100] do
    let count ← number (← field data (1 + 2 * j) "COUNT")
    unless count == j do throw (IO.userError s!"{path}: incorrect COUNT")
    let expected ← hex (← field data (2 + 2 * j) "MD")
    let label := s!"{path}, COUNT = {j}"
    if byteOriented then
      for _ in [:1000] do
        digest := alg.bytes digest
      checkBytes alg digest expected label
    else
      for _ in [:1000] do
        digestBits := alg.bits digestBits
      checkBits alg digestBits expected label
  IO.println s!"{path}: 100 checkpoints passed"

/-- The bit string of a state printed as bytes (Appendix B.1) -/
private def stateOfBytes (ℓ : Fin 7) (bytes : ByteArray) (label : String) :
    IO (Vector Bool (b ℓ)) := do
  let bits := bytesToBits bytes
  if h : bits.size = b ℓ then return ⟨bits, h⟩
  throw (IO.userError s!"{label}: state has {bytes.size} bytes")

/--
The bit string of a state printed as 25 lanes of `w` bits, five per line for `y` = 0 to 4, each
in hexadecimal: bit `z` of lane `(x, y)` is `S[w(5y + x) + z]` (§3.1.2)
-/
private def stateOfLanes (ℓ : Fin 7) (lines : List String) (label : String) :
    IO (Vector Bool (b ℓ)) := do
  let words := lines.flatMap fun line => (line.splitOn " ").filter (· ≠ "")
  unless words.length == 25 do throw (IO.userError s!"{label}: expected 25 lanes")
  let mut bits := #[]
  for word in words do
    unless word.length * 4 == w ℓ do throw (IO.userError s!"{label}: invalid lane {word}")
    let mut lane := 0
    for c in word.toList do
      lane := 16 * lane + (← Standards.Tests.hexDigit c)
    bits := bits ++ (Array.range (w ℓ)).map fun z => lane.testBit z
  if h : bits.size = b ℓ then return ⟨bits, h⟩
  throw (IO.userError s!"{label}: invalid state size")

/--
One example of an XKCP intermediate-values file: input, the states after each step of each
round, and output
-/
private structure PermutationExample (ℓ : Fin 7) where
  input : Vector Bool (b ℓ)
  rounds : Array (Vector (Vector Bool (b ℓ)) 5)
  output : Vector Bool (b ℓ)

/-- The line after the first line equal to `marker`, and the lines after it -/
private def afterLine (lines : List String) (marker : String) (label : String) :
    IO (List String) := do
  match lines.dropWhile (· ≠ marker) with
  | _ :: rest => return rest
  | [] => throw (IO.userError s!"{label}: missing {marker}")

/-- Parses the example that follows `header` in an XKCP intermediate-values file -/
private def permutationExample (ℓ : Fin 7) (lines : List String) (header : String)
    (label : String) : IO (PermutationExample ℓ) := do
  let mut rest ← afterLine lines header label
  rest ← afterLine rest "Input of permutation:" label
  let input ← stateOfBytes ℓ (← Standards.Tests.hex rest.head!) s!"{label}, input"
  let mut rounds := #[]
  for r in [:12 + 2 * (ℓ : Nat)] do
    rest ← afterLine rest s!"--- Round {r} ---" label
    let mut steps := #[]
    for step in ["theta", "rho", "pi", "chi", "iota"] do
      rest ← afterLine rest s!"After {step}:" label
      steps := steps.push (← stateOfLanes ℓ (rest.take 5) s!"{label}, round {r}, {step}")
    if h : steps.size = 5 then rounds := rounds.push ⟨steps, h⟩
  rest ← afterLine rest "State after permutation:" label
  let output ← stateOfBytes ℓ (← Standards.Tests.hex rest.head!) s!"{label}, output"
  return ⟨input, rounds, output⟩

/-- Checks one width's XKCP intermediate-values file -/
private def permutation (ℓ : Fin 7) : IO Unit := do
  let path := System.FilePath.mk "Standards/NIST/SHA3/Vectors/XKCP" /
    s!"KeccakF-{b ℓ}-IntermediateValues.txt"
  let lines := ((← IO.FS.readFile path).splitOn "\n").map (·.trimAscii.toString)
  let roundCount := 12 + 2 * (ℓ : Nat)
  let first ← permutationExample ℓ lines "+++ Example with the all-zero input +++" s!"{path}"
  let second ← permutationExample ℓ lines "+++ Example taking the previous output as input +++"
    s!"{path}"
  check s!"{path}: first input is not zero" (first.input == Vector.replicate (b ℓ) false)
  check s!"{path}: second input is not the first output" (second.input == first.output)
  for ex in [first, second] do
    check s!"{path}: incorrect round count" (ex.rounds.size == roundCount)
    check s!"{path}: keccakF mismatch" (keccakF ℓ ex.input == ex.output)
    let mut previous := StateArray.ofString ex.input
    for h : r in [:ex.rounds.size] do
      let steps := ex.rounds[r]'h.2.1
      let label := s!"{path}, round {r}"
      let afterθ := θ previous
      check s!"{label}: θ mismatch" (afterθ.toString == steps[0])
      let afterρ := ρ (StateArray.ofString steps[0])
      check s!"{label}: ρ mismatch" (afterρ.toString == steps[1])
      let afterπ := π (StateArray.ofString steps[1])
      check s!"{label}: π mismatch" (afterπ.toString == steps[2])
      let afterχ := χ (StateArray.ofString steps[2])
      check s!"{label}: χ mismatch" (afterχ.toString == steps[3])
      let afterι := ι (StateArray.ofString steps[3]) r
      check s!"{label}: ι mismatch" (afterι.toString == steps[4])
      check s!"{label}: keccakP mismatch" (keccakP ℓ (roundCount - 1 - r) steps[4] == ex.output)
      previous := StateArray.ofString steps[4]
    check s!"{path}: keccakP from the input mismatch" (keccakP ℓ roundCount ex.input == ex.output)
  IO.println s!"{path}: 2 examples of {roundCount} rounds passed"

/-- Runs every FIPS 202 test, throwing on the first failure -/
def run : IO Unit := do
  let mut jobs := #[]
  for alg in algorithms do
    for (orientation, byteOriented) in [("Byte", true), ("Bit", false)] do
      jobs := jobs.push <| ← IO.asTask do
        let dir := System.FilePath.mk "Standards/NIST/SHA3/Vectors" / orientation
        let shortCount := (if byteOriented then alg.rateBits / 8 else alg.rateBits) + 1
        messages (dir / s!"{alg.name}ShortMsg.rsp") alg shortCount byteOriented
        messages (dir / s!"{alg.name}LongMsg.rsp") alg 100 byteOriented
        monteCarlo (dir / s!"{alg.name}Monte.rsp") alg byteOriented
  for ℓ in [(3 : Fin 7), 4, 5, 6] do
    jobs := jobs.push <| ← IO.asTask (permutation ℓ)
  for job in jobs do
    IO.ofExcept job.get

end Standards.NIST.SHA3.Tests
