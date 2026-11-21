import Standards.RFC.DeterministicSigning
import Standards.NIST.EllipticCurves
import Standards.SECG.ECC.Encoding
import Standards.NIST.SHA2
import Standards.Tests.Utilities

/-!
# RFC 6979 tests

Nonce derivation and retries against the unmodified RFC 6979 text from
https://www.rfc-editor.org/, and signing retries with a non-ECC signer.

| Source                     | Vectors | Checks                                               |
| -------------------------- | ------- | ---------------------------------------------------- |
| §A.2.5, P-256 with SHA-256 | 2       | first nonce candidate `k`, also with empty §3.6 data |
| §A.1.2, 163-bit order      | 1       | candidates `k1` and `k2` rejected, `k` accepted      |
| §3.6 with §A.2.5's key     | 1       | nonempty `k'` in steps d and f, by direct HMAC       |
| Synthetic                  | —       | non-ECC signer, attempt limit, signer failure        |

RFC 6979 publishes no vector with additional data, so the nonempty §3.6 check compares the state
with HMAC computed directly from the step d and f formulas.
-/

namespace Standards.RFC.DeterministicSigning.Tests

open Standards.Tests Standards.NIST.SHA2 Standards.RFC.DeterministicSigning Standards.SECG.ECC

private def p256Nonces : IO Unit := do
  let document ← IO.FS.readFile "Standards/RFC/DeterministicSigning/Vectors/rfc6979.txt"
  let vectors := ((← after document "\nA.2.5.  ECDSA, 256 Bits (Prime Field)\n").splitOn "\nA.2.6.").head!
  let order := Standards.NIST.EllipticCurves.P256.domain.n
  let secret := Encoding.octetsToNat (← value vectors "\n   x = ")
  for message in ["sample", "test"] do
    let vector ← after vectors s!"With SHA-256, message = \"{message}\":"
    let state := Nonce.initialState SHA256.hashBytes 64 32 order secret (SHA256.hashBytes message.toUTF8)
    let (candidate, _) := Nonce.candidate SHA256.hashBytes 64 32 order state
    check "RFC6979 nonce" (candidate == Encoding.octetsToNat (← value vector "\n   k = "))
    let withEmpty := AdditionalData.initialState SHA256.hashBytes 64 32 order secret
      (SHA256.hashBytes message.toUTF8) ByteArray.empty
    check "RFC6979 §3.6 empty additional data"
      ((Nonce.candidate SHA256.hashBytes 64 32 order withEmpty).1 == candidate)
  IO.println "RFC6979 A.2.5: P-256 SHA-256 nonces passed"

private def nonceRetries : IO Unit := do
  let document ← IO.FS.readFile "Standards/RFC/DeterministicSigning/Vectors/rfc6979.txt"
  let vectors := ((← after document "\nA.1.1.  Key Pair\n").splitOn "\nA.1.3.").head!
  let number := fun marker => do
    let text := (((← after vectors marker).splitOn "\n").head!).trimAscii.toString
    let mut result := 0
    for c in text.toList do result := 16 * result + (← hexDigit c)
    pure result
  let order ← number "q = 0x"
  let secret ← number "x = 0x"
  let mut state := Nonce.initialState SHA256.hashBytes 64 32 order secret
    (SHA256.hashBytes "sample".toUTF8)
  for (marker, accepted) in [("k1 = 0x", false), ("k2 = 0x", false), ("k = 0x", true)] do
    let (nonce, next) := Nonce.candidate SHA256.hashBytes 64 32 order state
    check "RFC6979 A.1 candidate" (nonce == (← number marker))
    check "RFC6979 A.1 acceptance" ((0 < nonce && nonce < order) == accepted)
    state := Nonce.reject SHA256.hashBytes 64 next
  IO.println "RFC6979 A.1: non-byte order and both rejected nonce candidates passed"

/-- Nonempty additional data `k'` against HMAC computed from §3.6's step d and §3.2's step f -/
private def additionalData : IO Unit := do
  let document ← IO.FS.readFile "Standards/RFC/DeterministicSigning/Vectors/rfc6979.txt"
  let part ← after document "\nA.2.5.  ECDSA, 256 Bits (Prime Field)\n"
  let vectors := (part.splitOn "\nA.2.6.").head!
  let order := Standards.NIST.EllipticCurves.P256.domain.n
  let x ← value vectors "\n   x = "
  let h1 := SHA256.hashBytes "sample".toUTF8
  let k' := "additional data".toUTF8
  let mac := Standards.RFC.HMAC.hmac SHA256.hashBytes 64
  let V₀ : ByteArray := ⟨Array.replicate 32 1⟩
  let K₀ : ByteArray := ⟨Array.replicate 32 0⟩
  let input := x ++ Nonce.bitsToOctets order h1 ++ k'
  let K_d := mac K₀ (V₀ ++ ⟨#[0]⟩ ++ input)
  let V_e := mac K_d V₀
  let K_f := mac K_d (V_e ++ ⟨#[1]⟩ ++ input)
  let V_g := mac K_f V_e
  let state :=
    AdditionalData.initialState SHA256.hashBytes 64 32 order (Encoding.octetsToNat x) h1 k'
  check "RFC6979 §3.6 state with additional data" (state.key == K_f && state.value == V_g)
  let plain := Nonce.initialState SHA256.hashBytes 64 32 order (Encoding.octetsToNat x) h1
  check "RFC6979 §3.6 additional data changes the state" (state.key != plain.key)
  IO.println "RFC6979 3.6: additional data checks passed"

/-- Check that signing uses the supplied hash and signer rather than a fixed algorithm. -/
private def genericSigning : IO Unit := do
  let digest : ByteArray := ⟨#[0]⟩
  let hash := fun (_ : ByteArray) => (⟨#[128]⟩ : ByteArray)
  let sign := fun (nonce : Nat) => some s!"nonce {nonce}"
  check "RFC signing supports a non-ECC signature type"
    (Signing.signWithin hash 1 1 19 sign 1 digest 1 == some "nonce 16")
  check "RFC zero attempts"
    (Signing.signWithin hash 1 1 19 sign 1 digest 0 == none)
  check "RFC rejects invalid nonce before signing"
    (Signing.signWithin (fun _ => ⟨#[255]⟩) 1 1 19 sign 1 digest 3 == none)
  check "RFC signer failure exhausts attempts"
    (Signing.signWithin hash 1 1 19 (fun _ => (none : Option String)) 1 digest 3 == none)
  IO.println "RFC6979: algorithm-independent signing checks passed"

def run : IO Unit := do
  p256Nonces
  nonceRetries
  additionalData
  genericSigning

end Standards.RFC.DeterministicSigning.Tests
