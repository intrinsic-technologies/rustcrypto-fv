import Standards.NIST.SHA3.Hash

/-!
# Keccak-224, Keccak-256, Keccak-384 and Keccak-512

The four fixed-output-length variants of the Keccak SHA-3 submission, version 3, §2, which the
`Keccak224`, `Keccak256`, `Keccak384` and `Keccak512` types of `sha3` 0.12.0 implement ("NIST
submission without padding changes", its README). The submission writes them `⌊Keccak[r, c]⌋n`: the
sponge function `Keccak[r, c]` on Keccak-f[1600] with the pad10*1 padding of round 3 (§7.2),
truncated to its first `n` output bits. With `r + c = 1600` that sponge is FIPS 202's `KECCAK[c]`
(§5.2: `SPONGE[KECCAK-p[1600, 24], pad10*1, 1600 − c]`, and §3.4: Keccak-f[1600] is KECCAK-p[1600,
24]), so each variant here is FIPS 202's `KECCAK[c](M, n)` in `Standards.NIST.SHA3`. Neither
document states this identification; it follows from FIPS 202 §5.2 and §3.4. Unlike SHA-3 (FIPS 202,
§6.1), no suffix bits follow the message. Messages and results are bit strings.

Source: G. Bertoni, J. Daemen, M. Peeters and G. Van Assche, "The Keccak SHA-3 submission",
version 3, 14 January 2011, https://keccak.team/files/Keccak-submission-3.pdf
-/

namespace Sha3.Spec.Keccak

open Standards.NIST.SHA3

/-- Keccak-224, `⌊Keccak[r = 1152, c = 448]⌋224`: KECCAK[448] of the message, 224 output bits -/
def keccak224 (m : Array Bool) : Vector Bool 224 :=
  KeccakC448.runRaw m 224

/-- Keccak-256, `⌊Keccak[r = 1088, c = 512]⌋256`: KECCAK[512] of the message, 256 output bits -/
def keccak256 (m : Array Bool) : Vector Bool 256 :=
  KeccakC512.runRaw m 256

/-- Keccak-384, `⌊Keccak[r = 832, c = 768]⌋384`: KECCAK[768] of the message, 384 output bits -/
def keccak384 (m : Array Bool) : Vector Bool 384 :=
  KeccakC768.runRaw m 384

/-- Keccak-512, `⌊Keccak[r = 576, c = 1024]⌋512`: KECCAK[1024] of the message, 512 output bits -/
def keccak512 (m : Array Bool) : Vector Bool 512 :=
  KeccakC1024.runRaw m 512

end Sha3.Spec.Keccak
