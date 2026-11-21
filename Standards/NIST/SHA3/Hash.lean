import Standards.NIST.SHA3.State
import Standards.NIST.SHA3.Steps
import Standards.NIST.SHA3.Permutation
import Standards.NIST.SHA3.Sponge
import Standards.NIST.SHA3.Padding

/-!
# SHA-3

The SHA-3 standard, FIPS 202, on bit strings: the KECCAK[c] family (§5.2), one named instance
per capacity of the four SHA-3 hash functions, and the hash functions themselves (§6.1).

Source: https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.202.pdf
-/

namespace Standards.NIST.SHA3

/-- Capacity `c` of KECCAK[c], with rate `1600 − c` (FIPS 202, §5.2) -/
structure Keccak where
  c : Nat
  hc : 0 < c ∧ c < b 6

/--
KECCAK[c] (FIPS 202, §5.2)

Input: bit string `N` and nonnegative output length `d`
Output: bit string of exactly `d` bits

`KECCAK[c](N, d) = SPONGE[KECCAK-p[1600, 24], pad10*1, 1600 − c](N, d)`
-/
def Keccak.runRaw (k : Keccak) (n : Array Bool) (d : Nat) : Vector Bool d :=
  sponge (keccakF 6) pad101 (b 6 - k.c) (by have := k.hc; omega) n d

/-- KECCAK[448], with a 1152-bit rate: the instance of SHA3-224 (FIPS 202, §6.1) -/
def KeccakC448 : Keccak := ⟨448, by decide⟩

/-- KECCAK[512], with a 1088-bit rate: the instance of SHA3-256 (FIPS 202, §6.1) -/
def KeccakC512 : Keccak := ⟨512, by decide⟩

/-- KECCAK[768], with an 832-bit rate: the instance of SHA3-384 (FIPS 202, §6.1) -/
def KeccakC768 : Keccak := ⟨768, by decide⟩

/-- KECCAK[1024], with a 576-bit rate: the instance of SHA3-512 (FIPS 202, §6.1) -/
def KeccakC1024 : Keccak := ⟨1024, by decide⟩

/--
SHA3-224: KECCAK[448] of the message followed by the bits `01`, with 224 output bits
(FIPS 202, §6.1)
-/
def SHA3_224 (m : Array Bool) : Vector Bool 224 :=
  KeccakC448.runRaw (m ++ #[false, true]) 224

/--
SHA3-256: KECCAK[512] of the message followed by the bits `01`, with 256 output bits
(FIPS 202, §6.1)
-/
def SHA3_256 (m : Array Bool) : Vector Bool 256 :=
  KeccakC512.runRaw (m ++ #[false, true]) 256

/--
SHA3-384: KECCAK[768] of the message followed by the bits `01`, with 384 output bits
(FIPS 202, §6.1)
-/
def SHA3_384 (m : Array Bool) : Vector Bool 384 :=
  KeccakC768.runRaw (m ++ #[false, true]) 384

/--
SHA3-512: KECCAK[1024] of the message followed by the bits `01`, with 512 output bits
(FIPS 202, §6.1)
-/
def SHA3_512 (m : Array Bool) : Vector Bool 512 :=
  KeccakC1024.runRaw (m ++ #[false, true]) 512

end Standards.NIST.SHA3
