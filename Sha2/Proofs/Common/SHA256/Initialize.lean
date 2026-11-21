import Sha2.Proofs.Common.SHA256.Hasher
import Sha2.Proofs.Common.SHA256.Words
import Sha2.Proofs.Wrapper.Variant

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

def Initialize.packedWords (v : Wrapper.Variant) : List (BitVec 64) :=
  match v with
  | .sha224 => [0x367cd507c1059ed8, 0xf70e59393070dd17, 0x68581511ffc00b31,
      0xbefa4fa464f98fa7]
  | .sha256 => [0xbb67ae856a09e667, 0xa54ff53a3c6ef372, 0x9b05688c510e527f,
      0x5be0cd191f83d9ab]

theorem HashStateAt.initial_of_packed {t : RamState} {base : BitVec 64}
    (v : Wrapper.Variant := .sha256)
    (packed : ∀ j < 4, memLoad t.external (base + BitVec.ofNat 64 (8*j)) 64 =
      (Initialize.packedWords v)[j]!)
    (read : MemReadable t base 32) :
    HashStateAt t base v.initialHash := by
  refine ⟨v.initialHash_size, ?_⟩
  intro j hj
  have bytes := Bytes.of_memLoad (n := 64) (m := t.external)
    (a := base + BitVec.ofNat 64 (8*(j/2))) (by
      intro i hi
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact read.mem _ (by omega))
  rw [packed (j/2) (by omega)] at bytes
  have half := bytes.sub (4*(j%2)) 4 (by omega)
  have address : base + BitVec.ofNat 64 (8*(j/2)) +
      BitVec.ofNat 64 (4*(j%2)) = base + BitVec.ofNat 64 (4*j) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
    omega
  rw [address] at half
  apply loadBytes32_of_bytes
  apply half.congr
  intro i hi
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
  all_goals cases v <;> decide +kernel

theorem HasherAt.empty {s : RamState} {base : BitVec 64} {initialHash : Array UInt32}
    (hash : HashStateAt s (base + 64) initialHash)
    (tail : s.external[base + 63]? = some 0)
    (blocks : memLoad s.external (base + 96) 64 = 0) :
    HasherAt s base ByteArray.empty initialHash := by
  refine ⟨?_, ⟨rfl, ?_⟩, tail, blocks⟩
  · simpa only [compressBlocks, ByteArray.size_empty, Nat.zero_div, compressBlocksFrom] using hash
  · intro i
    have hi := i.isLt
    simp only [remainderBytes_size, ByteArray.size_empty, Nat.zero_mod] at hi
    omega

end Sha2.Proofs.Common.SHA256
