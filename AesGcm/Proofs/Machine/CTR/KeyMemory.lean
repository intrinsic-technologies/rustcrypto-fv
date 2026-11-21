import AesGcm.Proofs.Machine.Runtime.Contracts
import AesGcm.Proofs.Machine.Fixslice16.Widening

namespace AesGcm.Proofs.Machine.CTR
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

theorem widening_store {n k : Nat} (keys : Vector (BitVec 16) n)
    (mem : Ram) (src dst : BitVec 64) (hk : k < n)
    (hbound : dst.toNat + 8 * n ≤ 2^64)
    (hapart : RangeApart dst (8 * n) src (2 * n))
    (hsource : WordsAt mem src 16 keys)
    (hprefix : ∀ i (hi : i < n), i < k →
      memLoad mem (dst + BitVec.ofNat 64 (8 * i)) 64 = Fixslice16.widenWord keys[i]) :
    let mem' := memStore mem (dst + BitVec.ofNat 64 (8 * k)) (Fixslice16.widenWord keys[k])
    WordsAt mem' src 16 keys ∧
    (∀ i (hi : i < n), i < k + 1 →
      memLoad mem' (dst + BitVec.ofNat 64 (8 * i)) 64 = Fixslice16.widenWord keys[i]) ∧
    RamWriteFrame mem mem' [span dst (8 * n)] := by
  have haddr (i : Nat) (hi : i < n) :
      (dst + BitVec.ofNat 64 (8 * i)).toNat = dst.toNat + 8 * i := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := 8 * i) (by omega), Nat.mod_eq_of_lt (by omega)]
  have hap : RangeApart (dst + BitVec.ofNat 64 (8 * k)) 8 src (2 * n) := by
    intro i hi j hj he
    apply hapart (8 * k + i) (by omega) j hj
    simpa only [BitVec.ofNat_add, ← BitVec.add_assoc] using he
  refine ⟨hsource.write_apart _ _ hap, ?_, ?_⟩
  · intro i hi hik
    by_cases he : i = k
    · subst i
      exact memLoad_memStore_same _ _ _ (by decide) (by decide)
    · rw [memLoad_memStore_of_rangeApart]
      · exact hprefix i hi (by omega)
      · apply RangeApart.of_toNat
        · rw [haddr k hk]; omega
        · rw [haddr i hi]; omega
        · rw [haddr k hk, haddr i hi]
          omega
  · apply (RamWriteFrame.refl mem [span dst (8 * n)]).memStore
    refine ⟨span dst (8 * n), by simp, ?_⟩
    simp only [InRegion, span, haddr k hk]
    omega

end AesGcm.Proofs.Machine.CTR
