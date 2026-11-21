import K256.Proofs.Generate.Generator.Affine.Memory
import K256.Proofs.Generate.Generator.Affine.Normalize.Entry

namespace K256.Proofs.Generate.Generator.Affine

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field

theorem normalizeMemory_frame {fr : Activation} (m : Ram) (room : 976 ≤ fr.rsp.toNat) :
    RamWriteFrame m (normalizeMemory fr m) [scratch fr.rsp] := by
  have slot (k : Word) (hk : 8 ≤ k.toNat ∧ k.toNat ≤ 976) :
      InRegions [scratch fr.rsp] (fr.rsp - k) 8 := by
    refine ⟨_, List.mem_cons_self, ?_⟩
    dsimp only [InRegion, scratch]
    rw [sub_toNat room k hk.2, sub_toNat room 976 (by decide)]
    change fr.rsp.toNat - 976 ≤ fr.rsp.toNat - k.toNat ∧ fr.rsp.toNat - k.toNat + 8 ≤ fr.rsp.toNat - 976 + 976 ∧ fr.rsp.toNat - k.toNat + 8 ≤ 2^64
    have := fr.rsp.isLt
    omega
  unfold normalizeMemory
  repeat' (apply RamWriteFrame.memStore _ _ (slot _ (by decide)))
  exact RamWriteFrame.refl _ _

theorem normalizeMemory_saved (fr : Activation) (m : Ram) :
    let m' := normalizeMemory fr m
    memLoad m' (fr.rsp - 48) 64 = fr.rbx ∧ memLoad m' (fr.rsp - 40) 64 = fr.r12 ∧
    memLoad m' (fr.rsp - 32) 64 = fr.r13 ∧ memLoad m' (fr.rsp - 24) 64 = fr.r14 ∧
    memLoad m' (fr.rsp - 16) 64 = fr.r15 ∧ memLoad m' (fr.rsp - 8) 64 = fr.rbp ∧
    memLoad m' (fr.rsp - 240) 64 = 0x10ed05 := by
  have other (v : Word) (a b : Word) (n : Ram)
      (h : 8 ≤ ((0 - b) - (0 - a)).toNat ∧ 8 ≤ ((0 - a) - (0 - b)).toNat) :
      memLoad (memStore n (fr.rsp - a) v) (fr.rsp - b) 64 = memLoad n (fr.rsp - b) 64 :=
    memLoad_memStore_of_rangeApart _ _ _ _ _ (RangeApart.of_offsets (addr_sub _ _) (addr_sub _ _) h)
  simp (disch := decide) only [normalizeMemory, other, memLoad_memStore_same, and_self]

end K256.Proofs.Generate.Generator.Affine
