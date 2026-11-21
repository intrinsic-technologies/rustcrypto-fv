import K256.Proofs.Signing.UpdateV.Finalize.State
import K256.Proofs.Common.Tactic
import K256.Proofs.Verify.LIR.Generated.Values

namespace K256.Proofs.Signing.UpdateV.Finalize

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

def callerWrites (sp : BitVec 64) : List MemoryRegion :=
  [⟨(sp - 8).toNat,8⟩,⟨(sp + 72).toNat,32⟩]

theorem callBlock {a : Registers} {m : Ram} {sp : BitVec 64}
    (rsp : a[4].get 64 = sp)
    (depth : 8 ≤ sp.toNat) (limit : sp.toNat + 104 < 2^32)
    (stack : Writable Extracted.programImage m (sp - 8) 112) :
    ∃ b t, program.runBlock (dialect Extracted.programImage) ⟨.l104c21,a,m⟩ =
      .call ⟨.l107a50,b,t⟩ ⟨.l104c52,#v[],rfl,some ⟨64,0x104c52⟩⟩ ∧
      b[4] = ⟨64,sp - 8⟩ ∧ b[6] = ⟨64,sp + 72⟩ ∧ b[7] = ⟨64,a[14].get 64⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,22,39,50,51] → b[i] = a[i]) ∧
      memLoad t (sp - 8) 64 = 0x104c52 ∧ RamWriteFrame m t (callerWrites sp) := by
  refine ⟨?_,?_,?step,?post⟩
  case step =>
    cfg_eval [rsp]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l104c21)
    rfl
  case post =>
    refine ⟨rfl,rfl,rfl,?_,memLoad_memStore_same _ _ _ (by decide) (by decide),?_⟩
    · rintro ⟨i,_⟩ hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · have push : InRegions (callerWrites sp) (sp-8) 8 := by
        refine ⟨_,List.mem_cons_self,Nat.le_refl _,Nat.le_refl _,?_⟩
        have h := BitVec.toNat_sub_of_le (show (8 : BitVec 64) ≤ sp from depth)
        rw [h]; simp only [BitVec.reduceToNat]; omega
      have word (off : BitVec 64) (h : 72 ≤ off.toNat ∧ off.toNat ≤ 96) :
          InRegions (callerWrites sp) (sp+off) 8 := by
        refine ⟨_,List.mem_cons_of_mem _ (List.mem_singleton_self _),?_⟩
        change (sp+72).toNat ≤ (sp+off).toNat ∧
          (sp+off).toNat+8 ≤ (sp+72).toNat+32 ∧ (sp+off).toNat+8 ≤ 2^64
        simp only [BitVec.toNat_add,BitVec.reduceToNat,Nat.reducePow]
        omega
      apply RamWriteFrame.memStore _ _ push
      repeat' apply RamWriteFrame.memStore _ _ (word _ (by decide))
      exact RamWriteFrame.refl _ _

end K256.Proofs.Signing.UpdateV.Finalize
