import K256.Proofs.Verify.LIR.Generated.Values
import K256.Proofs.Common.Tactic
import K256.Proofs.Verify.Core.Scalars.Inverse.Batch.State

namespace K256.Proofs.Verify.Core.Scalars.Inverse.Batch

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Verify.LIR
set_option maxRecDepth 4096 in
theorem correctionReturnBlock {c : Registers} {p : Ram} {q : Word}
    (rsp : c[4].get 64 = q) (rbx : c[3].get 8 = 1) (r14 : c[14].get 64 = q + 408)
    (win : Readable p q 392) (retRead : Readable p (q + 392) 8)
    (dest : Writable Extracted.programImage p (q + 440) 1)
    (ret : memLoad p (q + 392) 64 = 0x10a0f2)
    (unit : WordsAt p (q + 8) 64 (#v[1,0,0,0] : Vector Word 4)) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l109989,c,p⟩,[]⟩ out ∧ out.tag = some ⟨64, 0x10a0f2⟩ ∧
      out.store = memStore p (q + 440) (1 : BitVec 8) ∧ out.values[4] = ⟨64, q + 400⟩ ∧
      (∀ (i : Fin Reg.count) (off : Nat), (i.val,off) ∈ [(3,344),(5,384),(12,352),(13,360),(14,368),(15,376)] →
        out.values[i] = ⟨64, memLoad p (q + BitVec.ofNat 64 off) 64⟩) ∧
      ∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → out.values[i] = c[i] := by
  have u0 := unit 0 (by decide)
  have u1 := unit 1 (by decide)
  have u2 := unit 2 (by decide)
  have u3 := unit 3 (by decide)
  change memLoad p (q + 8 + 0) 64 = 1 at u0
  change memLoad p (q + 8 + 8) 64 = 0 at u1
  change memLoad p (q + 8 + 16) 64 = 0 at u2
  change memLoad p (q + 8 + 24) 64 = 0 at u3
  simp only [Lift.reduceAddOffset] at u0 u1 u2 u3
  have byte : (c[3].get 64).setWidth 8 = 1 := (BitVec.setWidth_setWidth_of_le _ (by decide)).trans rbx
  refine ⟨?out, .done ?run, ?post⟩
  case run =>
    unfold Program.step
    cfg_eval
    simp only [rsp, r14, Lift.reduceAddOffset, u0, u1, u2, u3, orFlags, Option.getD_some,
      setWidth_mergeGPR8,
      byte]
    repeat' (refine Eq.trans (congrArg _ (ite_eq_left ?_)) ?_)
    all_goals try slot_guard using code_l109989
    all_goals try simp (disch := store_disch) only [memLoad_memStore_of_rangeApart, ret, BitVec.reduceToNat]
    all_goals try exact ⟨by slot_guard using code_l109989, by decide⟩
    all_goals try rfl
  case post =>
    refine ⟨rfl, rfl, rfl, ?_, ?_⟩
    · intro ⟨i, hi⟩ off hm
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> rfl
    · intro ⟨i, hi⟩ hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl|rfl|rfl|rfl <;> rfl

end K256.Proofs.Verify.Core.Scalars.Inverse.Batch
