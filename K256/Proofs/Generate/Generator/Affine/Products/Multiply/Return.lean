import K256.Proofs.Common.Tactic
import K256.Proofs.Generate.Generator.Affine.Products.Input

namespace K256.Proofs.Generate.Generator.Affine

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Generate.LIR

theorem productReturnBlock {sp : Word} {a : Registers} {m : Ram}
    (rsp : a[4].get 64 = sp) (rbx : a[3].get 64 = sp + 376)
    (win : Writable Extracted.programImage m sp 464)
    (ret : memLoad m (sp + 280) 64 = 0x10ee37) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l10ecc3, a, m⟩, []⟩ out ∧
      out.tag = some ⟨64, 0x10ee37⟩ ∧ out.store = memStore m (sp + 456) (0 : BitVec 8) ∧
      out.values[4] = ⟨64, sp + 288⟩ ∧ out.values[3] = ⟨64, memLoad m (sp + 232) 64⟩ ∧
      out.values[12] = ⟨64, memLoad m (sp + 240) 64⟩ ∧
      out.values[14] = ⟨64, memLoad m (sp + 256) 64⟩ ∧
      out.values[15] = ⟨64, memLoad m (sp + 264) 64⟩ ∧
      ∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → out.values[i] = a[i] := by
  refine ⟨?out, .done ?run, ?post⟩
  case run =>
    unfold Program.step
    cfg_eval
    simp only [rsp, rbx, Lift.reduceAddOffset]
    repeat' (refine Eq.trans (congrArg _ (ite_eq_left ?_)) ?_)
    all_goals try slot_guard using code_l10ecc3
    all_goals try simp (disch := store_disch) only [memLoad_memStore_of_rangeApart, ret,
      BitVec.reduceToNat]
    all_goals try exact ⟨by slot_guard using code_l10ecc3, by decide⟩
    all_goals try rfl
  case post =>
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    intro ⟨i, hi⟩ hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl|rfl|rfl|rfl <;> rfl

end K256.Proofs.Generate.Generator.Affine
