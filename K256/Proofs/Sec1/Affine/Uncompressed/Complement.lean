import K256.Proofs.Sec1.Affine.Uncompressed.Entry

namespace K256.Proofs.Sec1.Affine.Uncompressed

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
open K256.Proofs.Common.Field K256.Proofs.Sec1.LIR

theorem complementChoice (y : Bool) (code : CodeMap) (args : Values Value Reg.count) (mem : Ram)
    (sp : Word) (rsp : args[4].get 64 = sp) (invalid : Bool)
    (bit : (args[0].get 64).setWidth 8 = BitVec.ofNat 8 invalid.toNat)
    (push : StoreOk code mem (sp - 8) 8 (if y then 0x11f8f1 else 0x11f82c) 5) :
    let ret : Word := if y then 0x11f8f6 else 0x11f831
    let resume := if y then choiceResume .l11f8f6 ret rfl else choiceResume .l11f831 ret rfl
    ∃ next : Values Value Reg.count,
      program.runBlock (dialect code) ⟨if y then .l11f8ea else .l11f825, args, mem⟩ =
        .call ⟨.l127d50, next, memStore mem (sp - 8) ret⟩ resume ∧
      next[4].get 64 = sp - 8 ∧ next[7].get 64 = BitVec.ofNat 64 (!invalid).toNat ∧
      ∀ i : Fin Reg.count, i.val ∈ [1, 2, 3, 5, 6, 8, 9, 10, 11, 12, 13, 14, 15, 22, 39, 50, 51] →
        next[i] = args[i] := by
  have hc : ((~~~BitVec.ofNat 8 invalid.toNat) &&& 1).setWidth 64 =
      BitVec.ofNat 64 (!invalid).toNat := by cases invalid <;> rfl
  cases y <;> simp only [Bool.false_eq_true, ↓reduceIte] at push ⊢
  all_goals
    refine ⟨?next, ?step, ?stack, ?bit, ?regs⟩
    case step =>
      first
        | change program.runBlock (dialect code) ⟨.l11f825, args, mem⟩ = _
        | change program.runBlock (dialect code) ⟨.l11f8ea, args, mem⟩ = _
      cfg_eval [rsp, push]
      rfl
    case stack => rfl
    case bit =>
      change BitVec.setWidth 64 (BitVec.setWidth 8 (mergeGPR 8 _ _)) = _
      simp only [setWidth_mergeGPR8, bit]
      exact hc
    case regs =>
      intro ⟨i, hi⟩ hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

end K256.Proofs.Sec1.Affine.Uncompressed
