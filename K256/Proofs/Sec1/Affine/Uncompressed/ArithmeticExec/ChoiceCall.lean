import K256.Proofs.Sec1.Affine.Uncompressed.ArithmeticExec.Registers
import K256.Proofs.Sec1.Affine.Uncompressed.ArithmeticExec.StackSlots
import K256.Proofs.Sec1.Affine.Uncompressed.ArithmeticExec.WordSteps.Schedule

namespace K256.Proofs.Sec1.Affine.Uncompressed

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
open K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Sec1.LIR

private theorem mergeChoiceByte (b : Bool) :
    mergeGPR 8 (if b = true then 1 else 0) 0 = BitVec.ofNat 64 b.toNat := by
  cases b <;> rfl

theorem arithmeticChoiceCall {code : CodeMap} {orig : Values Value Reg.count}
    {args : Values Value 1397} {mem m : Ram} {sp : Word} {s : ArithmeticState}
    (h : registersMatch args s.regs inputs31) (kept : preservedAt args orig)
    (rsp : s.regs 4 = sp) (stack : SlotState code mem m sp s.slots)
    (cover : ∀ v ∈ fnCode, v ∈ code) :
    ∃ next m2, b_l11f8f6_31.eval (dialect code) args m =
      .call ⟨.l127d50, next, m2⟩ (choiceResume .l120298 0x120298 rfl) ∧
      next[4].get 64 = sp - 8 ∧ next[7].get 64 = (arithmeticStep31 s).regs 7 ∧
      memLoad m2 (sp - 8) 64 = 0x120298 ∧ SlotState code mem m2 sp s.slots ∧
      preservedAt next orig := by
  simp only [inputs31, registersMatch, Nat.reduceEqDiff, ↓reduceIte] at h
  rcases h with ⟨h0, h1, h2, h3, h4, h6, _, h8, h10, h14, _⟩
  have hsp : args[4].get 64 = sp := h4.trans rsp
  have push : StoreOk code m (sp - 8) 8 0x120293 5 := stack.pushOk cover (by decide)
  refine ⟨?next, memStore m (sp - 8) (0x120298 : Word), ?eval, ?stackReg, ?word,
    memLoad_memStore_same _ _ _ (by decide) (by decide), stack.push _, ?preserved⟩
  case eval =>
    unfold b_l11f8f6_31
    simp only [cfg_eval, ↓reduceIte, reduceCtorEq, BitVec.reduceEq, BitVec.reduceSetWidth, hsp, push]
    rfl
  case stackReg => rfl
  case word =>
    change mergeGPR 8 (if (cmpSpec _ _).ZF = true then 1 else 0) 0 = _
    rw [cmpSpec_ZF, mergeChoiceByte]
    simp only [arithmeticStep31, ← h0, ← h1, ← h2, ← h3, ← h6, ← h8, ← h10, ← h14]
    rfl
  case preserved =>
    intro i _ ho hiKept
    have fromOrig := kept i (Nat.lt_trans ho (by decide)) ho hiKept
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hiKept
    rcases hiKept with rfl | rfl | rfl | rfl <;> exact fromOrig

end K256.Proofs.Sec1.Affine.Uncompressed
