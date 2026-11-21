import K256.Proofs.Verify.Hash.FinalBlocks.Memory
import K256.Proofs.Verify.LIR.Program
import K256.Proofs.Verify.LIR.Generated.Values
import K256.Proofs.Common.Lift.Generated.Values.Store2

namespace K256.Proofs.Verify.Hash.FinalBlocks

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Spec.Program
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

theorem paddingBranch (a : Values Value Reg.count) (m : Ram) (n : Nat)
    (rem : a[14].get 64 = BitVec.ofNat 64 (63 - n % 64)) :
    ∃ b : Values Value Reg.count,
      program.runBlock (dialect Extracted.programImage) ⟨.l1031c3, a, m⟩ =
        (if n % 64 < 56 then .jump ⟨.l103289, b, m⟩ else .jump ⟨.l1031cd, b, m⟩) ∧
      ∀ i : Fin Reg.count, i.val ∈ [3,4,5,12,13,14,15,22,39,50,51] → b[i] = a[i] := by
  have route : ∀ k : Fin 64,
      let flags := cmpSpec (BitVec.ofNat 64 (63-k.val)) 7
      (!(flags.CF || flags.ZF)) = decide (k.val < 56) := by
    decide +kernel
  have h := route ⟨n % 64, Nat.mod_lt _ (by decide)⟩
  refine ⟨?b, ?step, ?keep⟩
  case step =>
    cfg_eval [rem]
    rw [h]
    by_cases hs : n % 64 < 56 <;> simp only [hs, decide_true, decide_false,
      Bool.false_eq_true, ↓reduceIte] <;> rfl
  case keep =>
    intro ⟨j,_⟩ hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem clearBlock (a : Values Value Reg.count) (m : Ram) (sp : Word)
    (rsp : a[4].get 64 = sp) (stack : Writable Extracted.programImage m (sp + 8) 56) :
    ∃ b : Values Value Reg.count,
      program.runBlock (dialect Extracted.programImage) ⟨.l10324a,a,m⟩ =
        .jump ⟨.l103289,b,clearPrefix m sp⟩ ∧
      ∀ i : Fin Reg.count, i.val ∈ [3,4,5,12,13,14,15,22,39,50,51] → b[i] = a[i] := by
  refine ⟨?b, ?step, ?keep⟩
  case step =>
    cfg_eval [rsp]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l10324a)
    rfl
  case keep =>
    intro ⟨j,_⟩ hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

end K256.Proofs.Verify.Hash.FinalBlocks
