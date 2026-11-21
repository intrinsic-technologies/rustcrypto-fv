import AesGcm.Proofs.Machine.Runtime.Tactics
import AesGcm.Proofs.Machine.LIR.Program

namespace AesGcm.Proofs.Machine.Entry.InPlaceDecrypt

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift
  X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem length_runBlock (use256 : Bool) (code : CodeMap)
    (args : Values Value Reg.count) (mem : Ram) (hTypes : GPRsTyped args) :
    ∃ next,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l101560 else .l101280), args, mem⟩ = .jump next ∧
      next.label = (if (args[13].get 64).toNat < 16 then
        (if use256 then .l1015b2 else .l1012d2) else
        (if use256 then .l10156b else .l10128b)) ∧
      next.store = mem ∧
      next.arguments[0]'(by change 0 < 53; decide) = ⟨64, 1⟩ ∧
      (∀ r : Fin 53, r.val ∈ [1,2,3,4,5,6,7,8,9,12,13,14,15,22,39,50,51] →
        next.arguments[r] = args[r]) ∧ GPRsTyped next.arguments := by
  cases use256
  all_goals
    by_cases hl : (args[13].get 64).toNat < 16
    all_goals
      refine ⟨?_, ?exec, ?_, ?_, ?_, ?_, ?_⟩
      case exec =>
        first
          | change LIR.program.runBlock (dialect code) ⟨.l101280, args, mem⟩ = _
          | change LIR.program.runBlock (dialect code) ⟨.l101560, args, mem⟩ = _
        cfg_eval []
        refine_norm []
        simp only [hl, decide_true, decide_false]
        rfl
      all_goals first
        | rfl
        | (simp only [hl, Bool.false_eq_true, ↓reduceIte]; done)
        | runtime_typed
        | (rintro ⟨r, hr⟩ hin; simp only [List.mem_cons, List.not_mem_nil, or_false] at hin;
            rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
              rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem status_runBlock (use256 : Bool) (code : CodeMap)
    (args : Values Value Reg.count) (mem : Ram) (hTypes : GPRsTyped args) :
    ∃ next,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l1015af else .l1012cf), args, mem⟩ = .jump next ∧
      next.label = (if use256 then .l1015b2 else .l1012d2) ∧
      next.store = mem ∧
      next.arguments[0]'(by change 0 < 53; decide) = ⟨64, (args[0].get 8).setWidth 64⟩ ∧
      (∀ r : Fin 53, r.val ∈ [4,22,39,50,51] → next.arguments[r] = args[r]) ∧
      GPRsTyped next.arguments := by
  cases use256
  all_goals
    refine ⟨?_, ?exec, ?_, ?_, ?_, ?_, ?_⟩
    case exec =>
      first
        | change LIR.program.runBlock (dialect code) ⟨.l1012cf, args, mem⟩ = _
        | change LIR.program.runBlock (dialect code) ⟨.l1015af, args, mem⟩ = _
      cfg_eval []
      refine_norm []
      rfl
    all_goals first
      | rfl
      | runtime_typed
      | (rintro ⟨r, hr⟩ hin; simp only [List.mem_cons, List.not_mem_nil, or_false] at hin;
          rcases hin with rfl | rfl | rfl | rfl | rfl <;> rfl)
      | simp only [Value.get, BitVec.setWidth_setWidth_of_le, Nat.reduceLeDiff]

end AesGcm.Proofs.Machine.Entry.InPlaceDecrypt
