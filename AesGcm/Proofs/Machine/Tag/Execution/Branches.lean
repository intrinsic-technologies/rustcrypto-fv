import AesGcm.Proofs.Machine.Runtime.Tactics
import AesGcm.Proofs.Machine.LIR.Program

namespace AesGcm.Proofs.Machine.Tag.Execution

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

set_option maxRecDepth 2048 in
set_option maxHeartbeats 800000 in
theorem aad_tail_branch (use256 : Bool) (code : CodeMap)
    (args : Values Value Reg.count) (mem : Ram) :
    ∃ next,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l101c86 else .l101866), args, mem⟩ = .jump next ∧
      next.label = (if args[3].get 64 &&& 15 = 0 then
        (if use256 then .l101d5e else .l10193e) else
        (if use256 then .l101c93 else .l101873)) ∧
      next.store = mem ∧
      next.arguments[13]'(by change 13 < 53; decide) = ⟨64, args[3].get 64 &&& 15⟩ ∧
      (∀ r : Fin 53, r.val ∈ [3,4,5,12,14,15,22,39,50,51] → next.arguments[r] = args[r]) ∧
      (GPRsTyped args → GPRsTyped next.arguments) := by
  cases use256
  all_goals
    by_cases hz : args[3].get 64 &&& 15 = 0
    all_goals
      simp only [hz, ↓reduceIte]
      refine ⟨?_, ?exec, ?_, ?_, ?_, ?_, ?_⟩
      case exec =>
        first
          | change LIR.program.runBlock (dialect code) ⟨.l101866, args, mem⟩ = _
          | change LIR.program.runBlock (dialect code) ⟨.l101c86, args, mem⟩ = _
        cfg_eval [andFlags]
        refine_norm [hz]
        rfl
      all_goals first
        | rfl
        | (intro hTypes; runtime_typed)
        | (rintro ⟨r, hr⟩ hin; simp only [List.mem_cons, List.not_mem_nil, or_false] at hin;
            rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
        | runtime_finish [hz]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 800000 in
theorem ciphertext_tail_branch (use256 : Bool) (code : CodeMap)
    (args : Values Value Reg.count) (mem : Ram) :
    ∃ next,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l101d72 else .l101952), args, mem⟩ = .jump next ∧
      next.label = (if args[15].get 64 &&& 15 = 0 then
        (if use256 then .l101e4a else .l101a2a) else
        (if use256 then .l101d7f else .l10195f)) ∧
      next.store = mem ∧
      next.arguments[12]'(by change 12 < 53; decide) = ⟨64, args[15].get 64 &&& 15⟩ ∧
      (∀ r : Fin 53, r.val ∈ [3,4,5,13,14,15,22,39,50,51] → next.arguments[r] = args[r]) ∧
      (GPRsTyped args → GPRsTyped next.arguments) := by
  cases use256
  all_goals
    by_cases hz : args[15].get 64 &&& 15 = 0
    all_goals
      simp only [hz, ↓reduceIte]
      refine ⟨?_, ?exec, ?_, ?_, ?_, ?_, ?_⟩
      case exec =>
        first
          | change LIR.program.runBlock (dialect code) ⟨.l101952, args, mem⟩ = _
          | change LIR.program.runBlock (dialect code) ⟨.l101d72, args, mem⟩ = _
        cfg_eval [andFlags]
        refine_norm [hz]
        rfl
      all_goals first
        | rfl
        | (intro hTypes; runtime_typed)
        | (rintro ⟨r, hr⟩ hin; simp only [List.mem_cons, List.not_mem_nil, or_false] at hin;
            rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
        | runtime_finish [hz]

end AesGcm.Proofs.Machine.Tag.Execution
