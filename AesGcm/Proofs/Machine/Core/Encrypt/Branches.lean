import AesGcm.Proofs.Machine.Runtime.Tactics
import AesGcm.Proofs.Machine.LIR.Program

namespace AesGcm.Proofs.Machine.Core.Encrypt

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

set_option maxRecDepth 2048 in
set_option maxHeartbeats 800000 in
theorem small_runBlock (use256 : Bool) (code : CodeMap)
    (args : Values Value Reg.count) (mem : Ram) :
    ∃ next,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l102aaf else .l10264f), args, mem⟩ = .jump next ∧
      next.label = (if args[5].get 64 = 0 then (if use256 then .l102b3e else .l1026de) else (if use256 then .l102abe else .l10265e)) ∧
      next.store = mem ∧
      (next.arguments[12]'(by change 12 < 53; decide)).get 64 = args[13].get 64 ∧
      (next.arguments[14]'(by change 14 < 53; decide)).get 64 = args[5].get 64 ∧
      (∀ r : Fin 53, r.val ∈ [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 22, 39, 50, 51] → next.arguments[r] = args[r]) ∧
      (GPRsTyped args → GPRsTyped next.arguments) := by
  cases use256
  all_goals
    by_cases hz : args[5].get 64 = 0
    all_goals
      simp only [hz, ↓reduceIte]
      refine ⟨?_, ?exec, ?_, ?_, ?_, ?_, ?_, ?_⟩
      case exec =>
        first
          | change LIR.program.runBlock (dialect code) ⟨.l10264f, args, mem⟩ = _
          | change LIR.program.runBlock (dialect code) ⟨.l102aaf, args, mem⟩ = _
        cfg_eval []
        refine_norm [hz]
        rfl
      all_goals first
        | rfl
        | (intro hTypes; runtime_typed)
        | (rintro ⟨r, hr⟩ hin; simp only [List.mem_cons, List.not_mem_nil, or_false] at hin;
            rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
        | runtime_finish [hz]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 800000 in
theorem afterFull_runBlock (use256 : Bool) (code : CodeMap)
    (args : Values Value Reg.count) (mem : Ram) :
    ∃ next,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l102aa2 else .l102642), args, mem⟩ = .jump next ∧
      next.label = (if args[14].get 64 = 0 then (if use256 then .l102aaa else .l10264a) else (if use256 then .l102abe else .l10265e)) ∧
      next.store = mem ∧
      (next.arguments[15]'(by change 15 < 53; decide)).get 64 = args[3].get 64 ∧
      (∀ r : Fin 53, r.val ∈ [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 22, 39, 50, 51] → next.arguments[r] = args[r]) ∧
      (GPRsTyped args → GPRsTyped next.arguments) := by
  cases use256
  all_goals
    by_cases hz : args[14].get 64 = 0
    all_goals
      simp only [hz, ↓reduceIte]
      refine ⟨?_, ?exec, ?_, ?_, ?_, ?_, ?_⟩
      case exec =>
        first
          | change LIR.program.runBlock (dialect code) ⟨.l102642, args, mem⟩ = _
          | change LIR.program.runBlock (dialect code) ⟨.l102aa2, args, mem⟩ = _
        cfg_eval []
        refine_norm [hz]
        rfl
      all_goals first
        | rfl
        | (intro hTypes; runtime_typed)
        | (rintro ⟨r, hr⟩ hin; simp only [List.mem_cons, List.not_mem_nil, or_false] at hin;
            rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
        | runtime_finish [hz]

theorem fullDone_runBlock (use256 : Bool) (code : CodeMap)
    (args : Values Value Reg.count) (mem : Ram) :
    ∃ next,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l102aaa else .l10264a), args, mem⟩ = .jump next ∧
      next.label = (if use256 then .l102b3e else .l1026de) ∧
      next.store = mem ∧
      (∀ r : Fin 53, r.val ∈ [3,4,5,12,13,14,15,22,39,50,51] → next.arguments[r] = args[r]) ∧
      (GPRsTyped args → GPRsTyped next.arguments) := by
  cases use256
  all_goals
    refine ⟨?_, ?exec, ?_, ?_, ?_, ?_⟩
    case exec =>
      first
        | change LIR.program.runBlock (dialect code) ⟨.l10264a, args, mem⟩ = _
        | change LIR.program.runBlock (dialect code) ⟨.l102aaa, args, mem⟩ = _
      cfg_eval []
      rfl
    all_goals first
      | rfl
      | (intro hTypes; runtime_typed)
      | (rintro ⟨r, hr⟩ hin; simp only [List.mem_cons, List.not_mem_nil, or_false] at hin;
          rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)

end AesGcm.Proofs.Machine.Core.Encrypt
