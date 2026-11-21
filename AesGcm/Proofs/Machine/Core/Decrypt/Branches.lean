import AesGcm.Proofs.Machine.Runtime.Tactics
import AesGcm.Proofs.Machine.LIR.Program

namespace AesGcm.Proofs.Machine.Core.Decrypt

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime


set_option maxRecDepth 2048 in
set_option maxHeartbeats 800000 in
theorem small_runBlock (use256 : Bool) (code : CodeMap)
    (args : Values Value Reg.count) (mem : Ram) :
    ∃ next,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l1028dc else .l10247c), args, mem⟩ = .jump next ∧
      next.label = (if args[14].get 64 = 0 then (if use256 then .l102961 else .l102501) else (if use256 then .l1028e4 else .l102484)) ∧
      next.store = mem ∧
      next.arguments[13]'(by change 13 < 53; decide) = ⟨64, args[12].get 64⟩ ∧
      (∀ r : Fin 53, r.val ∈ [0,3,4,5,12,14,15,22,39,50,51] → next.arguments[r] = args[r]) ∧
      (GPRsTyped args → GPRsTyped next.arguments) := by
  cases use256
  all_goals by_cases hz : args[14].get 64 = 0
  all_goals
    simp only [hz, ↓reduceIte]
    refine ⟨?_, ?exec, ?_, ?_, ?_, ?_, ?_⟩
    case exec =>
      first
        | change LIR.program.runBlock (dialect code) ⟨.l10247c, args, mem⟩ = _
        | change LIR.program.runBlock (dialect code) ⟨.l1028dc, args, mem⟩ = _
      cfg_eval []
      refine_norm [hz]
      rfl
    all_goals first
      | rfl
      | (intro hTypes; runtime_typed)
      | (rintro ⟨r, hr⟩ hin; simp only [List.mem_cons, List.not_mem_nil, or_false] at hin;
          rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
      | runtime_finish []

set_option maxRecDepth 2048 in
set_option maxHeartbeats 800000 in
theorem afterFull_runBlock (use256 : Bool) (code : CodeMap)
    (args : Values Value Reg.count) (mem : Ram) :
    ∃ next,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l1028d0 else .l102470), args, mem⟩ = .jump next ∧
      next.label = (if args[14].get 64 = 0 then (if use256 then .l1028d7 else .l102477) else (if use256 then .l1028e4 else .l102484)) ∧
      next.store = mem ∧
      next.arguments[0]'(by change 0 < 53; decide) = ⟨64, (args[3].get 32).setWidth 64⟩ ∧
      (∀ r : Fin 53, r.val ∈ [3,4,5,12,13,14,15,22,39,50,51] → next.arguments[r] = args[r]) ∧
      (GPRsTyped args → GPRsTyped next.arguments) := by
  cases use256
  all_goals by_cases hz : args[14].get 64 = 0
  all_goals
    simp only [hz, ↓reduceIte]
    refine ⟨?_, ?exec, ?_, ?_, ?_, ?_, ?_⟩
    case exec =>
      first
        | change LIR.program.runBlock (dialect code) ⟨.l102470, args, mem⟩ = _
        | change LIR.program.runBlock (dialect code) ⟨.l1028d0, args, mem⟩ = _
      cfg_eval []
      refine_norm [hz]
      rfl
    all_goals first
      | rfl
      | (intro hTypes; runtime_typed)
      | (rintro ⟨r, hr⟩ hin; simp only [List.mem_cons, List.not_mem_nil, or_false] at hin;
          rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
      | runtime_finish []

set_option maxRecDepth 2048 in
set_option maxHeartbeats 800000 in
theorem fullDone_runBlock (use256 : Bool) (code : CodeMap)
    (args : Values Value Reg.count) (mem : Ram) :
    ∃ next,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l1028d7 else .l102477), args, mem⟩ = .jump next ∧
      next.label = (if use256 then .l102961 else .l102501) ∧
      next.store = mem ∧
      (∀ r : Fin 53, r.val ∈ [0,3,4,5,12,13,14,15,22,39,50,51] → next.arguments[r] = args[r]) ∧
      (GPRsTyped args → GPRsTyped next.arguments) := by
  cases use256
  all_goals
    refine ⟨?_, ?exec, ?_, ?_, ?_, ?_⟩
    case exec =>
      first
        | change LIR.program.runBlock (dialect code) ⟨.l102477, args, mem⟩ = _
        | change LIR.program.runBlock (dialect code) ⟨.l1028d7, args, mem⟩ = _
      cfg_eval []
      rfl
    all_goals first
      | rfl
      | (intro hTypes; runtime_typed)
      | (rintro ⟨r, hr⟩ hin; simp only [List.mem_cons, List.not_mem_nil, or_false] at hin;
          rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
      | runtime_finish []

set_option maxRecDepth 2048 in
set_option maxHeartbeats 800000 in
theorem tailDone_runBlock (use256 : Bool) (code : CodeMap)
    (args : Values Value Reg.count) (mem : Ram) :
    ∃ next,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l10295f else .l1024ff), args, mem⟩ = .jump next ∧
      next.label = (if use256 then .l102961 else .l102501) ∧
      next.store = mem ∧
      next.arguments[0]'(by change 0 < 53; decide) = ⟨64, (args[5].get 32).setWidth 64⟩ ∧
      (∀ r : Fin 53, r.val ∈ [3,4,5,12,13,14,15,22,39,50,51] → next.arguments[r] = args[r]) ∧
      (GPRsTyped args → GPRsTyped next.arguments) := by
  cases use256
  all_goals
    refine ⟨?_, ?exec, ?_, ?_, ?_, ?_, ?_⟩
    case exec =>
      first
        | change LIR.program.runBlock (dialect code) ⟨.l1024ff, args, mem⟩ = _
        | change LIR.program.runBlock (dialect code) ⟨.l10295f, args, mem⟩ = _
      cfg_eval []
      rfl
    all_goals first
      | rfl
      | (intro hTypes; runtime_typed)
      | (rintro ⟨r, hr⟩ hin; simp only [List.mem_cons, List.not_mem_nil, or_false] at hin;
          rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
      | runtime_finish []

end AesGcm.Proofs.Machine.Core.Decrypt
