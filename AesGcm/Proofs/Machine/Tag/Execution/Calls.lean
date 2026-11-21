import AesGcm.Proofs.Machine.Runtime.Tactics
import AesGcm.Proofs.Machine.LIR.Program

namespace AesGcm.Proofs.Machine.Tag.Execution

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
theorem ciphertext_runBlock (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (args : Values Value Reg.count) (mem : Ram)
    (hstack : Writable code mem (args[4].get 64 - 8) 8) :
    ∃ (callee : LIR.lifted.Location), ∃ continuation,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l101d5e else .l10193e), args, mem⟩ = .call callee continuation ∧
      callee.label = .l109980 ∧
      continuation.target = (if use256 then .l101d72 else .l101952) ∧
      continuation.guard = some ⟨64, (if use256 then (0x101d72 : BitVec 64) else 0x101952)⟩ ∧
      callee.store = memStore mem (args[4].get 64 - 8) (if use256 then (0x101d72 : BitVec 64) else 0x101952) ∧
      callee.arguments[4]'(by change 4 < 53; decide) = ⟨64, args[4].get 64 - 8⟩ ∧
      callee.arguments[7]'(by change 7 < 53; decide) = ⟨64, args[4].get 64 + 80⟩ ∧
      callee.arguments[6]'(by change 6 < 53; decide) = ⟨64, args[14].get 64⟩ ∧
      callee.arguments[2]'(by change 2 < 53; decide) = ⟨64, args[15].get 64 >>> 4⟩ ∧
      (∀ r : Fin 53, r.val ∈ [3,5,12,13,14,15,22,39,50,51] → callee.arguments[r] = args[r]) ∧
      (GPRsTyped args → GPRsTyped callee.arguments) := by
  have hhelperApart {m : Ram} {a : BitVec 64} {n : Nat}
      (h : Writable code m a n) :
      RangeApart a n (if use256 then 0x101d5e else 0x10193e) 20 := by
    cases use256
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l10193e x hx))).apart
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l101d5e x hx))).apart
  cases use256
  all_goals
    simp only [Bool.false_eq_true, ↓reduceIte] at hhelperApart
    refine ⟨?_, ?_, ?exec, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    case exec =>
      first
        | change LIR.program.runBlock (dialect code) ⟨.l10193e, args, mem⟩ = _
        | change LIR.program.runBlock (dialect code) ⟨.l101d5e, args, mem⟩ = _
      cfg_eval []
      refine_norm []
      runtime_guards call
      rfl
    all_goals first
      | rfl
      | (intro hTypes; runtime_typed)
      | (rintro ⟨r, hr⟩ hin; simp only [List.mem_cons, List.not_mem_nil, or_false] at hin;
          rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
      | runtime_finish []

def finalizeMemory (use256 : Bool) (args : Values Value Reg.count) (mem : Ram) : Ram :=
  let sp := args[4].get 64
  let mem := memStore mem (sp + 40) (memLoad mem (sp + 104) 64)
  let mem := memStore mem (sp + 32) (memLoad mem (sp + 96) 64)
  let lo := memLoad mem (sp + 80) 64
  let hi := memLoad mem (sp + 88) 64
  let mem := memStore mem (sp + 24) hi
  let mem := memStore mem (sp + 16) lo
  memStore mem (sp - 8) (if use256 then (0x101f22 : BitVec 64) else 0x101b02)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
theorem finalize_runBlock (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (args : Values Value Reg.count) (mem : Ram)
    (hstack : Writable code mem (args[4].get 64 - 8) 40)
    (hw : Writable code mem (args[4].get 64 + 32) 16)
    (hr : Readable mem (args[4].get 64 + 80) 32) :
    ∃ (callee : LIR.lifted.Location), ∃ continuation,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l101eeb else .l101acb), args, mem⟩ = .call callee continuation ∧
      callee.label = .l1034a0 ∧
      continuation.target = (if use256 then .l101f22 else .l101b02) ∧
      continuation.guard = some ⟨64, (if use256 then (0x101f22 : BitVec 64) else 0x101b02)⟩ ∧
      callee.store = finalizeMemory use256 args mem ∧
      callee.arguments[4]'(by change 4 < 53; decide) = ⟨64, args[4].get 64 - 8⟩ ∧
      callee.arguments[7]'(by change 7 < 53; decide) = ⟨64, args[4].get 64 + 64⟩ ∧
      callee.arguments[6]'(by change 6 < 53; decide) = ⟨64, args[4].get 64 + 16⟩ ∧
      (∀ r : Fin 53, r.val ∈ [3,5,12,13,14,15,22,39,50,51] → callee.arguments[r] = args[r]) ∧
      (GPRsTyped args → GPRsTyped callee.arguments) := by
  have hhelperApart {m : Ram} {a : BitVec 64} {n : Nat}
      (h : Writable code m a n) :
      RangeApart a n (if use256 then 0x101eeb else 0x101acb) 55 := by
    cases use256
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l101acb x hx))).apart
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l101eeb x hx))).apart
  cases use256
  all_goals
    simp only [Bool.false_eq_true, ↓reduceIte] at hhelperApart
    refine ⟨?_, ?_, ?exec, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    case exec =>
      first
        | change LIR.program.runBlock (dialect code) ⟨.l101acb, args, mem⟩ = _
        | change LIR.program.runBlock (dialect code) ⟨.l101eeb, args, mem⟩ = _
      cfg_eval []
      refine_norm []
      runtime_guards call
      rfl
    all_goals first
      | rfl
      | (intro hTypes; runtime_typed)
      | (rintro ⟨r, hr⟩ hin; simp only [List.mem_cons, List.not_mem_nil, or_false] at hin;
          rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
      | runtime_finish [finalizeMemory]

end AesGcm.Proofs.Machine.Tag.Execution
