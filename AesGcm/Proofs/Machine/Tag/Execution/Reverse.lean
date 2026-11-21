import AesGcm.Proofs.Machine.Tag.Execution.Reverse.Memory
import AesGcm.Proofs.Machine.LIR.Program

namespace AesGcm.Proofs.Machine.Tag.Execution

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem reverse_runBlock_state (use256 isCipher : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (args : Values Value Reg.count) (mem : Ram)
    (hstack : Writable code mem (args[4].get 64 - 8) 40)
    (hr : Readable mem (args[4].get 64 + 64) 16) :
    ∃ (callee : LIR.lifted.Location), ∃ continuation,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then (if isCipher then .l101db8 else .l101ccc)
          else (if isCipher then .l101998 else .l1018ac)), args, mem⟩ =
        .call callee continuation ∧
      callee.label = .l1034c0 ∧
      continuation.target = (if use256 then (if isCipher then .l101e4a else .l101d5e)
          else (if isCipher then .l101a2a else .l10193e)) ∧
      continuation.guard = some ⟨64, if use256 then (if isCipher then 0x101e4a else 0x101d5e)
          else (if isCipher then 0x101a2a else 0x10193e)⟩ ∧
      callee.arguments[4]'(by change 4 < 53; decide) = ⟨64, args[4].get 64 - 8⟩ ∧
      callee.arguments[7]'(by change 7 < 53; decide) = ⟨64, args[4].get 64 + 80⟩ ∧
      callee.arguments[6]'(by change 6 < 53; decide) = ⟨64, args[4].get 64 + 16⟩ ∧
      (∀ r : Fin 53, r.val ∈ [3,5,12,13,14,15,22,39,50,51] → callee.arguments[r] = args[r]) ∧
      (GPRsTyped args → GPRsTyped callee.arguments) ∧
      callee.store = reverseMemory mem (args[4].get 64)
        (if use256 then (if isCipher then 0x101e4a else 0x101d5e)
          else (if isCipher then 0x101a2a else 0x10193e)) := by
  have hread := hstack.readable
  have hlow := hstack.readable.low
  have hhelperApart {m : Ram} {a : BitVec 64} {n : Nat}
      (h : Writable code m a n) :
      RangeApart a n (if use256 then (if isCipher then 0x101db8 else 0x101ccc)
        else (if isCipher then 0x101998 else 0x1018ac)) 146 := by
    cases use256 <;> cases isCipher
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l1018ac x hx))).apart
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l101998 x hx))).apart
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l101ccc x hx))).apart
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l101db8 x hx))).apart
  cases use256 <;> cases isCipher
  all_goals
    simp only [Bool.false_eq_true, ↓reduceIte] at hhelperApart
    refine ⟨?_, ?_, ?exec, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    case exec =>
      first
        | change LIR.program.runBlock (dialect code) ⟨.l1018ac, args, mem⟩ = _
        | change LIR.program.runBlock (dialect code) ⟨.l101998, args, mem⟩ = _
        | change LIR.program.runBlock (dialect code) ⟨.l101ccc, args, mem⟩ = _
        | change LIR.program.runBlock (dialect code) ⟨.l101db8, args, mem⟩ = _
      cfg_eval []
      runtime_guards call
      rfl
    all_goals first
      | rfl
      | (intro hTypes; runtime_typed)
      | (rintro ⟨r, hr⟩ hin; simp only [List.mem_cons, List.not_mem_nil, or_false] at hin;
          rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
      | (refine_norm [reverseMemory, AesGcm.Proofs.setWidth_mergeGPR16]; done)

theorem reverse_runBlock (use256 isCipher : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (args : Values Value Reg.count) (mem : Ram)
    (hstack : Writable code mem (args[4].get 64 - 8) 40)
    (hr : Readable mem (args[4].get 64 + 64) 16) :
    ∃ (callee : LIR.lifted.Location), ∃ continuation,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then (if isCipher then .l101db8 else .l101ccc)
          else (if isCipher then .l101998 else .l1018ac)), args, mem⟩ =
        .call callee continuation ∧
      callee.label = .l1034c0 ∧
      continuation.target = (if use256 then (if isCipher then .l101e4a else .l101d5e)
          else (if isCipher then .l101a2a else .l10193e)) ∧
      continuation.guard = some ⟨64, if use256 then (if isCipher then 0x101e4a else 0x101d5e)
          else (if isCipher then 0x101a2a else 0x10193e)⟩ ∧
      callee.arguments[4]'(by change 4 < 53; decide) = ⟨64, args[4].get 64 - 8⟩ ∧
      callee.arguments[7]'(by change 7 < 53; decide) = ⟨64, args[4].get 64 + 80⟩ ∧
      callee.arguments[6]'(by change 6 < 53; decide) = ⟨64, args[4].get 64 + 16⟩ ∧
      (∀ r : Fin 53, r.val ∈ [3,5,12,13,14,15,22,39,50,51] → callee.arguments[r] = args[r]) ∧
      (GPRsTyped args → GPRsTyped callee.arguments) ∧
      RamWriteFrame mem callee.store [span (args[4].get 64 - 8) 40] ∧
      memLoad callee.store (args[4].get 64 - 8) 64 =
        (if use256 then (if isCipher then 0x101e4a else 0x101d5e)
          else (if isCipher then 0x101a2a else 0x10193e)) ∧
      memLoad callee.store (args[4].get 64 + 16) 64 =
        bswapSpec (memLoad mem (args[4].get 64 + 72) 64) ∧
      memLoad callee.store (args[4].get 64 + 24) 64 =
        bswapSpec (memLoad mem (args[4].get 64 + 64) 64) := by
  obtain ⟨callee, continuation, hcall, hlabel, htarget, hguard, hsp, hcontext, hsource,
    hpreserved, htyped, hmemory⟩ := reverse_runBlock_state use256 isCipher code hcode
      args mem hstack hr
  refine ⟨callee, continuation, hcall, hlabel, htarget, hguard, hsp, hcontext, hsource,
    hpreserved, htyped, ?_, ?_, ?_, ?_⟩
  · rw [hmemory]
    have hlow := hstack.readable.low
    exact reverseMemory_frame mem _ _ (by bv_omega) hlow
  · rw [hmemory]
    exact reverseMemory_return mem _ _
  · rw [hmemory]
    exact (reverseMemory_words mem _ _).1
  · rw [hmemory]
    exact (reverseMemory_words mem _ _).2

end AesGcm.Proofs.Machine.Tag.Execution
