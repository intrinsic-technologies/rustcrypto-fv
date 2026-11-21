import AesGcm.Proofs.Machine.Tag.Execution.Length.Memory
import AesGcm.Proofs.Machine.LIR.Program

namespace AesGcm.Proofs.Machine.Tag.Execution

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
private theorem length_runBlock_state (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (args : Values Value Reg.count) (mem : Ram)
    (hstack : Writable code mem (args[4].get 64 - 8) 40) :
    ∃ (callee : LIR.lifted.Location), ∃ continuation,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l101e4a else .l101a2a), args, mem⟩ = .call callee continuation ∧
      callee.label = .l1034c0 ∧
      continuation.target = (if use256 then .l101eeb else .l101acb) ∧
      continuation.guard = some ⟨64, if use256 then 0x101eeb else 0x101acb⟩ ∧
      callee.arguments[4]'(by change 4 < 53; decide) = ⟨64, args[4].get 64 - 8⟩ ∧
      callee.arguments[7]'(by change 7 < 53; decide) = ⟨64, args[4].get 64 + 80⟩ ∧
      callee.arguments[6]'(by change 6 < 53; decide) = ⟨64, args[4].get 64 + 16⟩ ∧
      (∀ r : Fin 53, r.val ∈ [5,12,13,14,22,39,50,51] → callee.arguments[r] = args[r]) ∧
      (GPRsTyped args → GPRsTyped callee.arguments) ∧
      callee.store = lengthMemory mem (args[4].get 64) (args[3].get 64)
        (args[15].get 64) (if use256 then 0x101eeb else 0x101acb) := by
  have hread := hstack.readable
  have hlow := hstack.readable.low
  have hhelperApart {m : Ram} {a : BitVec 64} {n : Nat}
      (h : Writable code m a n) :
      RangeApart a n (if use256 then 0x101e4a else 0x101a2a) 161 := by
    cases use256
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l101a2a x hx))).apart
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l101e4a x hx))).apart
  cases use256
  all_goals
    simp only [Bool.false_eq_true, ↓reduceIte] at hhelperApart
    refine ⟨?_, ?_, ?exec, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    case exec =>
      first
        | change LIR.program.runBlock (dialect code) ⟨.l101a2a, args, mem⟩ = _
        | change LIR.program.runBlock (dialect code) ⟨.l101e4a, args, mem⟩ = _
      cfg_eval []
      runtime_guards call
      rfl
    all_goals first
      | rfl
      | (intro hTypes; runtime_typed)
      | (rintro ⟨r, hr⟩ hin; simp only [List.mem_cons, List.not_mem_nil, or_false] at hin;
          rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
      | (refine_norm [lengthMemory, AesGcm.Proofs.setWidth_mergeGPR_of_le]; done)

theorem length_runBlock (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (args : Values Value Reg.count) (mem : Ram)
    (hstack : Writable code mem (args[4].get 64 - 8) 40)
    (hmessage : (args[15].get 64).toNat < 2^36) :
    ∃ (callee : LIR.lifted.Location), ∃ continuation,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l101e4a else .l101a2a), args, mem⟩ = .call callee continuation ∧
      callee.label = .l1034c0 ∧
      continuation.target = (if use256 then .l101eeb else .l101acb) ∧
      continuation.guard = some ⟨64, if use256 then 0x101eeb else 0x101acb⟩ ∧
      callee.arguments[4]'(by change 4 < 53; decide) = ⟨64, args[4].get 64 - 8⟩ ∧
      callee.arguments[7]'(by change 7 < 53; decide) = ⟨64, args[4].get 64 + 80⟩ ∧
      callee.arguments[6]'(by change 6 < 53; decide) = ⟨64, args[4].get 64 + 16⟩ ∧
      (∀ r : Fin 53, r.val ∈ [5,12,13,14,22,39,50,51] → callee.arguments[r] = args[r]) ∧
      (GPRsTyped args → GPRsTyped callee.arguments) ∧
      RamWriteFrame mem callee.store [span (args[4].get 64 - 8) 40] ∧
      memLoad callee.store (args[4].get 64 - 8) 64 =
        (if use256 then 0x101eeb else 0x101acb) ∧
      memLoad callee.store (args[4].get 64 + 16) 64 = args[15].get 64 <<< 3 ∧
      memLoad callee.store (args[4].get 64 + 24) 64 = args[3].get 64 <<< 3 := by
  obtain ⟨callee, continuation, hcall, hlabel, htarget, hguard, hsp, hcontext, hsource,
    hpreserved, htyped, hmemory⟩ := length_runBlock_state use256 code hcode args mem hstack
  refine ⟨callee, continuation, hcall, hlabel, htarget, hguard, hsp, hcontext, hsource,
    hpreserved, htyped, ?_, ?_, ?_, ?_⟩
  · rw [hmemory]
    have hlow := hstack.readable.low
    exact lengthMemory_frame mem _ _ _ _ (by bv_omega) hlow
  · rw [hmemory]
    exact lengthMemory_return mem _ _ _ _
  · rw [hmemory]
    exact (lengthMemory_words mem _ _ _ _ hmessage).1
  · rw [hmemory]
    exact (lengthMemory_words mem _ _ _ _ hmessage).2

end AesGcm.Proofs.Machine.Tag.Execution
