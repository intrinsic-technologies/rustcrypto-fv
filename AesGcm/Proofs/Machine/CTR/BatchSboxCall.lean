import AesGcm.Proofs.Machine.LIR
import AesGcm.Proofs.Machine.Runtime.Tactics

namespace AesGcm.Proofs.Machine.CTR
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

def batchSboxFrame (use256 : Bool) : StackFrame Value LIR.Label signature Reg.count :=
  { target := if use256 then .l1090e0 else .l107c50, kept := #v[], arity := rfl,
    guard := some ⟨64, if use256 then 0x1090e0 else 0x107c50⟩ }

set_option maxHeartbeats 400000 in
theorem batch_sbox_call (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (args : Values Value Reg.count) (mem : Ram) (sp : BitVec 64)
    (hTypes : GPRsTyped args) (hsp : args[4].get 64 = sp)
    (hStack : Writable code mem (sp - 8) 8) :
    ∃ callee : LIR.lifted.Location,
      LIR.program.runBlock (dialect code) ⟨(if use256 then .l1090d1 else .l107c41), args, mem⟩ =
        .call callee (batchSboxFrame use256) ∧
      callee.label = .l100e90 ∧
      callee.arguments[4]'(by change 4 < 53; decide) = ⟨64, sp - 8⟩ ∧
      callee.arguments[7]'(by change 7 < 53; decide) = ⟨64, sp + 8⟩ ∧
      callee.arguments[6]'(by change 6 < 53; decide) = ⟨64, 8⟩ ∧
      callee.store = memStore mem (sp - 8) (if use256 then 0x1090e0 else (0x107c50#64)) ∧
      (∀ r : Fin 53, r.val ∈ [3,5,12,13,14,15,22,39,50,51] → callee.arguments[r] = args[r]) ∧
      GPRsTyped callee.arguments ∧
      RamWriteFrame mem callee.store [span (sp - 8) 8] := by
  have hStackRead := hStack.readable
  have hStackLow := hStackRead.low
  runtime_context [hsp]
  have hRange {m : Ram} {a : BitVec 64} {n : Nat}
      (h : Writable code m a n) : RangeApart a n
        (if use256 then 0x1090d1 else 0x107c41) 15 := by
    cases use256
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l107c41 x hx))).apart
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l1090d1 x hx))).apart
  cases use256
  all_goals
    have hhelperApart := @hRange
    simp only [Bool.false_eq_true, ↓reduceIte] at hhelperApart
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    rotate_left
    · first
      | change LIR.program.runBlock (dialect code) ⟨.l107c41, args, mem⟩ = _
      | change LIR.program.runBlock (dialect code) ⟨.l1090d1, args, mem⟩ = _
      cfg_eval [LIR.program, batchSboxFrame, hsp]
      runtime_guards call
      rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rintro ⟨r, hr⟩ hin
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
      rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · runtime_typed
    · runtime_finish [span]

end AesGcm.Proofs.Machine.CTR
