import AesGcm.Proofs.Machine.LIR
import AesGcm.Proofs.Machine.Runtime.Tactics

namespace AesGcm.Proofs.Machine.CTR
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

def batchHeaderFrame (use256 : Bool) : StackFrame Value LIR.Label signature Reg.count :=
  { target := if use256 then .l10902f else .l107b9f, kept := #v[], arity := rfl,
    guard := some ⟨64, if use256 then 0x10902f else 0x107b9f⟩ }

set_option maxHeartbeats 800000 in
theorem batch_header (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (args : Values Value Reg.count) (mem : Ram) (sp index tail key : BitVec 64)
    (hTypes : GPRsTyped args) (hsp : args[4].get 64 = sp)
    (hIndex : args[5].get 64 = index)
    (hTail : (args[if use256 then 15 else 14]'(by cases use256 <;> decide)).get 64 = tail)
    (hStack : Writable code mem (sp - 8) 80)
    (hKeyRead : Readable mem (sp + (index <<< 3) + (if use256 then 336 else 400)) 8)
    (hKey : memLoad mem (sp + (index <<< 3) + (if use256 then 336 else 400)) 64 = key) :
    ∃ callee : LIR.lifted.Location,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l109010 else .l107b80), args, mem⟩ = .call callee (batchHeaderFrame use256) ∧
      callee.label = .l100e90 ∧
      callee.arguments[4]'(by change 4 < 53; decide) = ⟨64, sp - 8⟩ ∧
      callee.arguments[7]'(by change 7 < 53; decide) = ⟨64, sp + 8⟩ ∧
      callee.arguments[6]'(by change 6 < 53; decide) = ⟨64, 8⟩ ∧
      callee.arguments[3]'(by change 3 < 53; decide) = ⟨64, sp + 8⟩ ∧
      callee.store = memStore (memStore mem (sp + 64) (tail ^^^ key)) (sp - 8)
        (if use256 then (0x10902f#64) else 0x107b9f) ∧
      (∀ r : Fin 53, r.val ∈ [5,12,13,22,39,50,51] → callee.arguments[r] = args[r]) ∧
      GPRsTyped callee.arguments ∧
      RamWriteFrame mem callee.store [span (sp - 8) 8, span (sp + 64) 8] := by
  have hStackRead := hStack.readable
  have hStackLow := hStackRead.low
  have hKeyLow := hKeyRead.low
  have hroom : 8 ≤ sp.toNat := by bv_omega
  have hRange {m : Ram} {a : BitVec 64} {n : Nat}
      (h : Writable code m a n) : RangeApart a n
        (if use256 then 0x109010 else 0x107b80) 31 := by
    cases use256
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l107b80 x hx))).apart
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l109010 x hx))).apart
  cases use256
  all_goals
    have hhelperApart := @hRange
    simp only [Bool.false_eq_true, ↓reduceIte] at hhelperApart hKeyRead hKey hKeyLow hTail
    runtime_context [hsp, hIndex, hTail, hKey]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    rotate_left
    · first
      | change LIR.program.runBlock (dialect code) ⟨.l107b80, args, mem⟩ = _
      | change LIR.program.runBlock (dialect code) ⟨.l109010, args, mem⟩ = _
      cfg_eval [LIR.program, batchHeaderFrame, hsp, hIndex]
      runtime_guards call
      rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · simp only [hTail, hKey, Bool.false_eq_true, ↓reduceIte]
      all_goals rfl
    · rintro ⟨r, hr⟩ hin
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
      rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · runtime_typed
    · runtime_finish [span]

end AesGcm.Proofs.Machine.CTR
