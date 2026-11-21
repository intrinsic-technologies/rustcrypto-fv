import AesGcm.Proofs.Machine.LIR
import AesGcm.Proofs.Machine.Runtime.Tactics

namespace AesGcm.Proofs.Machine.CTR
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

def batchMixLabel (use256 mix3 : Bool) : LIR.Label :=
  if use256 then (if mix3 then .l109326 else .l10902f)
  else (if mix3 then .l107e96 else .l107b9f)

def batchMixReturn (use256 mix3 : Bool) : BitVec 64 :=
  if use256 then (if mix3 then 0x10932e else 0x109037)
  else (if mix3 then 0x107e9e else 0x107ba7)

def batchMixFrame (use256 mix3 : Bool) : StackFrame Value LIR.Label signature Reg.count :=
  { target := if use256 then (if mix3 then .l10932e else .l109037)
      else (if mix3 then .l107e9e else .l107ba7), kept := #v[], arity := rfl,
    guard := some ⟨64, batchMixReturn use256 mix3⟩ }

set_option maxHeartbeats 400000 in
theorem batch_mix_call (use256 mix3 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (args : Values Value Reg.count) (mem : Ram) (sp base : BitVec 64)
    (hTypes : GPRsTyped args) (hsp : args[4].get 64 = sp)
    (hbase : args[3].get 64 = base) (hStack : Writable code mem (sp - 8) 8) :
    ∃ callee : LIR.lifted.Location,
      LIR.program.runBlock (dialect code) ⟨batchMixLabel use256 mix3, args, mem⟩ =
        .call callee (batchMixFrame use256 mix3) ∧
      callee.label = (if mix3 then .l100830 else .l1002a0) ∧
      callee.arguments[4]'(by change 4 < 53; decide) = ⟨64, sp - 8⟩ ∧
      callee.arguments[7]'(by change 7 < 53; decide) = ⟨64, base⟩ ∧
      callee.store = memStore mem (sp - 8) (batchMixReturn use256 mix3) ∧
      (∀ r : Fin 53, r.val ∈ [3,5,12,13,14,15,22,39,50,51] → callee.arguments[r] = args[r]) ∧
      GPRsTyped callee.arguments ∧
      RamWriteFrame mem callee.store [span (sp - 8) 8] := by
  have hStackRead := hStack.readable
  have hStackLow := hStackRead.low
  runtime_context [hsp, hbase]
  have hRange {m : Ram} {a : BitVec 64} {n : Nat}
      (h : Writable code m a n) : RangeApart a n
        (if use256 then (if mix3 then 0x109326 else 0x10902f)
         else (if mix3 then 0x107e96 else 0x107b9f)) 8 := by
    cases use256 <;> cases mix3
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l107b9f x hx))).apart
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l107e96 x hx))).apart
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l10902f x hx))).apart
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l109326 x hx))).apart
  cases use256 <;> cases mix3
  all_goals
    have hhelperApart := @hRange
    simp only [Bool.false_eq_true, ↓reduceIte] at hhelperApart
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    rotate_left
    · first
      | change LIR.program.runBlock (dialect code) ⟨.l107b9f, args, mem⟩ = _
      | change LIR.program.runBlock (dialect code) ⟨.l107e96, args, mem⟩ = _
      | change LIR.program.runBlock (dialect code) ⟨.l10902f, args, mem⟩ = _
      | change LIR.program.runBlock (dialect code) ⟨.l109326, args, mem⟩ = _
      cfg_eval [LIR.program, batchMixFrame, batchMixReturn, hsp, hbase]
      runtime_guards call
      rfl
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
