import AesGcm.Proofs.Machine.CTR.KeyLoop
import AesGcm.Proofs.Machine.Runtime.Tactics

namespace AesGcm.Proofs.Machine.CTR
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

def keyCopyReturn (use256 : Bool) : BitVec 64 := if use256 then 0x108590 else 0x107100

def keyCopyFrame (use256 : Bool) : StackFrame Value LIR.Label signature Reg.count :=
  { target := if use256 then .l108590 else .l107100, kept := #v[], arity := rfl,
    guard := some ⟨64, keyCopyReturn use256⟩ }

set_option maxHeartbeats 800000 in
theorem keyCopy_prepare (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (args : Values Value Reg.count) (mem : Ram) (sp : BitVec 64)
    (hTypes : GPRsTyped args) (hsp : args[4].get 64 = sp)
    (hStack : Writable code mem (sp - 8) 352)
    (hSlotRead : Readable mem 0x201208 8)
    (hSlot : memLoad mem 0x201208 64 = 0x103f00)
    (hApart : sp.toNat + 344 ≤ 0x201208 ∨ 0x201210 ≤ sp.toNat - 8) :
    ∃ callee : LIR.lifted.Location,
      LIR.program.runBlock (dialect code) ⟨wideningExit use256, args, mem⟩ =
        .call callee (keyCopyFrame use256) ∧
      callee.label = .l103f00 ∧
      callee.arguments[4]'(by change 4 < 53; decide) = ⟨64, sp - 8⟩ ∧
      callee.arguments[7]'(by change 7 < 53; decide) = ⟨64, sp + 0x158⟩ ∧
      callee.arguments[6]'(by change 6 < 53; decide) = ⟨64, sp + wideningOffset use256⟩ ∧
      callee.arguments[2]'(by change 2 < 53; decide) = ⟨64, BitVec.ofNat 64 (8 * keyWords use256)⟩ ∧
      callee.store = memStore (memStore mem (sp + 0x150) (args[0].get 64))
        (sp - 8) (keyCopyReturn use256) ∧
      (∀ r : Fin 53, r.val ∈ [0,3,5,9,11,12,13,14,15,22,39,50,51] →
        callee.arguments[r.val]'(by exact r.isLt) = args[r]) ∧
      GPRsTyped callee.arguments ∧
      RamWriteFrame mem callee.store [span (sp - 8) 352] := by
  have hStackRead := hStack.readable
  have hStackLow := hStackRead.low
  have hroom : 8 ≤ sp.toNat := by bv_omega
  have hbase : (sp - 8).toNat = sp.toNat - 8 := by bv_omega
  runtime_context [hSlot, hsp]
  have hRange {m : Ram} {a : BitVec 64} {n : Nat}
      (h : Writable code m a n) : RangeApart a n
        (if use256 then 0x10856d else 0x1070dd) 35 := by
    cases use256
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l1070dd x hx))).apart
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l10856d x hx))).apart
  cases use256
  all_goals
    have hhelperApart := @hRange
    simp only [Bool.false_eq_true, ↓reduceIte] at hhelperApart
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    rotate_left
    · first
      | change LIR.program.runBlock (dialect code) ⟨.l1070dd, args, mem⟩ = _
      | change LIR.program.runBlock (dialect code) ⟨.l10856d, args, mem⟩ = _
      cfg_eval [LIR.program, keyCopyFrame, keyCopyReturn, hsp]
      runtime_guards call
      rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rintro ⟨r,hr⟩ hin
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
      rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · runtime_typed
    · runtime_finish [span]

end AesGcm.Proofs.Machine.CTR
