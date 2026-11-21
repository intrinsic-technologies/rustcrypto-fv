import AesGcm.Proofs.Machine.LIR
import AesGcm.Proofs.Machine.CTR.CounterMemory
import AesGcm.Proofs.Copied.X86Proofs.Lift.Generated.Values

namespace AesGcm.Proofs.Machine.CTR
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime


def batchReturnLabel (use256 : Bool) : LIR.Label := if use256 then .l108fa2 else .l107b12

def batchReturnAddress (use256 : Bool) : BitVec 64 := if use256 then 0x108fa2 else 0x107b12

def batchFrame (use256 : Bool) : StackFrame Value LIR.Label signature Reg.count :=
  { target := batchReturnLabel use256, kept := #v[], arity := rfl,
    guard := some ⟨64, batchReturnAddress use256⟩ }

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
theorem batch_prepare_execution (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (args : Values Value Reg.count) (mem : Ram) (sp counter : BitVec 64)
    (hTypes : GPRsTyped args)
    (hsp : args[4].get 64 = sp) (hcounter : args[9].get 64 = counter)
    (hStack : Writable code mem (sp - 8) 328)
    (hCounter : Writable code mem counter 20) :
    ∃ callee : Location Value Ram LIR.Label signature,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l108e98 else .l107a08), args, mem⟩ =
          .call callee (batchFrame use256) ∧
      callee.label = .l10a690 ∧
      callee.arguments[4]'(by change 4 < 53; decide) = ⟨64, sp - 8⟩ ∧
      callee.arguments[7]'(by change 7 < 53; decide) = ⟨64, sp + 8⟩ ∧
      callee.arguments[6]'(by change 6 < 53; decide) = ⟨64, 8⟩ ∧
      callee.arguments[2]'(by change 2 < 53; decide) = ⟨64, sp + 256⟩ ∧
      callee.store = batchMemory mem sp counter (batchReturnAddress use256) ∧
      (∀ r : Fin 53, r.val ∈ [3, 5, 9, 12, 13, 14, 15, 22, 39, 50, 51] →
        callee.arguments[r.val]'(by exact r.isLt) = args[r.val]) ∧
      GPRsTyped callee.arguments := by
  have hStackRead := hStack.readable
  have hCounterRead := hCounter.readable
  have hStackLow := hStackRead.low
  have hCounterLow := hCounterRead.low
  have hRange {m : Ram} {a : BitVec 64} {n : Nat}
        (h : Writable code m a n) : RangeApart a n (if use256 then 0x108e98 else 0x107a08) 266 := by
      cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte]
      all_goals first
      | (have hh := storeOk_of_codeRange h (fun x hx => hcode x (LIR.code_l107a08 x hx));
         have hn : LIR.bytes_l107a08.length = 266 := by decide +kernel;
         rw [hn] at hh; exact hh.apart)
      | (have hh := storeOk_of_codeRange h (fun x hx => hcode x (LIR.code_l108e98 x hx));
         have hn : LIR.bytes_l108e98.length = 266 := by decide +kernel;
         rw [hn] at hh; exact hh.apart)
  cases use256
  all_goals
    have hhelperApart := @hRange
    simp only [Bool.false_eq_true, ↓reduceIte] at hhelperApart
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    rotate_left
    ·
      first
      | change LIR.program.runBlock (dialect code) ⟨.l107a08, args, mem⟩ = _
      | change LIR.program.runBlock (dialect code) ⟨.l108e98, args, mem⟩ = _
      cfg_eval [LIR.program, batchFrame, batchReturnLabel, batchReturnAddress, hsp, hcounter]
      runtime_guards call
      rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · change _ = batchMemory mem sp counter (batchReturnAddress _)
      dsimp only [batchMemory]
      simp (config := {bitVecOfNat := false}) only [batchReturnAddress, Bool.false_eq_true, ↓reduceIte,
        BitVec.setWidth_add _ _ (show 32 ≤ 64 by decide),
        BitVec.setWidth_setWidth_of_le _ (show 32 ≤ 64 by decide), BitVec.setWidth_eq]
      repeat apply congrArg₂ (fun (m : Ram) (v : BitVec _) ↦ memStore m _ v)
      all_goals rfl
    · rintro ⟨r,hrbound⟩ hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals rfl
    · runtime_typed

end AesGcm.Proofs.Machine.CTR
