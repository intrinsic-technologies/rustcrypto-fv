import AesGcm.Proofs.Machine.Runtime.Tactics
import AesGcm.Proofs.Machine.LIR.Program
import AesGcm.Proofs.Common.Bitwise

namespace AesGcm.Proofs.Machine.Core.Decrypt

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime


theorem xor_zero_flag {n : Nat} (a b : BitVec n) :
    (xorFlags (a ^^^ b)).ZF.getD false = decide (a = b) := by
  apply Bool.eq_iff_iff.mpr
  simp [xorFlags, BitVec.xor_eq_zero_iff]

theorem comparisonByte_eq {n : Nat} (a b c d x y : BitVec 64) :
    BitVec.setWidth 8
    (if
        (xorFlags
          (BitVec.setWidth 16
            (BitVec.setWidth 8
              (if (xorFlags (0 : BitVec n)).ZF.getD false = false then (0 : BitVec 64)
              else BitVec.setWidth 64
                (BitVec.setWidth 8
                  (if (xorFlags (b ^^^ d)).ZF.getD false = false then (0 : BitVec 64)
                  else BitVec.setWidth 64
                    (BitVec.setWidth 8
                      (if (xorFlags (a ^^^ c)).ZF.getD false = false then (0 : BitVec 64)
                      else mergeGPR 16 1 y)))))) ^^^
              BitVec.setWidth 16 (mergeGPR 16 1 x))).ZF.getD false = true then
      BitVec.setWidth 32 (mergeGPR 16 1 x)
    else 0) = (if a = c ∧ b = d then 1 else 0) := by
  simp only [show (xorFlags (0 : BitVec n)).ZF.getD false = true by rfl,
    Bool.true_eq_false, ↓reduceIte, xor_zero_flag, AesGcm.Proofs.setWidth_mergeGPR16]
  by_cases h1 : a = c <;> by_cases h2 : b = d
  all_goals simp [h1, h2, AesGcm.Proofs.setWidth_mergeGPR_of_le, BitVec.setWidth_setWidth_of_le]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
theorem authenticate_runBlock (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) (args : Values Value Reg.count) (mem : Ram)
    (hstack : Writable code mem (args[4].get 64 + 0x10) 1)
    (hcomputed : Readable mem (args[4].get 64 + 0x88) 16)
    (hprovided : Readable mem (args[13].get 64) 16) :
    ∃ next,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l1027e8 else .l102388), args, mem⟩ = .jump next ∧
      next.label = (if memLoad mem (args[4].get 64 + 0x88) 64 = memLoad mem (args[13].get 64) 64 ∧
          memLoad mem (args[4].get 64 + 0x90) 64 = memLoad mem (args[13].get 64 + 8) 64
        then (if use256 then .l102849 else .l1023e9)
        else (if use256 then .l102961 else .l102501)) ∧
      next.store = memStore mem (args[4].get 64 + 0x10)
        (if memLoad mem (args[4].get 64 + 0x88) 64 = memLoad mem (args[13].get 64) 64 ∧
          memLoad mem (args[4].get 64 + 0x90) 64 = memLoad mem (args[13].get 64 + 8) 64
        then (1 : BitVec 8) else 0) ∧
      next.arguments[0].get 8 =
        (if memLoad mem (args[4].get 64 + 0x88) 64 = memLoad mem (args[13].get 64) 64 ∧
          memLoad mem (args[4].get 64 + 0x90) 64 = memLoad mem (args[13].get 64 + 8) 64
        then 0 else 1) ∧
      (∀ r : Fin 53, r.val ∈ [3,4,5,12,13,14,15,22,39,50,51] → next.arguments[r] = args[r]) ∧
      (GPRsTyped args → GPRsTyped next.arguments) := by
  have hhelperApart {m : Ram} {a : BitVec 64} {n : Nat}
      (h : Writable code m a n) :
      RangeApart a n (if use256 then 0x1027e8 else 0x102388) 97 := by
    cases use256
    · exact (storeOk_of_codeRange h (fun x hx => hcode x (LIR.code_l102388 x hx))).apart
    · exact (storeOk_of_codeRange h (fun x hx => hcode x (LIR.code_l1027e8 x hx))).apart
  cases use256
  all_goals
    simp only [Bool.false_eq_true, ↓reduceIte] at hhelperApart
    by_cases hfirst : memLoad mem (args[4].get 64 + 0x88) 64 = memLoad mem (args[13].get 64) 64
    all_goals by_cases hsecond : memLoad mem (args[4].get 64 + 0x90) 64 = memLoad mem (args[13].get 64 + 8) 64
    all_goals
      simp only [hfirst, hsecond, and_self, and_false, false_and, ↓reduceIte]
      have hcomparison := comparisonByte_eq (n := 64)
        (memLoad mem (args[4].get 64 + 0x88) 64)
        (memLoad mem (args[4].get 64 + 0x90) 64)
        (memLoad mem (args[13].get 64) 64)
        (memLoad mem (args[13].get 64 + 8) 64)
        (args[1].get 64) (args[9].get 64)
      conv at hcomparison => rhs; simp only [hfirst, hsecond, and_self, and_false, false_and, ↓reduceIte]
      have htest (b : BitVec 8) :
          (cmpSpec (memLoad (memStore mem (args[4].get 64 + 16) b)
            (args[4].get 64 + 16) 8) 0).ZF = (b == 0) := by
        rw [memLoad_memStore_same _ _ _ (by decide) (by decide)]
        exact cmpSpec_ZF b 0
      runtime_context [hcomparison]
      refine ⟨?_, ?exec, ?_, ?_, ?_, ?_, ?_⟩
      case exec =>
        first
          | change LIR.program.runBlock (dialect code) ⟨.l102388, args, mem⟩ = _
          | change LIR.program.runBlock (dialect code) ⟨.l1027e8, args, mem⟩ = _
        cfg_eval []
        simp only [Bool.not_eq_true']
        simp only [hcomparison]
        simp only [htest, BitVec.reduceBEq, Bool.false_eq_true, ↓reduceIte]
        runtime_guards transfer
        rfl
      all_goals first
        | rfl
        | (intro hTypes; runtime_typed)
        | (rintro ⟨r, hr⟩ hin; simp only [List.mem_cons, List.not_mem_nil, or_false] at hin;
            rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
        | runtime_finish [hfirst, hsecond, setWidth_mergeGPR8]

end AesGcm.Proofs.Machine.Core.Decrypt
