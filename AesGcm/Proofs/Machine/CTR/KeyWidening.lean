import AesGcm.Proofs.Machine.LIR
import AesGcm.Proofs.Machine.Fixslice16.Widening
import AesGcm.Proofs.Machine.Runtime.Contracts
import AesGcm.Proofs.Copied.X86Proofs.Lift.Generated.Values
import AesGcm.Proofs.Copied.X86Proofs.Refine.Tactic

namespace AesGcm.Proofs.Machine.CTR
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

def wideningRegisters (args : Values Value Reg.count) (src sp index : BitVec 64) :
    Values Value Reg.count :=
  #v[⟨64, src⟩, ⟨64, index⟩, ⟨64, 0x1000001000⟩, args[3], ⟨64, sp⟩, args[5], ⟨64,
      0x000f000f000f000f⟩, ⟨64, 0x1111111111111111⟩,
    args[8], args[9], args[10], args[11], args[12], args[13], args[14], args[15],
    args[16], args[17], args[18], args[19], args[20], args[21], args[22], args[23],
    args[24], args[25], args[26], args[27], args[28], args[29], args[30], args[31],
    args[32], args[33], args[34], args[35], args[36], args[37], args[38], args[39],
    args[40], args[41], args[42], args[43], args[44], args[45], args[46], args[47],
    args[48], args[49], args[50], args[51], args[52]]


theorem wideningRegisters_eq (args : Values Value Reg.count) (src sp index : BitVec 64)
    (h0 : args[0] = ⟨64, src⟩) (h1 : args[1] = ⟨64, index⟩)
    (h2 : args[2] = ⟨64, 0x1000001000⟩) (h4 : args[4] = ⟨64, sp⟩)
    (h6 : args[6] = ⟨64, 0x000f000f000f000f⟩)
    (h7 : args[7] = ⟨64, 0x1111111111111111⟩) :
    wideningRegisters args src sp index = args := by
  apply Vector.ext
  intro i hi
  change i < 53 at hi
  have hs : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨
      i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i =
      21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 ∨
      i = 32 ∨ i = 33 ∨ i = 34 ∨ i = 35 ∨ i = 36 ∨ i = 37 ∨ i = 38 ∨ i = 39 ∨ i = 40 ∨ i = 41 ∨ i =
      42 ∨ i = 43 ∨ i = 44 ∨ i = 45 ∨ i = 46 ∨ i = 47 ∨ i = 48 ∨ i = 49 ∨ i = 50 ∨ i = 51 ∨ i = 52
      := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | rfl | exact h0.symm | exact h1.symm | exact h2.symm |
    exact h4.symm | exact h6.symm | exact h7.symm


set_option maxHeartbeats 800000 in
theorem widening_step (use256 : Bool) (code : CodeMap) (args : Values Value Reg.count)
    (src sp index : BitVec 64) (mem : Ram)
    (hTypes : GPRsTyped args)
    (hload : LoadOk mem (src + index <<< 1) 2)
    (hstore : StoreOk code mem (sp + index <<< 3 + (if use256 then 0x518 else 0x418)) 8 (if use256
        then 0x10855c else 0x1070cc) 8) :
    ∃ next : Location Value Ram LIR.Label signature,
      LIR.program.step (dialect code)
        ⟨⟨(if use256 then .l108520 else .l107090), wideningRegisters args src sp index, mem⟩, []⟩ =
            .next ⟨next, []⟩ ∧
      next.label = (if index + 1 = (if use256 then 120 else 88) then (if use256 then .l10856d else
          .l1070dd) else (if use256 then .l108520 else .l107090)) ∧
      next.store = memStore mem (sp + index <<< 3 + (if use256 then 0x518 else 0x418))
        (Fixslice16.widenWord (memLoad mem (src + index <<< 1) 16)) ∧
      next.arguments[1]'(by change 1 < 53; decide) = ⟨64, index + 1⟩ ∧
      (∀ r : Fin 53, r ≠ 1 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 19 →
        next.arguments[r.val]'(by have := r.isLt; change r.val < 53; omega) = (wideningRegisters
            args src sp index)[r.val]) ∧
      GPRsTyped next.arguments := by
  have hzf (n : BitVec 64) : (cmpSpec (index + 1) n).ZF = decide (index + 1 = n) := by
    simp only [cmpSpec, subSpec]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    constructor <;> intro h <;> bv_omega
  by_cases hb : index + 1 = (if use256 then 120 else 88)
  all_goals cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] at hb hstore ⊢
  all_goals
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    rotate_left
    · first
      | change LIR.program.step (dialect code)
          ⟨⟨.l107090, wideningRegisters args src sp index, mem⟩, []⟩ = _
      | change LIR.program.step (dialect code)
          ⟨⟨.l108520, wideningRegisters args src sp index, mem⟩, []⟩ = _
      cfg_eval [LIR.program, wideningRegisters]
      simp only [hload, hstore, ↓reduceIte, hzf]
      first
      | (simp only [hb, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]; rfl)
      | (simp only [hb, decide_false, Bool.not_false, ite_true]; rfl)
    · simp only [hb, ↓reduceIte]
    · change memStore mem _ _ = _
      rw [← Fixslice16.widenCircuit_eq_widenWord]
      congr 1
      simp only [Fixslice16.widenCircuit, BitVec.shiftLeft_eq_mul_twoPow]
      rfl
    · simp only [hb]
      rfl
    · intro r h1 h8 h9 h10 h19
      have hr : r = 0 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 11 ∨ r = 12 ∨ r = 13 ∨ r
          = 14 ∨ r = 15 ∨ r = 16 ∨ r = 17 ∨ r = 18 ∨ r = 20 ∨ r = 21 ∨ r = 22 ∨ r = 23 ∨ r = 24 ∨ r
          = 25 ∨ r = 26 ∨ r = 27 ∨ r = 28 ∨ r = 29 ∨ r = 30 ∨ r = 31 ∨ r = 32 ∨ r = 33 ∨ r = 34 ∨ r
          = 35 ∨ r = 36 ∨ r = 37 ∨ r = 38 ∨ r = 39 ∨ r = 40 ∨ r = 41 ∨ r = 42 ∨ r = 43 ∨ r = 44 ∨ r
          = 45 ∨ r = 46 ∨ r = 47 ∨ r = 48 ∨ r = 49 ∨ r = 50 ∨ r = 51 ∨ r = 52 := by
        have := r.isLt
        omega
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl <;> rfl

    · intro r
      have hr : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 9 ∨ r =
          10 ∨ r = 11 ∨ r = 12 ∨ r = 13 ∨ r = 14 ∨ r = 15 := by
        have := r.isLt
        omega
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl
      all_goals first | rfl | exact hTypes 3 | exact hTypes 5 | exact hTypes 11 | exact hTypes 12 |
          exact hTypes 13 | exact hTypes 14 | exact hTypes 15

end AesGcm.Proofs.Machine.CTR
