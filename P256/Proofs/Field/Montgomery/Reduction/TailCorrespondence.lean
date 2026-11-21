import P256.Proofs.Field.Montgomery.Reduction.RoundsCorrespondence
import P256.Proofs.Field.Montgomery.Reduction.CorrectionArithmetic
import P256.Proofs.Field.Montgomery.Reduction.BorrowLow
import P256.Proofs.Field.Montgomery.Reduction.BorrowMiddle
import P256.Proofs.Field.Montgomery.Reduction.BorrowHigh
import P256.Proofs.Field.Montgomery.Reduction.BorrowTop
import P256.Proofs.Field.Montgomery.Reduction.Correction

set_option autoImplicit false

namespace P256.Proofs.Field.Montgomery.Reduction

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.SecretKeyFromBytes.Scalar (Limbs)
open P256.Proofs.Common.Instructions.Carry (adcSpec adcSpec_result adcSpec_cf)

theorem adcSpec_ofBool (x y : BitVec 64) (c : Bool) :
    (adcSpec x y (BitVec.ofBool c)).1 = adc x y c := by
  rw [adcSpec_result]
  cases c <;> rfl

theorem adcSpec_cf_ofBool (x y : BitVec 64) (c : Bool) :
    (adcSpec x y (BitVec.ofBool c)).2.CF = carry x y c := by
  rw [adcSpec_cf]
  cases c <;> rfl

theorem addSpec_cf_carry (x y : BitVec 64) :
    (addSpec x y).2.CF = carry x y false := by
  simp only [addSpec, carry, BitVec.toNat_add, Bool.toNat_false, Nat.add_zero,
    ne_eq, Nat.mod_eq_iff_lt (by decide : 2^64 ≠ 0), Nat.not_lt]

def outputLimbs (s : RamState) : Limbs :=
  ⟨(Operand.reg 2 : Operand 64).read s, (Operand.reg 9 : Operand 64).read s,
    (Operand.reg 3 : Operand 64).read s, (Operand.reg 1 : Operand 64).read s⟩

theorem correction_correspondence {s t : RamState} (h : (correctionEffect s).Holds s t)
    (hk : (Operand.reg 11 : Operand 64).read s = 0xffffffff00000001) :
    outputLimbs t = correct
      ⟨(Operand.reg 0 : Operand 64).read s, (Operand.reg 8 : Operand 64).read s,
        (Operand.reg 10 : Operand 64).read s, (Operand.reg 6 : Operand 64).read s⟩
      ((Operand.reg 1 : Operand 64).read s) := by
  have hw := h.writes
  dsimp only [correctionEffect, Write.AllHold] at hw
  rcases hw with ⟨h1, h2, h3, h9⟩
  have addLow (a b : BitVec 64) : (addSpec a b).1 = a + b := rfl
  simp only [outputLimbs, h1, h2, h3, h9, hk]
  simp only [addLow, setb_zero,
    adcSpec_ofBool, adcSpec_cf_ofBool, addSpec_cf_carry,
    cmpSpec, subSpec, correct, BitVec.lt_def, BitVec.and_comm]
  simp only [BitVec.ofNat_eq_ofNat]
  rfl

set_option maxHeartbeats 800000 in
theorem tail_correspondence {s t u v w x : RamState} {c1 : Bool}
    (h1 : (borrowLowEffect s).Holds s t)
    (h2 : (borrowMiddleEffect t).Holds t u)
    (h3 : (borrowHighEffect u).Holds u v)
    (h4 : (borrowTopEffect v).Holds v w)
    (h5 : (correctionEffect w).Holds w x)
    (hk : (Operand.reg 11 : Operand 64).read s = 0xffffffff00000001)
    (hn : (Operand.reg 3 : Operand 64).read s = 0xffffffff)
    (hb : ((Operand.reg 1 : Operand 64).read s).setWidth 8 = BitVec.ofNat 8 c1.toNat) :
    outputLimbs x = rawTail ((Operand.reg 12 : Operand 64).read s)
      ((Operand.reg 15 : Operand 64).read s) ((Operand.reg 6 : Operand 64).read s)
      ((Operand.reg 2 : Operand 64).read s) ((Operand.reg 9 : Operand 64).read s)
      (StatusFlags.ofRFLAGS s.RFLAGS).CF c1 := by
  have hw1 := h1.writes
  dsimp only [borrowLowEffect, Write.AllHold] at hw1
  rcases hw1 with ⟨g1r0, g1r5, g1r8, g1r12, g1r14, _⟩
  have g1r1 : ((Operand.reg 1 : Operand 64).read t) = ((Operand.reg 1 : Operand 64).read s) := h1.agrees.read (by simp [borrowLowEffect, Effect.components])
  have g1r2 : ((Operand.reg 2 : Operand 64).read t) = ((Operand.reg 2 : Operand 64).read s) := h1.agrees.read (by simp [borrowLowEffect, Effect.components])
  have g1r3 : ((Operand.reg 3 : Operand 64).read t) = ((Operand.reg 3 : Operand 64).read s) := h1.agrees.read (by simp [borrowLowEffect, Effect.components])
  have g1r4 : ((Operand.reg 4 : Operand 64).read t) = ((Operand.reg 4 : Operand 64).read s) := h1.agrees.read (by simp [borrowLowEffect, Effect.components])
  have g1r6 : ((Operand.reg 6 : Operand 64).read t) = ((Operand.reg 6 : Operand 64).read s) := h1.agrees.read (by simp [borrowLowEffect, Effect.components])
  have g1r7 : ((Operand.reg 7 : Operand 64).read t) = ((Operand.reg 7 : Operand 64).read s) := h1.agrees.read (by simp [borrowLowEffect, Effect.components])
  have g1r9 : ((Operand.reg 9 : Operand 64).read t) = ((Operand.reg 9 : Operand 64).read s) := h1.agrees.read (by simp [borrowLowEffect, Effect.components])
  have g1r10 : ((Operand.reg 10 : Operand 64).read t) = ((Operand.reg 10 : Operand 64).read s) := h1.agrees.read (by simp [borrowLowEffect, Effect.components])
  have g1r11 : ((Operand.reg 11 : Operand 64).read t) = ((Operand.reg 11 : Operand 64).read s) := h1.agrees.read (by simp [borrowLowEffect, Effect.components])
  have g1r13 : ((Operand.reg 13 : Operand 64).read t) = ((Operand.reg 13 : Operand 64).read s) := h1.agrees.read (by simp [borrowLowEffect, Effect.components])
  have g1r15 : ((Operand.reg 15 : Operand 64).read t) = ((Operand.reg 15 : Operand 64).read s) := h1.agrees.read (by simp [borrowLowEffect, Effect.components])
  have hw2 := h2.writes
  dsimp only [borrowMiddleEffect, Write.AllHold] at hw2
  simp only [g1r8, g1r11, g1r15] at hw2
  rcases hw2 with ⟨g2r8, g2r10, g2r15, _⟩
  have g2r0 : ((Operand.reg 0 : Operand 64).read u) = ((Operand.reg 0 : Operand 64).read t) := h2.agrees.read (by simp [borrowMiddleEffect, Effect.components])
  rw [g1r0] at g2r0
  have g2r1 : ((Operand.reg 1 : Operand 64).read u) = ((Operand.reg 1 : Operand 64).read t) := h2.agrees.read (by simp [borrowMiddleEffect, Effect.components])
  rw [g1r1] at g2r1
  have g2r2 : ((Operand.reg 2 : Operand 64).read u) = ((Operand.reg 2 : Operand 64).read t) := h2.agrees.read (by simp [borrowMiddleEffect, Effect.components])
  rw [g1r2] at g2r2
  have g2r3 : ((Operand.reg 3 : Operand 64).read u) = ((Operand.reg 3 : Operand 64).read t) := h2.agrees.read (by simp [borrowMiddleEffect, Effect.components])
  rw [g1r3] at g2r3
  have g2r4 : ((Operand.reg 4 : Operand 64).read u) = ((Operand.reg 4 : Operand 64).read t) := h2.agrees.read (by simp [borrowMiddleEffect, Effect.components])
  rw [g1r4] at g2r4
  have g2r5 : ((Operand.reg 5 : Operand 64).read u) = ((Operand.reg 5 : Operand 64).read t) := h2.agrees.read (by simp [borrowMiddleEffect, Effect.components])
  rw [g1r5] at g2r5
  have g2r6 : ((Operand.reg 6 : Operand 64).read u) = ((Operand.reg 6 : Operand 64).read t) := h2.agrees.read (by simp [borrowMiddleEffect, Effect.components])
  rw [g1r6] at g2r6
  have g2r7 : ((Operand.reg 7 : Operand 64).read u) = ((Operand.reg 7 : Operand 64).read t) := h2.agrees.read (by simp [borrowMiddleEffect, Effect.components])
  rw [g1r7] at g2r7
  have g2r9 : ((Operand.reg 9 : Operand 64).read u) = ((Operand.reg 9 : Operand 64).read t) := h2.agrees.read (by simp [borrowMiddleEffect, Effect.components])
  rw [g1r9] at g2r9
  have g2r11 : ((Operand.reg 11 : Operand 64).read u) = ((Operand.reg 11 : Operand 64).read t) := h2.agrees.read (by simp [borrowMiddleEffect, Effect.components])
  rw [g1r11] at g2r11
  have g2r12 : ((Operand.reg 12 : Operand 64).read u) = ((Operand.reg 12 : Operand 64).read t) := h2.agrees.read (by simp [borrowMiddleEffect, Effect.components])
  rw [g1r12] at g2r12
  have g2r13 : ((Operand.reg 13 : Operand 64).read u) = ((Operand.reg 13 : Operand 64).read t) := h2.agrees.read (by simp [borrowMiddleEffect, Effect.components])
  rw [g1r13] at g2r13
  have g2r14 : ((Operand.reg 14 : Operand 64).read u) = ((Operand.reg 14 : Operand 64).read t) := h2.agrees.read (by simp [borrowMiddleEffect, Effect.components])
  rw [g1r14] at g2r14
  have hw3 := h3.writes
  dsimp only [borrowHighEffect, Write.AllHold] at hw3
  simp only [g2r2, g2r5, g2r6, g2r9, g2r10] at hw3
  rcases hw3 with ⟨g3r2, g3r5, g3r6, g3r10, g3r15, _⟩
  have g3r0 : ((Operand.reg 0 : Operand 64).read v) = ((Operand.reg 0 : Operand 64).read u) := h3.agrees.read (by simp [borrowHighEffect, Effect.components])
  rw [g2r0] at g3r0
  have g3r1 : ((Operand.reg 1 : Operand 64).read v) = ((Operand.reg 1 : Operand 64).read u) := h3.agrees.read (by simp [borrowHighEffect, Effect.components])
  rw [g2r1] at g3r1
  have g3r3 : ((Operand.reg 3 : Operand 64).read v) = ((Operand.reg 3 : Operand 64).read u) := h3.agrees.read (by simp [borrowHighEffect, Effect.components])
  rw [g2r3] at g3r3
  have g3r4 : ((Operand.reg 4 : Operand 64).read v) = ((Operand.reg 4 : Operand 64).read u) := h3.agrees.read (by simp [borrowHighEffect, Effect.components])
  rw [g2r4] at g3r4
  have g3r7 : ((Operand.reg 7 : Operand 64).read v) = ((Operand.reg 7 : Operand 64).read u) := h3.agrees.read (by simp [borrowHighEffect, Effect.components])
  rw [g2r7] at g3r7
  have g3r8 : ((Operand.reg 8 : Operand 64).read v) = ((Operand.reg 8 : Operand 64).read u) := h3.agrees.read (by simp [borrowHighEffect, Effect.components])
  rw [g2r8] at g3r8
  have g3r9 : ((Operand.reg 9 : Operand 64).read v) = ((Operand.reg 9 : Operand 64).read u) := h3.agrees.read (by simp [borrowHighEffect, Effect.components])
  rw [g2r9] at g3r9
  have g3r11 : ((Operand.reg 11 : Operand 64).read v) = ((Operand.reg 11 : Operand 64).read u) := h3.agrees.read (by simp [borrowHighEffect, Effect.components])
  rw [g2r11] at g3r11
  have g3r12 : ((Operand.reg 12 : Operand 64).read v) = ((Operand.reg 12 : Operand 64).read u) := h3.agrees.read (by simp [borrowHighEffect, Effect.components])
  rw [g2r12] at g3r12
  have g3r13 : ((Operand.reg 13 : Operand 64).read v) = ((Operand.reg 13 : Operand 64).read u) := h3.agrees.read (by simp [borrowHighEffect, Effect.components])
  rw [g2r13] at g3r13
  have g3r14 : ((Operand.reg 14 : Operand 64).read v) = ((Operand.reg 14 : Operand 64).read u) := h3.agrees.read (by simp [borrowHighEffect, Effect.components])
  rw [g2r14] at g3r14
  have hw4 := h4.writes
  dsimp only [borrowTopEffect, Write.AllHold] at hw4
  simp only [g3r1, g3r2, g3r3, g3r4, g3r6, g3r9, g3r14, g3r15] at hw4
  rcases hw4 with ⟨g4r1, g4r2, g4r3, g4r6, g4r14, g4r15, _⟩
  have g4r0 : ((Operand.reg 0 : Operand 64).read w) = ((Operand.reg 0 : Operand 64).read v) := h4.agrees.read (by simp [borrowTopEffect, Effect.components])
  rw [g3r0] at g4r0
  have g4r4 : ((Operand.reg 4 : Operand 64).read w) = ((Operand.reg 4 : Operand 64).read v) := h4.agrees.read (by simp [borrowTopEffect, Effect.components])
  rw [g3r4] at g4r4
  have g4r5 : ((Operand.reg 5 : Operand 64).read w) = ((Operand.reg 5 : Operand 64).read v) := h4.agrees.read (by simp [borrowTopEffect, Effect.components])
  rw [g3r5] at g4r5
  have g4r7 : ((Operand.reg 7 : Operand 64).read w) = ((Operand.reg 7 : Operand 64).read v) := h4.agrees.read (by simp [borrowTopEffect, Effect.components])
  rw [g3r7] at g4r7
  have g4r8 : ((Operand.reg 8 : Operand 64).read w) = ((Operand.reg 8 : Operand 64).read v) := h4.agrees.read (by simp [borrowTopEffect, Effect.components])
  rw [g3r8] at g4r8
  have g4r9 : ((Operand.reg 9 : Operand 64).read w) = ((Operand.reg 9 : Operand 64).read v) := h4.agrees.read (by simp [borrowTopEffect, Effect.components])
  rw [g3r9] at g4r9
  have g4r10 : ((Operand.reg 10 : Operand 64).read w) = ((Operand.reg 10 : Operand 64).read v) := h4.agrees.read (by simp [borrowTopEffect, Effect.components])
  rw [g3r10] at g4r10
  have g4r11 : ((Operand.reg 11 : Operand 64).read w) = ((Operand.reg 11 : Operand 64).read v) := h4.agrees.read (by simp [borrowTopEffect, Effect.components])
  rw [g3r11] at g4r11
  have g4r12 : ((Operand.reg 12 : Operand 64).read w) = ((Operand.reg 12 : Operand 64).read v) := h4.agrees.read (by simp [borrowTopEffect, Effect.components])
  rw [g3r12] at g4r12
  have g4r13 : ((Operand.reg 13 : Operand 64).read w) = ((Operand.reg 13 : Operand 64).read v) := h4.agrees.read (by simp [borrowTopEffect, Effect.components])
  rw [g3r13] at g4r13
  rw [correction_correspondence h5 (g4r11.trans hk)]
  simp only [g4r0, g4r8, g4r10, g4r6, g4r1, hk, hn]
  have addLow (a b : BitVec 64) : (addSpec a b).1 = a + b := rfl
  have narrow (a : BitVec 64) : (a.setWidth 32 |>.setWidth 64).setWidth 8 = a.setWidth 8 := by
    rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_setWidth_of_le _ (by decide)]
  simp only [narrow, P256.Proofs.Common.Instructions.ByteOps.ByteOps.mergeGPR_low8, low8_word,
    P256.Proofs.Common.Field.Montgomery.Schoolbook.savedCarry_add_ff, hb, widen_carry]
  simp only [rawTail, add64, adc64]
  simp only [addLow, subSpec]
  simp only [BitVec.ofNat_eq_ofNat, BitVec.zero_sub, BitVec.add_zero]
  simp only [BitVec.add_comm]


end P256.Proofs.Field.Montgomery.Reduction
