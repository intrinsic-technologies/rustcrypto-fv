import P256.Proofs.Field.Montgomery.Reduction.TailCorrespondence
import P256.Proofs.Field.Montgomery.Reduction.Body

set_option autoImplicit false

open P256.Proofs.SecretKeyFromBytes.Scalar (Limbs)

namespace P256.Proofs.Field.Montgomery.Reduction

open P256.Spec.Program.Routines P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem fourthRound_carryByte {s t : RamState} (h : (fourthRoundEffect s).Holds s t) :
    ((Operand.reg 1 : Operand 64).read t).setWidth 8 =
      BitVec.ofNat 8 (((Operand.reg 1 : Operand 64).read t).setWidth 8 |>.getLsbD 0).toNat := by
  have hr := h.writes.2.1
  change (Operand.reg 1 : Operand 64).read t = _ at hr
  rw [hr]
  simp only [P256.Proofs.Common.Instructions.ByteOps.ByteOps.mergeGPR_low8, low8_word]
  cases (P256.Proofs.Common.Instructions.Carry.adcSpec
    ((((Operand.reg 2 : Operand 64).read s).setWidth 8).setWidth 64)
    ((Operand.mem ((Operand.reg 1 : Operand 64).read s + 24) : Operand 64).read s)
    (BitVec.ofBool (addSpec ((Operand.reg 6 : Operand 64).read s)
      ((Operand.reg 13 : Operand 64).read s)).2.CF)).2.CF <;> rfl

theorem body_value {s t : RamState} (trace : BodyTrace s t)
    (bound : (readLimbs s ((Operand.reg 6 : Operand 64).read s)).toNat +
      2^256*(readLimbs s ((Operand.reg 2 : Operand 64).read s)).toNat <
      P256.Proofs.Field.Montgomery.p*2^256) :
    (outputLimbs t).toNat = P256.Proofs.Field.Montgomery.subtractP
      (P256.Proofs.Field.Montgomery.reduceFour
        ((readLimbs s ((Operand.reg 6 : Operand 64).read s)).toNat +
          2^256*(readLimbs s ((Operand.reg 2 : Operand 64).read s)).toNat)) := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10,
    e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩ := trace
  have first := firstRound_correspondence e1 e2 e3
  have k4 : (Operand.reg 11 : Operand 64).read s4 = 0xffffffff00000001 :=
    (e4.agrees.read (by simp [secondRoundEffect, Effect.components])).trans first.2.2.2.2
  have k5 : (Operand.reg 11 : Operand 64).read s5 = 0xffffffff00000001 :=
    (e5.agrees.read (by simp [thirdRoundEffect, Effect.components])).trans k4
  have k6 : (Operand.reg 11 : Operand 64).read s6 = 0xffffffff00000001 :=
    (e6.agrees.read (by simp [fourthRoundEffect, Effect.components])).trans k5
  have n4 : (Operand.reg 3 : Operand 64).read s4 = 0xffffffff :=
    (e4.agrees.read (by simp [secondRoundEffect, Effect.components])).trans first.2.2.2.1
  have n5 : (Operand.reg 3 : Operand 64).read s5 = 0xffffffff :=
    (e5.agrees.read (by simp [thirdRoundEffect, Effect.components])).trans n4
  have n6 : (Operand.reg 3 : Operand 64).read s6 = 0xffffffff :=
    (e6.agrees.read (by simp [fourthRoundEffect, Effect.components])).trans n5
  have tail := tail_correspondence e7 e8 e9 e10 e11 k6 n6 (fourthRound_carryByte e6)
  rw [rawTail_eq_reduceSum] at tail
  change outputLimbs t = reduceSum (normalize (pendingRounds s6).1 (pendingRounds s6).2).1
    (normalize (pendingRounds s6).1 (pendingRounds s6).2).2 at tail
  rw [rounds_correspondence e1 e2 e3 e4 e5 e6] at tail
  rw [tail]
  exact reduce_normalizedRounds _ _ bound

end P256.Proofs.Field.Montgomery.Reduction
