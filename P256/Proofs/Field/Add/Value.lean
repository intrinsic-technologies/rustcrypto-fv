import P256.Proofs.Field.Add.Body
import P256.Proofs.Common.Instructions.ByteOps.Effects

set_option autoImplicit false

namespace P256.Proofs.Field.Add

open P256.Proofs.SecretKeyFromBytes.Scalar (Limbs)
open P256.Proofs.Field.Montgomery.Reduction
open X86 X86.Machine X86.UserProcess X86Proofs

def outputLimbs (s : RamState) : Limbs :=
  ⟨s.regValue .r9, s.regValue .r10, s.regValue .rbx, s.regValue .rsi⟩

theorem body_value {s t : RamState} (trace : BodyTrace s t) :
    outputLimbs t = add (readLimbs s (s.regValue .rsi)) (readLimbs s (s.regValue .rdx)) := by
  obtain ⟨s1, s2, s3, s4, e1, e2, e3, e4, e5⟩ := trace
  let raw := addRaw (readLimbs s (s.regValue .rdx)) (readLimbs s (s.regValue .rsi))
  let a := raw.1
  let carryIn := raw.2
  have l0sum : (Operand.reg 1 : Operand 64).read s1 = a.l0 := e1.writes.1
  have l1sum : (Operand.reg 8 : Operand 64).read s1 = a.l1 := e1.writes.2.1
  have l2sum : (Operand.reg 11 : Operand 64).read s1 = a.l2 := e1.writes.2.2.1
  have l3sum : (Operand.reg 9 : Operand 64).read s1 = a.l3 := e1.writes.2.2.2
  have carrySum : (StatusFlags.ofRFLAGS s1.RFLAGS).CF = carryIn := e1.flags.1
  have r0 : (Operand.reg 0 : Operand 64).read s2 = a.l0 + 1 := by
    have hw : (Operand.reg 0 : Operand 64).read s2 = (Operand.reg 1 : Operand 64).read s1 + 1 := e2.writes.1
    exact hw.trans (congrArg (· + 1) l0sum)
  have mask0 : (Operand.reg 1 : Operand 64).read s2 =
      (-((~~~a.l0 ||| (a.l0+1)) >>> 63)).sshiftRight 63 := by
    have hw := e2.writes.2.1
    change (Operand.reg 1 : Operand 64).read s2 =
      (-((~~~(Operand.reg 1 : Operand 64).read s1 ||| ((Operand.reg 1 : Operand 64).read s1 + 1)) >>> 63)).sshiftRight 63 at hw
    simpa only [l0sum] using hw
  have zero10 : (Operand.reg 10 : Operand 64).read s2 = 0 := e2.writes.2.2.2.1
  have savedCarry : (Operand.reg 6 : Operand 8).read s2 = if carryIn then 1 else 0 := by
    have hw := e2.writes.2.2.1
    change (Operand.reg 6 : Operand 64).read s2 =
      mergeGPR 8 (if (StatusFlags.ofRFLAGS s1.RFLAGS).CF then 1#8 else 0#8)
        ((Operand.reg 6 : Operand 64).read s1) at hw
    change ((Operand.reg 6 : Operand 64).read s2).setWidth 8 = _
    rw [hw, P256.Proofs.Common.Instructions.ByteOps.ByteOps.mergeGPR_low8, carrySum]
    cases carryIn <;> rfl
  have l1 : (Operand.reg 8 : Operand 64).read s2 = a.l1 :=
    (e2.agrees.read (n := 64) (r := 8) (by simp [lowEffect, Effect.components])).trans l1sum
  have l2 : (Operand.reg 11 : Operand 64).read s2 = a.l2 :=
    (e2.agrees.read (n := 64) (r := 11) (by simp [lowEffect, Effect.components])).trans l2sum
  have l3 : (Operand.reg 9 : Operand 64).read s3 = a.l3 :=
    (e3.agrees.read (n := 64) (r := 9) (by simp [middleEffect, Effect.components])).trans
      ((e2.agrees.read (n := 64) (r := 9) (by simp [lowEffect, Effect.components])).trans l3sum)
  have zero10' : (Operand.reg 10 : Operand 64).read s3 = 0 :=
    (e3.agrees.read (n := 64) (r := 10) (by simp [middleEffect, Effect.components])).trans zero10
  have savedCarry' : (Operand.reg 6 : Operand 8).read s3 = if carryIn then 1 else 0 :=
    (e3.agrees.read (n := 8) (r := 6) (by simp [middleEffect, Effect.components])).trans savedCarry
  have corrInput : correctionInput s4 = (subtractModulus a).1 := by
    have h0 := (e4.agrees.read (n := 64) (r := 0) (by simp [upperEffect, Effect.components])).trans
      ((e3.agrees.read (n := 64) (r := 0) (by simp [middleEffect, Effect.components])).trans r0)
    have h1 := (e4.agrees.read (n := 64) (r := 2) (by simp [upperEffect, Effect.components])).trans e3.writes.1
    have h2 := (e4.agrees.read (n := 64) (r := 8) (by simp [upperEffect, Effect.components])).trans e3.writes.2.2.1
    have h3 := e4.writes.2.1
    have hm := e3.writes.2.2.2.1
    simp only [hm, l3] at h3
    simp only [l1, l2, mask0] at h1 h2 h3
    unfold correctionInput subtractModulus
    rw [h0, h1, h2, h3]
  have corrChoice : (Operand.reg 6 : Operand 64).read s4 =
      ((-(subtractModulus a).2).sshiftRight 63 + BitVec.ofNat 64 carryIn.toNat) >>> 63 := by
    have hw := e4.writes.2.2.2.2.1
    have hm := e3.writes.2.2.2.1
    simp only [l1, l2, mask0] at hm
    simp only [hm, l3, zero10', savedCarry'] at hw
    rw [hw]
    unfold subtractModulus
    cases carryIn <;> rfl
  have value : correctionValue s4 = reduceSum a carryIn := by
    rw [reduceSum_eq_correct]
    unfold correctionValue
    rw [corrInput, corrChoice]
  have out : outputLimbs t = correctionValue s4 := by
    have hw := e5.writes
    change _ ∧ _ ∧ _ ∧ _ ∧ _ at hw
    change (⟨(Operand.reg 9 : Operand 64).read t, (Operand.reg 10 : Operand 64).read t,
      (Operand.reg 3 : Operand 64).read t, (Operand.reg 6 : Operand 64).read t⟩ : Limbs) = _
    rw [hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1]
  rw [out, value]
  change reduceSum raw.1 raw.2 = _
  simp only [raw, add, addRaw_comm]

end P256.Proofs.Field.Add
