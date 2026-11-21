import P256.Proofs.Field.Montgomery.Reduction.Setup
import P256.Proofs.Field.Montgomery.Reduction.FirstCarry
import P256.Proofs.Field.Montgomery.Reduction.FirstHigh
import P256.Proofs.Field.Montgomery.Reduction.Arithmetic
import P256.Proofs.Field.Representation

set_option autoImplicit false

namespace P256.Proofs.Field.Montgomery.Reduction

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.SecretKeyFromBytes.Scalar (Limbs)

theorem setb_zero (c : Bool) :
    mergeGPR 8 (if c then 1 else 0) (0 : BitVec 64) = BitVec.ofNat 64 c.toNat := by
  cases c <;> rfl

theorem firstRound_correspondence {s t u v : RamState}
    (hs : (firstSetupEffect s).Holds s t)
    (hc : (firstCarryEffect t).Holds t u)
    (hh : (firstHighEffect u).Holds u v) :
    (⟨(Operand.reg 8 : Operand 64).read v, (Operand.reg 14 : Operand 64).read v,
      (Operand.reg 10 : Operand 64).read v, (Operand.reg 9 : Operand 64).read v⟩ : Limbs) =
      firstRound (readLimbs s ((Operand.reg 6 : Operand 64).read s)) ∧
    (Operand.reg 1 : Operand 64).read v = (Operand.reg 2 : Operand 64).read s ∧
    (Operand.reg 12 : Operand 64).read v =
      (Operand.mem ((Operand.reg 2 : Operand 64).read s + 8) : Operand 64).read s ∧
    (Operand.reg 3 : Operand 64).read v = 0xffffffff ∧
    (Operand.reg 11 : Operand 64).read v = 0xffffffff00000001 := by
  have m1 : t.external = s.external := (hs.agrees.external (by simp [firstSetupEffect, Effect.components, Component.Covers]))
  have mem1 (a : BitVec 64) : (Operand.mem a : Operand 64).read t = (Operand.mem a : Operand 64).read s := by
    change memLoad _ _ _ = memLoad _ _ _
    rw [m1]
  have hw1 := hs.writes
  dsimp only [firstSetupEffect, Write.AllHold] at hw1
  rcases hw1 with ⟨g1r1, g1r9, g1r3, g1r0, g1r2, g1r8, g1r14⟩
  have g1r4 : ((Operand.reg 4 : Operand 64).read t) = ((Operand.reg 4 : Operand 64).read s) := hs.agrees.read (by simp [firstSetupEffect, Effect.components])
  have g1r5 : ((Operand.reg 5 : Operand 64).read t) = ((Operand.reg 5 : Operand 64).read s) := hs.agrees.read (by simp [firstSetupEffect, Effect.components])
  have g1r6 : ((Operand.reg 6 : Operand 64).read t) = ((Operand.reg 6 : Operand 64).read s) := hs.agrees.read (by simp [firstSetupEffect, Effect.components])
  have g1r7 : ((Operand.reg 7 : Operand 64).read t) = ((Operand.reg 7 : Operand 64).read s) := hs.agrees.read (by simp [firstSetupEffect, Effect.components])
  have g1r10 : ((Operand.reg 10 : Operand 64).read t) = ((Operand.reg 10 : Operand 64).read s) := hs.agrees.read (by simp [firstSetupEffect, Effect.components])
  have g1r11 : ((Operand.reg 11 : Operand 64).read t) = ((Operand.reg 11 : Operand 64).read s) := hs.agrees.read (by simp [firstSetupEffect, Effect.components])
  have g1r12 : ((Operand.reg 12 : Operand 64).read t) = ((Operand.reg 12 : Operand 64).read s) := hs.agrees.read (by simp [firstSetupEffect, Effect.components])
  have g1r13 : ((Operand.reg 13 : Operand 64).read t) = ((Operand.reg 13 : Operand 64).read s) := hs.agrees.read (by simp [firstSetupEffect, Effect.components])
  have g1r15 : ((Operand.reg 15 : Operand 64).read t) = ((Operand.reg 15 : Operand 64).read s) := hs.agrees.read (by simp [firstSetupEffect, Effect.components])
  have m2 : u.external = s.external := (hc.agrees.external (by simp [firstCarryEffect, Effect.components, Component.Covers])).trans m1
  have mem2 (a : BitVec 64) : (Operand.mem a : Operand 64).read u = (Operand.mem a : Operand 64).read s := by
    change memLoad _ _ _ = memLoad _ _ _
    rw [m2]
  have hw2 := hc.writes
  dsimp only [firstCarryEffect, Write.AllHold] at hw2
  simp only [g1r2, g1r6, g1r8, g1r9, g1r14, mem1] at hw2
  rcases hw2 with ⟨g2r0, g2r8, g2r14⟩
  have g2r1 : ((Operand.reg 1 : Operand 64).read u) = ((Operand.reg 1 : Operand 64).read t) := hc.agrees.read (by simp [firstCarryEffect, Effect.components])
  rw [g1r1] at g2r1
  have g2r2 : ((Operand.reg 2 : Operand 64).read u) = ((Operand.reg 2 : Operand 64).read t) := hc.agrees.read (by simp [firstCarryEffect, Effect.components])
  rw [g1r2] at g2r2
  have g2r3 : ((Operand.reg 3 : Operand 64).read u) = ((Operand.reg 3 : Operand 64).read t) := hc.agrees.read (by simp [firstCarryEffect, Effect.components])
  rw [g1r3] at g2r3
  have g2r4 : ((Operand.reg 4 : Operand 64).read u) = ((Operand.reg 4 : Operand 64).read t) := hc.agrees.read (by simp [firstCarryEffect, Effect.components])
  rw [g1r4] at g2r4
  have g2r5 : ((Operand.reg 5 : Operand 64).read u) = ((Operand.reg 5 : Operand 64).read t) := hc.agrees.read (by simp [firstCarryEffect, Effect.components])
  rw [g1r5] at g2r5
  have g2r6 : ((Operand.reg 6 : Operand 64).read u) = ((Operand.reg 6 : Operand 64).read t) := hc.agrees.read (by simp [firstCarryEffect, Effect.components])
  rw [g1r6] at g2r6
  have g2r7 : ((Operand.reg 7 : Operand 64).read u) = ((Operand.reg 7 : Operand 64).read t) := hc.agrees.read (by simp [firstCarryEffect, Effect.components])
  rw [g1r7] at g2r7
  have g2r9 : ((Operand.reg 9 : Operand 64).read u) = ((Operand.reg 9 : Operand 64).read t) := hc.agrees.read (by simp [firstCarryEffect, Effect.components])
  rw [g1r9] at g2r9
  have g2r10 : ((Operand.reg 10 : Operand 64).read u) = ((Operand.reg 10 : Operand 64).read t) := hc.agrees.read (by simp [firstCarryEffect, Effect.components])
  rw [g1r10] at g2r10
  have g2r11 : ((Operand.reg 11 : Operand 64).read u) = ((Operand.reg 11 : Operand 64).read t) := hc.agrees.read (by simp [firstCarryEffect, Effect.components])
  rw [g1r11] at g2r11
  have g2r12 : ((Operand.reg 12 : Operand 64).read u) = ((Operand.reg 12 : Operand 64).read t) := hc.agrees.read (by simp [firstCarryEffect, Effect.components])
  rw [g1r12] at g2r12
  have g2r13 : ((Operand.reg 13 : Operand 64).read u) = ((Operand.reg 13 : Operand 64).read t) := hc.agrees.read (by simp [firstCarryEffect, Effect.components])
  rw [g1r13] at g2r13
  have g2r15 : ((Operand.reg 15 : Operand 64).read u) = ((Operand.reg 15 : Operand 64).read t) := hc.agrees.read (by simp [firstCarryEffect, Effect.components])
  rw [g1r15] at g2r15
  have m3 : v.external = s.external := (hh.agrees.external (by simp [firstHighEffect, Effect.components, Component.Covers])).trans m2
  have mem3 (a : BitVec 64) : (Operand.mem a : Operand 64).read v = (Operand.mem a : Operand 64).read s := by
    change memLoad _ _ _ = memLoad _ _ _
    rw [m3]
  have hw3 := hh.writes
  dsimp only [firstHighEffect, Write.AllHold] at hw3
  simp only [g2r1, g2r6, g2r9, g2r14, mem2] at hw3
  rcases hw3 with ⟨g3r0, g3r2, g3r9, g3r10, g3r11, g3r12, g3r14⟩
  have g3r1 : ((Operand.reg 1 : Operand 64).read v) = ((Operand.reg 1 : Operand 64).read u) := hh.agrees.read (by simp [firstHighEffect, Effect.components])
  rw [g2r1] at g3r1
  have g3r3 : ((Operand.reg 3 : Operand 64).read v) = ((Operand.reg 3 : Operand 64).read u) := hh.agrees.read (by simp [firstHighEffect, Effect.components])
  rw [g2r3] at g3r3
  have g3r4 : ((Operand.reg 4 : Operand 64).read v) = ((Operand.reg 4 : Operand 64).read u) := hh.agrees.read (by simp [firstHighEffect, Effect.components])
  rw [g2r4] at g3r4
  have g3r5 : ((Operand.reg 5 : Operand 64).read v) = ((Operand.reg 5 : Operand 64).read u) := hh.agrees.read (by simp [firstHighEffect, Effect.components])
  rw [g2r5] at g3r5
  have g3r6 : ((Operand.reg 6 : Operand 64).read v) = ((Operand.reg 6 : Operand 64).read u) := hh.agrees.read (by simp [firstHighEffect, Effect.components])
  rw [g2r6] at g3r6
  have g3r7 : ((Operand.reg 7 : Operand 64).read v) = ((Operand.reg 7 : Operand 64).read u) := hh.agrees.read (by simp [firstHighEffect, Effect.components])
  rw [g2r7] at g3r7
  have g3r8 : ((Operand.reg 8 : Operand 64).read v) = ((Operand.reg 8 : Operand 64).read u) := hh.agrees.read (by simp [firstHighEffect, Effect.components])
  rw [g2r8] at g3r8
  have g3r13 : ((Operand.reg 13 : Operand 64).read v) = ((Operand.reg 13 : Operand 64).read u) := hh.agrees.read (by simp [firstHighEffect, Effect.components])
  rw [g2r13] at g3r13
  have g3r15 : ((Operand.reg 15 : Operand 64).read v) = ((Operand.reg 15 : Operand 64).read u) := hh.agrees.read (by simp [firstHighEffect, Effect.components])
  rw [g2r15] at g3r15
  simp only [g3r8, g3r14, g3r10, g3r9, g3r1, g3r12, g3r3, g3r11, and_self, firstRound, readLimbs, add64, adc64, product64, setb_zero]
  exact ⟨rfl, trivial⟩


end P256.Proofs.Field.Montgomery.Reduction
