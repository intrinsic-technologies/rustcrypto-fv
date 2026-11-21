import P256.Proofs.Common.Field.Montgomery.Schoolbook.CarryCompose
import P256.Proofs.Program.Code

set_option autoImplicit false

open P256.Proofs.Common.Instructions.Carry (adcR64R64Effect adcR64R64Effect_components adcSpec adc_r64_r64_effect_step)
open P256.Proofs.Common.Instructions.Setb (SupportedOpcode setccR8Effect setccR8Effect_components setcc_r8_rex_effect_step)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Field.Montgomery.Reduction

open P256.Spec.Program.Routines
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

attribute [local simp] adcR64R64Effect_components setccR8Effect_components

structure FirstCarryPre (s : RamState) : Prop where
  rip : s.RIP = 0x113c32
  readable : MemReadable s ((Operand.reg 6 : Operand 64).read s + 8) 8

def firstCarryBytes : List UInt8 :=
  [0x48, 0x8b, 0x46, 0x08, 0x4c, 0x01, 0xc8, 0x41, 0x0f, 0x92, 0xc6,
   0x49, 0x01, 0xc0, 0x49, 0x11, 0xd6]

def firstCarryEffect (s : RamState) : Effect :=
  let x := addSpec ((Operand.mem ((Operand.reg 6 : Operand 64).read s + 8) : Operand 64).read s)
    ((Operand.reg 9 : Operand 64).read s)
  let y := addSpec ((Operand.reg 8 : Operand 64).read s) x.1
  let z := adcSpec (mergeGPR 8 (if x.2.CF then 1 else 0) ((Operand.reg 14 : Operand 64).read s))
    ((Operand.reg 2 : Operand 64).read s) (BitVec.ofBool y.2.CF)
  { rip := 0x113c43
    writes := [⟨(.reg 0 : Operand 64), x.1⟩, ⟨(.reg 8 : Operand 64), y.1⟩,
      ⟨(.reg 14 : Operand 64), z.1⟩]
    flags := some (.ofStatusFlags z.2) }

theorem first_carry [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary FirstCarryPre (codeRange 0x113c32 firstCarryBytes)
      (Effect.post firstCarryEffect) := by
  intro s ready loaded pre
  have next (offset : Nat) (h : offset < 118431) :=
    boundary_ne_program hout (inProgram_of_textOffset offset h)
  have code (offset len : Nat) := loaded.mono (codeRange_slice_subset 0x113c32 firstCarryBytes offset len)
  let x := addSpec ((Operand.mem ((Operand.reg 6 : Operand 64).read s + 8) : Operand 64).read s)
    ((Operand.reg 9 : Operand 64).read s)
  let y := addSpec ((Operand.reg 8 : Operand 64).read s) x.1
  let z := adcSpec (mergeGPR 8 (if x.2.CF then 1 else 0) ((Operand.reg 14 : Operand 64).read s))
    ((Operand.reg 2 : Operand 64).read s) (BitVec.ofBool y.2.CF)
  obtain ⟨s1, a1, r1, e1⟩ :=
    (mov_r64_m64_effect_step 0x113c32 0x48 (by simp [RexWPrefix]) 0 (.base 6 (.d8 8))
      (by decide) rfl rfl).advances ready (code 0 4) ⟨pre.rip, pre.readable⟩ (next 0x13c36 (by decide))
  change (movR64M64Effect 0x113c32 0 (.base 6 (.d8 8)) s).Holds s s1 at e1
  have m1 : s1.external = s.external := e1.agrees.external (by simp [Component.Covers])
  have v1 : (Operand.reg 0 : Operand 64).read s1 =
      (Operand.mem ((Operand.reg 6 : Operand 64).read s + 8) : Operand 64).read s := e1.writes
  obtain ⟨s2, a2, r2, e2⟩ :=
    (add_r64_r64_effect_step 0x113c36 0x4c 0xc8 (by simp [RexWPrefix]) (by decide)).advances
      r1 ((code 4 3).of_external_eq m1) e1.rip (next 0x13c39 (by decide))
  change (addR64R64Effect 0x113c36 0 9 s1).Holds s1 s2 at e2
  have m2 : s2.external = s.external := (e2.agrees.external (by simp [Component.Covers])).trans m1
  have r9 : (Operand.reg 9 : Operand 64).read s1 = (Operand.reg 9 : Operand 64).read s :=
    e1.agrees.read (by simp)
  have v2 : (Operand.reg 0 : Operand 64).read s2 = x.1 := by
    have h : (Operand.reg 0 : Operand 64).read s2 =
      (addSpec ((Operand.reg 0 : Operand 64).read s1) ((Operand.reg 9 : Operand 64).read s1)).1 := e2.writes
    rw [v1, r9] at h
    exact h
  have c2 : (StatusFlags.ofRFLAGS s2.RFLAGS).CF = x.2.CF := by
    have h := e2.flags.1
    change (StatusFlags.ofRFLAGS s2.RFLAGS).CF =
      (addSpec ((Operand.reg 0 : Operand 64).read s1) ((Operand.reg 9 : Operand 64).read s1)).2.CF at h
    rw [v1, r9] at h
    exact h
  obtain ⟨s3, a3, r3, e3⟩ :=
    (setcc_r8_rex_effect_step 0x113c39 0x41 0x92 0xc6 (by simp [RexPrefix]) (by simp [SupportedOpcode]) (by decide)).advances
      r2 ((code 7 4).of_external_eq m2) e2.rip (next 0x13c3d (by decide))
  change (setccR8Effect 0x113c39 4 14 2 s2).Holds s2 s3 at e3
  have m3 : s3.external = s.external := (e3.agrees.external (by simp [Component.Covers])).trans m2
  have r14 : (Operand.reg 14 : Operand 64).read s2 = (Operand.reg 14 : Operand 64).read s :=
    (e2.agrees.read (by simp)).trans (e1.agrees.read (by simp))
  have v3 : (Operand.reg 14 : Operand 64).read s3 =
      mergeGPR 8 (if x.2.CF then 1 else 0) ((Operand.reg 14 : Operand 64).read s) := by
    have h := e3.writes
    change (Operand.reg 14 : Operand 64).read s3 =
      mergeGPR 8 (if (StatusFlags.ofRFLAGS s2.RFLAGS).CF then 1 else 0) ((Operand.reg 14 : Operand 64).read s2) at h
    rw [c2, r14] at h
    exact h
  obtain ⟨s4, a4, r4, e4⟩ :=
    (add_r64_r64_effect_step 0x113c3d 0x49 0xc0 (by simp [RexWPrefix]) (by decide)).advances
      r3 ((code 11 3).of_external_eq m3) e3.rip (next 0x13c40 (by decide))
  change (addR64R64Effect 0x113c3d 8 0 s3).Holds s3 s4 at e4
  have m4 : s4.external = s.external := (e4.agrees.external (by simp [Component.Covers])).trans m3
  have r8 : (Operand.reg 8 : Operand 64).read s3 = (Operand.reg 8 : Operand 64).read s :=
    (e3.agrees.read (by simp)).trans ((e2.agrees.read (by simp)).trans (e1.agrees.read (by simp)))
  have r0 : (Operand.reg 0 : Operand 64).read s3 = x.1 :=
    (e3.agrees.read (by simp)).trans v2
  have v4 : (Operand.reg 8 : Operand 64).read s4 = y.1 := by
    have h : (Operand.reg 8 : Operand 64).read s4 =
      (addSpec ((Operand.reg 8 : Operand 64).read s3) ((Operand.reg 0 : Operand 64).read s3)).1 := e4.writes
    rw [r8, r0] at h
    exact h
  have c4 : (StatusFlags.ofRFLAGS s4.RFLAGS).CF = y.2.CF := by
    have h := e4.flags.1
    change (StatusFlags.ofRFLAGS s4.RFLAGS).CF =
      (addSpec ((Operand.reg 8 : Operand 64).read s3) ((Operand.reg 0 : Operand 64).read s3)).2.CF at h
    rw [r8, r0] at h
    exact h
  obtain ⟨s5, a5, r5, e5⟩ :=
    (adc_r64_r64_effect_step 0x113c40 0x49 0xd6 (by simp [RexWPrefix]) (by decide)).advances
      r4 ((code 14 3).of_external_eq m4) e4.rip (next 0x13c43 (by decide))
  change (adcR64R64Effect 0x113c40 14 2 s4).Holds s4 s5 at e5
  have m5 : s5.external = s.external := (e5.agrees.external (by simp [Component.Covers])).trans m4
  have r14' : (Operand.reg 14 : Operand 64).read s4 =
      mergeGPR 8 (if x.2.CF then 1 else 0) ((Operand.reg 14 : Operand 64).read s) :=
    (e4.agrees.read (by simp)).trans v3
  have r2' : (Operand.reg 2 : Operand 64).read s4 = (Operand.reg 2 : Operand 64).read s :=
    (e4.agrees.read (by simp)).trans ((e3.agrees.read (by simp)).trans
      ((e2.agrees.read (by simp)).trans (e1.agrees.read (by simp))))
  have vz : adcSpec ((Operand.reg 14 : Operand 64).read s4)
      ((Operand.reg 2 : Operand 64).read s4) (s4.RFLAGS.extractLsb' 0 1) = z := by
    rw [r14', r2', P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, c4]
  refine ⟨5, s5, (((a1.trans a2).trans a3).trans a4).trans a5, r5,
    loaded.of_external_eq m5, e5.rip, ?_, ?_, ?_⟩
  · change _ ∧ _ ∧ _
    refine ⟨?_, ?_, ?_⟩
    · exact (e5.agrees.read (by simp)).trans ((e4.agrees.read (by simp)).trans r0)
    · exact (e5.agrees.read (by simp)).trans v4
    · have h := e5.writes
      change (Operand.reg 14 : Operand 64).read s5 = _ at h
      rw [vz] at h
      exact h
  · have h := e5.flags
    change (StatusFlagsOutcome.ofStatusFlags (adcSpec _ _ _).2).Allows _ at h
    rw [vz] at h
    exact h
  · apply ((((e1.agrees.trans e2.agrees).trans e3.agrees).trans e4.agrees).trans e5.agrees).mono
    simp only [movR64M64Effect_components, addR64R64Effect_components,
      setccR8Effect_components, adcR64R64Effect_components]
    simp [firstCarryEffect, Effect.components]

theorem firstCarry_bytes :
    Extracted.textBytes.toListFrom 0x13c32 firstCarryBytes.length = firstCarryBytes := by
  decide +kernel

end P256.Proofs.Field.Montgomery.Reduction
