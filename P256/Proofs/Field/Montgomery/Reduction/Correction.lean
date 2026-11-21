import P256.Proofs.Common.Field.Montgomery.Schoolbook.CarryCompose
import P256.Proofs.Common.Instructions.ShiftLeft.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import P256.Proofs.Program.Code
import P256.Proofs.Common.Instructions.MovzxByte
import P256.Proofs.Common.Instructions.Neg64

set_option autoImplicit false

open P256.Proofs.Common.Instructions (addR64M64Effect_components mulR64Effect_components)
open P256.Proofs.Common.Instructions.AddByte (addR8Imm8Effect)
open P256.Proofs.Common.Instructions.Carry (adcR64Imm8Effect adcR64Imm8Effect_components adcR64M64Effect_components adcR64R64Effect adcR64R64Effect_components adcSpec adc_r64_imm8_effect_step adc_r64_r64_effect_step)
open P256.Proofs.Common.Instructions.MovzxByte (movzxR32R8Effect)
open P256.Proofs.Common.Instructions.Neg64 (negR64Effect neg_r64_effect_step)
open P256.Proofs.Common.Instructions.Setb (SupportedOpcode setccR8Effect setccR8Effect_components setcc_r8_effect_step)
open P256.Proofs.Common.Instructions.ShiftLeft (shlR64Effect_components)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Field.Montgomery.Reduction

open P256.Spec.Program.Routines
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

attribute [local simp] movzxR32R8Effect addR8Imm8Effect negR64Effect

attribute [local simp] mulR64Effect_components adcR64R64Effect_components adcR64Imm8Effect_components
  adcR64M64Effect_components addR64M64Effect_components setccR8Effect_components shlR64Effect_components

structure CorrectionPre (s : RamState) : Prop where
  rip : s.RIP = 0x113dc6

def correctionBytes : List UInt8 :=
  [0x48, 0x89, 0xc2, 0x48, 0x29, 0xca, 0x48, 0xf7, 0xd9, 0x41, 0x89, 0xc9, 0x31, 0xdb, 0x4d, 0x1, 0xc1, 0xf, 0x92, 0xc3, 0x4c, 0x21, 0xd9, 0x48, 0x39, 0xc2, 0x49, 0x83, 0xd1, 0x0, 0x4c, 0x11, 0xd3, 0x48, 0x11, 0xf1]

def correctionEffect (s : RamState) : Effect :=
  let q2 := subSpec ((Operand.reg 0 : Operand 64).read s) ((Operand.reg 1 : Operand 64).read s)
  let v3 := -((Operand.reg 1 : Operand 64).read s)
  let v4 := (v3.setWidth 32).setWidth 64
  let q6 := addSpec v4 ((Operand.reg 8 : Operand 64).read s)
  let v7 := mergeGPR 8 (if q6.2.CF then 1 else 0) (0 : BitVec 64)
  let v8 := v3 &&& ((Operand.reg 11 : Operand 64).read s)
  let q9 := cmpSpec q2.1 ((Operand.reg 0 : Operand 64).read s)
  let q10 := adcSpec q6.1 0 (BitVec.ofBool q9.CF)
  let q11 := adcSpec v7 ((Operand.reg 10 : Operand 64).read s) (BitVec.ofBool q10.2.CF)
  let q12 := adcSpec v8 ((Operand.reg 6 : Operand 64).read s) (BitVec.ofBool q11.2.CF)
  { rip := 0x113dea
    writes := [⟨(.reg 1 : Operand 64), q12.1⟩,
      ⟨(.reg 2 : Operand 64), q2.1⟩,
      ⟨(.reg 3 : Operand 64), q11.1⟩,
      ⟨(.reg 9 : Operand 64), q10.1⟩]
    flags := some (.ofStatusFlags q12.2) }

theorem correction_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary CorrectionPre (codeRange 0x113dc6 correctionBytes)
      (Effect.post correctionEffect) := by
  intro s ready loaded pre
  have next (offset : Nat) (h : offset < 118431) :=
    boundary_ne_program hout (inProgram_of_textOffset offset h)
  have code (offset len : Nat) := loaded.mono (codeRange_slice_subset 0x113dc6 correctionBytes offset len)
  let q2 := subSpec ((Operand.reg 0 : Operand 64).read s) ((Operand.reg 1 : Operand 64).read s)
  let v3 := -((Operand.reg 1 : Operand 64).read s)
  let v4 := (v3.setWidth 32).setWidth 64
  let q6 := addSpec v4 ((Operand.reg 8 : Operand 64).read s)
  let v7 := mergeGPR 8 (if q6.2.CF then 1 else 0) (0 : BitVec 64)
  let v8 := v3 &&& ((Operand.reg 11 : Operand 64).read s)
  let q9 := cmpSpec q2.1 ((Operand.reg 0 : Operand 64).read s)
  let q10 := adcSpec q6.1 0 (BitVec.ofBool q9.CF)
  let q11 := adcSpec v7 ((Operand.reg 10 : Operand 64).read s) (BitVec.ofBool q10.2.CF)
  let q12 := adcSpec v8 ((Operand.reg 6 : Operand 64).read s) (BitVec.ofBool q11.2.CF)
  obtain ⟨s1, a1, ready1, e1⟩ :=
    (mov_r64_r64_effect_step 0x113dc6 0x48 0xc2 (by simp [RexWPrefix]) (by decide)).advances ready (code 0 3)
      pre.rip (next 0x13dc9 (by decide))
  change (movR64R64Effect 0x113dc6 2 0 s).Holds s s1 at e1
  have m1 : s1.external = s.external := (e1.agrees.external (by simp [Component.Covers] <;> simp [Effect.components]))
  have v1r2 : ((Operand.reg 2 : Operand 64).read s1) = ((Operand.reg 0 : Operand 64).read s) := by
    have h : ((Operand.reg 2 : Operand 64).read s1) = ((Operand.reg 0 : Operand 64).read s) := e1.writes
    exact h
  have r1b1 : ((Operand.reg 1 : Operand 64).read s1) = ((Operand.reg 1 : Operand 64).read s) := (e1.agrees.read (by simp <;> simp [Effect.components])).trans (rfl)
  have r1b2 : ((Operand.reg 2 : Operand 64).read s1) = ((Operand.reg 0 : Operand 64).read s) := v1r2
  obtain ⟨s2, a2, ready2, e2⟩ :=
    (sub_r64_r64_effect_step 0x113dc9 0x48 0xca (by simp [RexWPrefix]) (by decide)).advances ready1 ((code 3 3).of_external_eq m1)
      e1.rip (next 0x13dcc (by decide))
  change (subR64R64Effect 0x113dc9 2 1 s1).Holds s1 s2 at e2
  have m2 : s2.external = s.external := (e2.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])).trans m1
  have v2r2 : ((Operand.reg 2 : Operand 64).read s2) = q2.1 := by
    have h : ((Operand.reg 2 : Operand 64).read s2) = (subSpec ((Operand.reg 2 : Operand 64).read s1) ((Operand.reg 1 : Operand 64).read s1) ).1 := e2.writes
    rw [r1b1, r1b2] at h
    exact h
  have c2 : (StatusFlags.ofRFLAGS s2.RFLAGS).CF = q2.2.CF := by
    have h : (StatusFlags.ofRFLAGS s2.RFLAGS).CF = (subSpec ((Operand.reg 2 : Operand 64).read s1) ((Operand.reg 1 : Operand 64).read s1) ).2.CF := e2.flags.1
    rw [r1b1, r1b2] at h
    exact h
  have r2b1 : ((Operand.reg 1 : Operand 64).read s2) = ((Operand.reg 1 : Operand 64).read s) := (e2.agrees.read (by simp <;> simp [Effect.components])).trans ((e1.agrees.read (by simp <;> simp [Effect.components])).trans (rfl))
  obtain ⟨s3, a3, ready3, e3⟩ :=
    (neg_r64_effect_step 0x113dcc 0x48 0xd9 (by simp [RexWPrefix]) (by decide) (by decide)).advances ready2 ((code 6 3).of_external_eq m2)
      e2.rip (next 0x13dcf (by decide))
  change (negR64Effect 0x113dcc 1 s2).Holds s2 s3 at e3
  have m3 : s3.external = s.external := (e3.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])).trans m2
  have v3r1 : ((Operand.reg 1 : Operand 64).read s3) = v3 := by
    have h : ((Operand.reg 1 : Operand 64).read s3) = -((Operand.reg 1 : Operand 64).read s2) := e3.writes
    rw [r2b1] at h
    exact h
  have r3b1 : ((Operand.reg 1 : Operand 64).read s3) = v3 := v3r1
  obtain ⟨s4, a4, ready4, e4⟩ :=
    (mov_r32_r32_rex_effect_step 0x113dcf 0x41 0xc9 (by simp [RexNoWPrefix]) (by decide)).advances ready3 ((code 9 3).of_external_eq m3)
      e3.rip (next 0x13dd2 (by decide))
  change (movR32R32Effect 0x113dcf 3 9 1 s3).Holds s3 s4 at e4
  have m4 : s4.external = s.external := (e4.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])).trans m3
  have v4r9 : ((Operand.reg 9 : Operand 64).read s4) = v4 := by
    have h : ((Operand.reg 9 : Operand 64).read s4) = (((Operand.reg 1 : Operand 64).read s3).setWidth 32).setWidth 64 := e4.writes
    rw [r3b1] at h
    exact h
  have r4b3 : ((Operand.reg 3 : Operand 64).read s4) = ((Operand.reg 3 : Operand 64).read s) := (e4.agrees.read (by simp <;> simp [Effect.components])).trans ((e3.agrees.read (by simp <;> simp [Effect.components])).trans ((e2.agrees.read (by simp <;> simp [Effect.components])).trans ((e1.agrees.read (by simp <;> simp [Effect.components])).trans (rfl))))
  obtain ⟨s5, a5, ready5, e5⟩ :=
    (xor_r32_r32_effect_step 0x113dd2 0xdb (by decide)).advances ready4 ((code 12 2).of_external_eq m4)
      e4.rip (next 0x13dd4 (by decide))
  change (xorR32R32Effect 0x113dd2 2 3 3 s4).Holds s4 s5 at e5
  have m5 : s5.external = s.external := (e5.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])).trans m4
  have v5r3 : ((Operand.reg 3 : Operand 64).read s5) = (0 : BitVec 64) := by
    have h : ((Operand.reg 3 : Operand 64).read s5) = 0 := (by simpa only [xorR32R32Effect, BitVec.xor_self, BitVec.setWidth_zero, BitVec.ofNat_eq_ofNat, Write.AllHold] using e5.writes)
    exact h
  have r5b8 : ((Operand.reg 8 : Operand 64).read s5) = ((Operand.reg 8 : Operand 64).read s) := (e5.agrees.read (by simp <;> simp [Effect.components])).trans ((e4.agrees.read (by simp <;> simp [Effect.components])).trans ((e3.agrees.read (by simp <;> simp [Effect.components])).trans ((e2.agrees.read (by simp <;> simp [Effect.components])).trans ((e1.agrees.read (by simp <;> simp [Effect.components])).trans (rfl)))))
  have r5b9 : ((Operand.reg 9 : Operand 64).read s5) = v4 := (e5.agrees.read (by simp <;> simp [Effect.components])).trans (v4r9)
  obtain ⟨s6, a6, ready6, e6⟩ :=
    (add_r64_r64_effect_step 0x113dd4 0x4d 0xc1 (by simp [RexWPrefix]) (by decide)).advances ready5 ((code 14 3).of_external_eq m5)
      e5.rip (next 0x13dd7 (by decide))
  change (addR64R64Effect 0x113dd4 9 8 s5).Holds s5 s6 at e6
  have m6 : s6.external = s.external := (e6.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])).trans m5
  have v6r9 : ((Operand.reg 9 : Operand 64).read s6) = q6.1 := by
    have h : ((Operand.reg 9 : Operand 64).read s6) = (addSpec ((Operand.reg 9 : Operand 64).read s5) ((Operand.reg 8 : Operand 64).read s5) ).1 := e6.writes
    rw [r5b8, r5b9] at h
    exact h
  have c6 : (StatusFlags.ofRFLAGS s6.RFLAGS).CF = q6.2.CF := by
    have h : (StatusFlags.ofRFLAGS s6.RFLAGS).CF = (addSpec ((Operand.reg 9 : Operand 64).read s5) ((Operand.reg 8 : Operand 64).read s5) ).2.CF := e6.flags.1
    rw [r5b8, r5b9] at h
    exact h
  have r6b3 : ((Operand.reg 3 : Operand 64).read s6) = (0 : BitVec 64) := (e6.agrees.read (by simp <;> simp [Effect.components])).trans (v5r3)
  have cf6in : (StatusFlags.ofRFLAGS s6.RFLAGS).CF = q6.2.CF := by
    exact c6
  obtain ⟨s7, a7, ready7, e7⟩ :=
    (setcc_r8_effect_step 0x113dd7 0x92 0xc3 (by simp [SupportedOpcode]) (by decide) (by decide)).advances ready6 ((code 17 3).of_external_eq m6)
      e6.rip (next 0x13dda (by decide))
  change (setccR8Effect 0x113dd7 3 3 2 s6).Holds s6 s7 at e7
  have m7 : s7.external = s.external := (e7.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])).trans m6
  have v7r3 : ((Operand.reg 3 : Operand 64).read s7) = v7 := by
    have h : ((Operand.reg 3 : Operand 64).read s7) = mergeGPR 8 (if (StatusFlags.ofRFLAGS s6.RFLAGS).CF then 1 else 0) ((Operand.reg 3 : Operand 64).read s6) := e7.writes
    rw [r6b3, cf6in] at h
    exact h
  have r7b11 : ((Operand.reg 11 : Operand 64).read s7) = ((Operand.reg 11 : Operand 64).read s) := (e7.agrees.read (by simp <;> simp [Effect.components])).trans ((e6.agrees.read (by simp <;> simp [Effect.components])).trans ((e5.agrees.read (by simp <;> simp [Effect.components])).trans ((e4.agrees.read (by simp <;> simp [Effect.components])).trans ((e3.agrees.read (by simp <;> simp [Effect.components])).trans ((e2.agrees.read (by simp <;> simp [Effect.components])).trans ((e1.agrees.read (by simp <;> simp [Effect.components])).trans (rfl)))))))
  have r7b1 : ((Operand.reg 1 : Operand 64).read s7) = v3 := (e7.agrees.read (by simp <;> simp [Effect.components])).trans ((e6.agrees.read (by simp <;> simp [Effect.components])).trans ((e5.agrees.read (by simp <;> simp [Effect.components])).trans ((e4.agrees.read (by simp <;> simp [Effect.components])).trans (v3r1))))
  obtain ⟨s8, a8, ready8, e8⟩ :=
    (and_r64_r64_effect_step 0x113dda 0x4c 0xd9 (by simp [RexWPrefix]) (by decide)).advances ready7 ((code 20 3).of_external_eq m7)
      e7.rip (next 0x13ddd (by decide))
  change (andR64R64Effect 0x113dda 1 11 s7).Holds s7 s8 at e8
  have m8 : s8.external = s.external := (e8.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])).trans m7
  have v8r1 : ((Operand.reg 1 : Operand 64).read s8) = v8 := by
    have h : ((Operand.reg 1 : Operand 64).read s8) = ((Operand.reg 1 : Operand 64).read s7) &&& ((Operand.reg 11 : Operand 64).read s7) := e8.writes
    rw [r7b11, r7b1] at h
    exact h
  have r8b0 : ((Operand.reg 0 : Operand 64).read s8) = ((Operand.reg 0 : Operand 64).read s) := (e8.agrees.read (by simp <;> simp [Effect.components])).trans ((e7.agrees.read (by simp <;> simp [Effect.components])).trans ((e6.agrees.read (by simp <;> simp [Effect.components])).trans ((e5.agrees.read (by simp <;> simp [Effect.components])).trans ((e4.agrees.read (by simp <;> simp [Effect.components])).trans ((e3.agrees.read (by simp <;> simp [Effect.components])).trans ((e2.agrees.read (by simp <;> simp [Effect.components])).trans ((e1.agrees.read (by simp <;> simp [Effect.components])).trans (rfl))))))))
  have r8b2 : ((Operand.reg 2 : Operand 64).read s8) = q2.1 := (e8.agrees.read (by simp <;> simp [Effect.components])).trans ((e7.agrees.read (by simp <;> simp [Effect.components])).trans ((e6.agrees.read (by simp <;> simp [Effect.components])).trans ((e5.agrees.read (by simp <;> simp [Effect.components])).trans ((e4.agrees.read (by simp <;> simp [Effect.components])).trans ((e3.agrees.read (by simp <;> simp [Effect.components])).trans (v2r2))))))
  obtain ⟨s9, a9, ready9, e9⟩ :=
    (cmp_r64_r64_effect_step 0x113ddd 0x48 0xc2 (by simp [RexWPrefix]) (by decide)).advances ready8 ((code 23 3).of_external_eq m8)
      e8.rip (next 0x13de0 (by decide))
  change (cmpR64R64Effect 0x113ddd 2 0 s8).Holds s8 s9 at e9
  have m9 : s9.external = s.external := (e9.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])).trans m8
  have c9 : (StatusFlags.ofRFLAGS s9.RFLAGS).CF = q9.CF := by
    have h : (StatusFlags.ofRFLAGS s9.RFLAGS).CF = (cmpSpec ((Operand.reg 2 : Operand 64).read s8) ((Operand.reg 0 : Operand 64).read s8)).CF := e9.flags.1
    rw [r8b0, r8b2] at h
    exact h
  have r9b9 : ((Operand.reg 9 : Operand 64).read s9) = q6.1 := (e9.agrees.read (by simp <;> simp [Effect.components])).trans ((e8.agrees.read (by simp <;> simp [Effect.components])).trans ((e7.agrees.read (by simp <;> simp [Effect.components])).trans (v6r9)))
  have cf9in : (StatusFlags.ofRFLAGS s9.RFLAGS).CF = q9.CF := by
    exact c9
  obtain ⟨s10, a10, ready10, e10⟩ :=
    (adc_r64_imm8_effect_step 0x113de0 0x49 0xd1 0 (by simp [RexWPrefix]) (by decide) (by decide)).advances ready9 ((code 26 4).of_external_eq m9)
      e9.rip (next 0x13de4 (by decide))
  change (adcR64Imm8Effect 0x113de0 9 0 s9).Holds s9 s10 at e10
  have m10 : s10.external = s.external := (e10.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])).trans m9
  have v10r9 : ((Operand.reg 9 : Operand 64).read s10) = q10.1 := by
    have h : ((Operand.reg 9 : Operand 64).read s10) = (adcSpec ((Operand.reg 9 : Operand 64).read s9) 0 (s9.RFLAGS.extractLsb' 0 1)).1 := e10.writes
    rw [r9b9, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf9in] at h
    exact h
  have c10 : (StatusFlags.ofRFLAGS s10.RFLAGS).CF = q10.2.CF := by
    have h : (StatusFlags.ofRFLAGS s10.RFLAGS).CF = (adcSpec ((Operand.reg 9 : Operand 64).read s9) 0 (s9.RFLAGS.extractLsb' 0 1)).2.CF := e10.flags.1
    rw [r9b9, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf9in] at h
    exact h
  have r10b10 : ((Operand.reg 10 : Operand 64).read s10) = ((Operand.reg 10 : Operand 64).read s) := (e10.agrees.read (by simp <;> simp [Effect.components])).trans ((e9.agrees.read (by simp <;> simp [Effect.components])).trans ((e8.agrees.read (by simp <;> simp [Effect.components])).trans ((e7.agrees.read (by simp <;> simp [Effect.components])).trans ((e6.agrees.read (by simp <;> simp [Effect.components])).trans ((e5.agrees.read (by simp <;> simp [Effect.components])).trans ((e4.agrees.read (by simp <;> simp [Effect.components])).trans ((e3.agrees.read (by simp <;> simp [Effect.components])).trans ((e2.agrees.read (by simp <;> simp [Effect.components])).trans ((e1.agrees.read (by simp <;> simp [Effect.components])).trans (rfl))))))))))
  have r10b3 : ((Operand.reg 3 : Operand 64).read s10) = v7 := (e10.agrees.read (by simp <;> simp [Effect.components])).trans ((e9.agrees.read (by simp <;> simp [Effect.components])).trans ((e8.agrees.read (by simp <;> simp [Effect.components])).trans (v7r3)))
  have cf10in : (StatusFlags.ofRFLAGS s10.RFLAGS).CF = q10.2.CF := by
    exact c10
  obtain ⟨s11, a11, ready11, e11⟩ :=
    (adc_r64_r64_effect_step 0x113de4 0x4c 0xd3 (by simp [RexWPrefix]) (by decide)).advances ready10 ((code 30 3).of_external_eq m10)
      e10.rip (next 0x13de7 (by decide))
  change (adcR64R64Effect 0x113de4 3 10 s10).Holds s10 s11 at e11
  have m11 : s11.external = s.external := (e11.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])).trans m10
  have v11r3 : ((Operand.reg 3 : Operand 64).read s11) = q11.1 := by
    have h : ((Operand.reg 3 : Operand 64).read s11) = (adcSpec ((Operand.reg 3 : Operand 64).read s10) ((Operand.reg 10 : Operand 64).read s10) (s10.RFLAGS.extractLsb' 0 1)).1 := e11.writes
    rw [r10b10, r10b3, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf10in] at h
    exact h
  have c11 : (StatusFlags.ofRFLAGS s11.RFLAGS).CF = q11.2.CF := by
    have h : (StatusFlags.ofRFLAGS s11.RFLAGS).CF = (adcSpec ((Operand.reg 3 : Operand 64).read s10) ((Operand.reg 10 : Operand 64).read s10) (s10.RFLAGS.extractLsb' 0 1)).2.CF := e11.flags.1
    rw [r10b10, r10b3, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf10in] at h
    exact h
  have r11b6 : ((Operand.reg 6 : Operand 64).read s11) = ((Operand.reg 6 : Operand 64).read s) := (e11.agrees.read (by simp <;> simp [Effect.components])).trans ((e10.agrees.read (by simp <;> simp [Effect.components])).trans ((e9.agrees.read (by simp <;> simp [Effect.components])).trans ((e8.agrees.read (by simp <;> simp [Effect.components])).trans ((e7.agrees.read (by simp <;> simp [Effect.components])).trans ((e6.agrees.read (by simp <;> simp [Effect.components])).trans ((e5.agrees.read (by simp <;> simp [Effect.components])).trans ((e4.agrees.read (by simp <;> simp [Effect.components])).trans ((e3.agrees.read (by simp <;> simp [Effect.components])).trans ((e2.agrees.read (by simp <;> simp [Effect.components])).trans ((e1.agrees.read (by simp <;> simp [Effect.components])).trans (rfl)))))))))))
  have r11b1 : ((Operand.reg 1 : Operand 64).read s11) = v8 := (e11.agrees.read (by simp <;> simp [Effect.components])).trans ((e10.agrees.read (by simp <;> simp [Effect.components])).trans ((e9.agrees.read (by simp <;> simp [Effect.components])).trans (v8r1)))
  have cf11in : (StatusFlags.ofRFLAGS s11.RFLAGS).CF = q11.2.CF := by
    exact c11
  obtain ⟨s12, a12, ready12, e12⟩ :=
    (adc_r64_r64_effect_step 0x113de7 0x48 0xf1 (by simp [RexWPrefix]) (by decide)).advances ready11 ((code 33 3).of_external_eq m11)
      e11.rip (next 0x13dea (by decide))
  change (adcR64R64Effect 0x113de7 1 6 s11).Holds s11 s12 at e12
  have m12 : s12.external = s.external := (e12.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])).trans m11
  have v12r1 : ((Operand.reg 1 : Operand 64).read s12) = q12.1 := by
    have h : ((Operand.reg 1 : Operand 64).read s12) = (adcSpec ((Operand.reg 1 : Operand 64).read s11) ((Operand.reg 6 : Operand 64).read s11) (s11.RFLAGS.extractLsb' 0 1)).1 := e12.writes
    rw [r11b6, r11b1, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf11in] at h
    exact h
  have c12 : (StatusFlags.ofRFLAGS s12.RFLAGS).CF = q12.2.CF := by
    have h : (StatusFlags.ofRFLAGS s12.RFLAGS).CF = (adcSpec ((Operand.reg 1 : Operand 64).read s11) ((Operand.reg 6 : Operand 64).read s11) (s11.RFLAGS.extractLsb' 0 1)).2.CF := e12.flags.1
    rw [r11b6, r11b1, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf11in] at h
    exact h
  have flags12 : (StatusFlagsOutcome.ofStatusFlags q12.2).Allows (StatusFlags.ofRFLAGS s12.RFLAGS) := by
    have h : (StatusFlagsOutcome.ofStatusFlags (adcSpec ((Operand.reg 1 : Operand 64).read s11) ((Operand.reg 6 : Operand 64).read s11) (s11.RFLAGS.extractLsb' 0 1)).2).Allows _ := e12.flags
    rw [r11b6, r11b1, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf11in] at h
    exact h
  have r12b1 : ((Operand.reg 1 : Operand 64).read s12) = q12.1 := v12r1
  have r12b2 : ((Operand.reg 2 : Operand 64).read s12) = q2.1 := (e12.agrees.read (by simp <;> simp [Effect.components])).trans ((e11.agrees.read (by simp <;> simp [Effect.components])).trans ((e10.agrees.read (by simp <;> simp [Effect.components])).trans ((e9.agrees.read (by simp <;> simp [Effect.components])).trans ((e8.agrees.read (by simp <;> simp [Effect.components])).trans ((e7.agrees.read (by simp <;> simp [Effect.components])).trans ((e6.agrees.read (by simp <;> simp [Effect.components])).trans ((e5.agrees.read (by simp <;> simp [Effect.components])).trans ((e4.agrees.read (by simp <;> simp [Effect.components])).trans ((e3.agrees.read (by simp <;> simp [Effect.components])).trans (v2r2))))))))))
  have r12b3 : ((Operand.reg 3 : Operand 64).read s12) = q11.1 := (e12.agrees.read (by simp <;> simp [Effect.components])).trans (v11r3)
  have r12b9 : ((Operand.reg 9 : Operand 64).read s12) = q10.1 := (e12.agrees.read (by simp <;> simp [Effect.components])).trans ((e11.agrees.read (by simp <;> simp [Effect.components])).trans (v10r9))
  refine ⟨12, s12, (((((((((((a1).trans a2).trans a3).trans a4).trans a5).trans a6).trans a7).trans a8).trans a9).trans a10).trans a11).trans a12, ready12, loaded.of_external_eq m12, e12.rip, ?_, ?_, ?_⟩
  · exact ⟨r12b1, r12b2, r12b3, r12b9⟩
  · exact flags12
  · apply ((((((((((((e1.agrees).trans e2.agrees).trans e3.agrees).trans e4.agrees).trans e5.agrees).trans e6.agrees).trans e7.agrees).trans e8.agrees).trans e9.agrees).trans e10.agrees).trans e11.agrees).trans e12.agrees).mono
    simp only [movR64R64Effect_components, subR64R64Effect_components, movR32R32Effect_components, xorR32R32Effect_components, addR64R64Effect_components, setccR8Effect_components, andR64R64Effect_components, cmpR64R64Effect_components, adcR64Imm8Effect_components, adcR64R64Effect_components]
    simp [correctionEffect, Effect.components]

theorem correction_bytes :
    Extracted.textBytes.toListFrom 0x13dc6 correctionBytes.length = correctionBytes := by
  decide +kernel

end P256.Proofs.Field.Montgomery.Reduction
