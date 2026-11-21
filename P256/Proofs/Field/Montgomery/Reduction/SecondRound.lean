import P256.Proofs.Common.Field.Montgomery.Schoolbook.CarryCompose
import P256.Proofs.Common.Instructions.ShiftLeft.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import P256.Proofs.Program.Code

set_option autoImplicit false

open P256.Proofs.Common.Instructions (addR64M64Effect addR64M64Effect_components add_r64_m64_effect_step mulHigh64 mulR64Effect mulR64Effect_components mul_r64_effect_step)
open P256.Proofs.Common.Instructions.Carry (adcR64Imm8Effect adcR64Imm8Effect_components adcR64M64Effect_components adcR64R64Effect adcR64R64Effect_components adcSpec adc_r64_imm8_effect_step adc_r64_r64_effect_step)
open P256.Proofs.Common.Instructions.Setb (SupportedOpcode setccR8Effect setccR8Effect_components setcc_r8_effect_step)
open P256.Proofs.Common.Instructions.ShiftLeft (shlR64Effect shlR64Effect_components shl_r64_imm8_effect_step)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Field.Montgomery.Reduction

open P256.Spec.Program.Routines
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

attribute [local simp] mulR64Effect_components adcR64R64Effect_components adcR64Imm8Effect_components
  adcR64M64Effect_components addR64M64Effect_components setccR8Effect_components shlR64Effect_components

structure SecondRoundPre (s : RamState) : Prop where
  rip : s.RIP = 0x113c71
  readable8 : MemReadable s (((Operand.reg 1 : Operand 64).read s) + 0) 8

def secondRoundBytes : List UInt8 :=
  [0x4c, 0x89, 0xc6, 0x4d, 0x89, 0xc7, 0x49, 0xc1, 0xef, 0x20, 0x48, 0xc1, 0xe6, 0x20, 0x4c, 0x89, 0xc0, 0x49, 0xf7, 0xe3, 0x49, 0x89, 0xd0, 0x4c, 0x3, 0x9, 0x49, 0x83, 0xd4, 0x0, 0xf, 0x92, 0xc2, 0x49, 0x1, 0xc1, 0x49, 0x83, 0xd0, 0x0, 0x4c, 0x1, 0xf6, 0x4d, 0x11, 0xd7, 0x49, 0x83, 0xd1, 0x0, 0x49, 0x83, 0xd0, 0x0]

def secondRoundEffect (s : RamState) : Effect :=
  let v3 := ((Operand.reg 8 : Operand 64).read s) >>> 32
  let v4 := ((Operand.reg 8 : Operand 64).read s) <<< 32
  let v6 := ((Operand.reg 8 : Operand 64).read s) * ((Operand.reg 11 : Operand 64).read s)
  let h6 := mulHigh64 ((Operand.reg 8 : Operand 64).read s) ((Operand.reg 11 : Operand 64).read s)
  let q8 := addSpec ((Operand.reg 9 : Operand 64).read s) ((Operand.mem (((Operand.reg 1 : Operand 64).read s) + 0) : Operand 64).read s)
  let q9 := adcSpec ((Operand.reg 12 : Operand 64).read s) 0 (BitVec.ofBool q8.2.CF)
  let v10 := mergeGPR 8 (if q9.2.CF then 1 else 0) h6
  let q11 := addSpec q8.1 v6
  let q12 := adcSpec h6 0 (BitVec.ofBool q11.2.CF)
  let q13 := addSpec v4 ((Operand.reg 14 : Operand 64).read s)
  let q14 := adcSpec v3 ((Operand.reg 10 : Operand 64).read s) (BitVec.ofBool q13.2.CF)
  let q15 := adcSpec q11.1 0 (BitVec.ofBool q14.2.CF)
  let q16 := adcSpec q12.1 0 (BitVec.ofBool q15.2.CF)
  { rip := 0x113ca7
    writes := [⟨(.reg 0 : Operand 64), v6⟩,
      ⟨(.reg 2 : Operand 64), v10⟩,
      ⟨(.reg 6 : Operand 64), q13.1⟩,
      ⟨(.reg 8 : Operand 64), q16.1⟩,
      ⟨(.reg 9 : Operand 64), q15.1⟩,
      ⟨(.reg 12 : Operand 64), q9.1⟩,
      ⟨(.reg 15 : Operand 64), q14.1⟩]
    flags := some (.ofStatusFlags q16.2) }

theorem secondRound_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary SecondRoundPre (codeRange 0x113c71 secondRoundBytes)
      (Effect.post secondRoundEffect) := by
  intro s ready loaded pre
  have next (offset : Nat) (h : offset < 118431) :=
    boundary_ne_program hout (inProgram_of_textOffset offset h)
  have code (offset len : Nat) := loaded.mono (codeRange_slice_subset 0x113c71 secondRoundBytes offset len)
  let v3 := ((Operand.reg 8 : Operand 64).read s) >>> 32
  let v4 := ((Operand.reg 8 : Operand 64).read s) <<< 32
  let v6 := ((Operand.reg 8 : Operand 64).read s) * ((Operand.reg 11 : Operand 64).read s)
  let h6 := mulHigh64 ((Operand.reg 8 : Operand 64).read s) ((Operand.reg 11 : Operand 64).read s)
  let q8 := addSpec ((Operand.reg 9 : Operand 64).read s) ((Operand.mem (((Operand.reg 1 : Operand 64).read s) + 0) : Operand 64).read s)
  let q9 := adcSpec ((Operand.reg 12 : Operand 64).read s) 0 (BitVec.ofBool q8.2.CF)
  let v10 := mergeGPR 8 (if q9.2.CF then 1 else 0) h6
  let q11 := addSpec q8.1 v6
  let q12 := adcSpec h6 0 (BitVec.ofBool q11.2.CF)
  let q13 := addSpec v4 ((Operand.reg 14 : Operand 64).read s)
  let q14 := adcSpec v3 ((Operand.reg 10 : Operand 64).read s) (BitVec.ofBool q13.2.CF)
  let q15 := adcSpec q11.1 0 (BitVec.ofBool q14.2.CF)
  let q16 := adcSpec q12.1 0 (BitVec.ofBool q15.2.CF)
  obtain ⟨s1, a1, ready1, e1⟩ :=
    (mov_r64_r64_effect_step 0x113c71 0x4c 0xc6 (by simp [RexWPrefix]) (by decide)).advances ready (code 0 3)
      pre.rip (next 0x13c74 (by decide))
  change (movR64R64Effect 0x113c71 6 8 s).Holds s s1 at e1
  have m1 : s1.external = s.external := (e1.agrees.external (by simp [Component.Covers]))
  have v1r6 : ((Operand.reg 6 : Operand 64).read s1) = ((Operand.reg 8 : Operand 64).read s) := by
    have h : ((Operand.reg 6 : Operand 64).read s1) = ((Operand.reg 8 : Operand 64).read s) := e1.writes
    exact h
  have r1b8 : ((Operand.reg 8 : Operand 64).read s1) = ((Operand.reg 8 : Operand 64).read s) := (e1.agrees.read (by simp)).trans (rfl)
  obtain ⟨s2, a2, ready2, e2⟩ :=
    (mov_r64_r64_effect_step 0x113c74 0x4d 0xc7 (by simp [RexWPrefix]) (by decide)).advances ready1 ((code 3 3).of_external_eq m1)
      e1.rip (next 0x13c77 (by decide))
  change (movR64R64Effect 0x113c74 15 8 s1).Holds s1 s2 at e2
  have m2 : s2.external = s.external := (e2.agrees.external (by simp [Component.Covers])).trans m1
  have v2r15 : ((Operand.reg 15 : Operand 64).read s2) = ((Operand.reg 8 : Operand 64).read s) := by
    have h : ((Operand.reg 15 : Operand 64).read s2) = ((Operand.reg 8 : Operand 64).read s1) := e2.writes
    rw [r1b8] at h
    exact h
  have r2b15 : ((Operand.reg 15 : Operand 64).read s2) = ((Operand.reg 8 : Operand 64).read s) := v2r15
  obtain ⟨s3, a3, ready3, e3⟩ :=
    (shr_r64_imm8_effect_step 0x113c77 0x49 0xef 32 (by simp [RexWPrefix]) (by decide) (by decide)).advances ready2 ((code 6 4).of_external_eq m2)
      e2.rip (next 0x13c7b (by decide))
  change (shrR64Effect 0x113c77 4 15 32 s2).Holds s2 s3 at e3
  have m3 : s3.external = s.external := (e3.agrees.external (by simp [Component.Covers])).trans m2
  have v3r15 : ((Operand.reg 15 : Operand 64).read s3) = v3 := by
    have h : ((Operand.reg 15 : Operand 64).read s3) = ((Operand.reg 15 : Operand 64).read s2) >>> 32 := e3.writes
    rw [r2b15] at h
    exact h
  have r3b6 : ((Operand.reg 6 : Operand 64).read s3) = ((Operand.reg 8 : Operand 64).read s) := (e3.agrees.read (by simp)).trans ((e2.agrees.read (by simp)).trans (v1r6))
  obtain ⟨s4, a4, ready4, e4⟩ :=
    (shl_r64_imm8_effect_step 0x113c7b 0x48 0xe6 32 (by simp [RexWPrefix]) (by decide) (by decide)).advances ready3 ((code 10 4).of_external_eq m3)
      e3.rip (next 0x13c7f (by decide))
  change (shlR64Effect 0x113c7b 4 6 32 s3).Holds s3 s4 at e4
  have m4 : s4.external = s.external := (e4.agrees.external (by simp [Component.Covers])).trans m3
  have v4r6 : ((Operand.reg 6 : Operand 64).read s4) = v4 := by
    have h : ((Operand.reg 6 : Operand 64).read s4) = ((Operand.reg 6 : Operand 64).read s3) <<< 32 := e4.writes
    rw [r3b6] at h
    exact h
  have r4b8 : ((Operand.reg 8 : Operand 64).read s4) = ((Operand.reg 8 : Operand 64).read s) := (e4.agrees.read (by simp)).trans ((e3.agrees.read (by simp)).trans ((e2.agrees.read (by simp)).trans ((e1.agrees.read (by simp)).trans (rfl))))
  obtain ⟨s5, a5, ready5, e5⟩ :=
    (mov_r64_r64_effect_step 0x113c7f 0x4c 0xc0 (by simp [RexWPrefix]) (by decide)).advances ready4 ((code 14 3).of_external_eq m4)
      e4.rip (next 0x13c82 (by decide))
  change (movR64R64Effect 0x113c7f 0 8 s4).Holds s4 s5 at e5
  have m5 : s5.external = s.external := (e5.agrees.external (by simp [Component.Covers])).trans m4
  have v5r0 : ((Operand.reg 0 : Operand 64).read s5) = ((Operand.reg 8 : Operand 64).read s) := by
    have h : ((Operand.reg 0 : Operand 64).read s5) = ((Operand.reg 8 : Operand 64).read s4) := e5.writes
    rw [r4b8] at h
    exact h
  have r5b11 : ((Operand.reg 11 : Operand 64).read s5) = ((Operand.reg 11 : Operand 64).read s) := (e5.agrees.read (by simp)).trans ((e4.agrees.read (by simp)).trans ((e3.agrees.read (by simp)).trans ((e2.agrees.read (by simp)).trans ((e1.agrees.read (by simp)).trans (rfl)))))
  have r5b0 : ((Operand.reg 0 : Operand 64).read s5) = ((Operand.reg 8 : Operand 64).read s) := v5r0
  obtain ⟨s6, a6, ready6, e6⟩ :=
    (mul_r64_effect_step 0x113c82 0x49 0xe3 (by simp [RexWPrefix]) (by decide) (by decide)).advances ready5 ((code 17 3).of_external_eq m5)
      e5.rip (next 0x13c85 (by decide))
  change (mulR64Effect 0x113c82 11 s5).Holds s5 s6 at e6
  have m6 : s6.external = s.external := (e6.agrees.external (by simp [Component.Covers])).trans m5
  have v6r0 : ((Operand.reg 0 : Operand 64).read s6) = v6 := by
    have h : ((Operand.reg 0 : Operand 64).read s6) = ((Operand.reg 0 : Operand 64).read s5) * ((Operand.reg 11 : Operand 64).read s5) := e6.writes.1
    rw [r5b11, r5b0] at h
    exact h
  have v6r2 : ((Operand.reg 2 : Operand 64).read s6) = h6 := by
    have h : ((Operand.reg 2 : Operand 64).read s6) = mulHigh64 ((Operand.reg 0 : Operand 64).read s5) ((Operand.reg 11 : Operand 64).read s5) := e6.writes.2
    rw [r5b11, r5b0] at h
    exact h
  have r6b2 : ((Operand.reg 2 : Operand 64).read s6) = h6 := v6r2
  obtain ⟨s7, a7, ready7, e7⟩ :=
    (mov_r64_r64_effect_step 0x113c85 0x49 0xd0 (by simp [RexWPrefix]) (by decide)).advances ready6 ((code 20 3).of_external_eq m6)
      e6.rip (next 0x13c88 (by decide))
  change (movR64R64Effect 0x113c85 8 2 s6).Holds s6 s7 at e7
  have m7 : s7.external = s.external := (e7.agrees.external (by simp [Component.Covers])).trans m6
  have v7r8 : ((Operand.reg 8 : Operand 64).read s7) = h6 := by
    have h : ((Operand.reg 8 : Operand 64).read s7) = ((Operand.reg 2 : Operand 64).read s6) := e7.writes
    rw [r6b2] at h
    exact h
  have r7b1 : ((Operand.reg 1 : Operand 64).read s7) = ((Operand.reg 1 : Operand 64).read s) := (e7.agrees.read (by simp)).trans ((e6.agrees.read (by simp)).trans ((e5.agrees.read (by simp)).trans ((e4.agrees.read (by simp)).trans ((e3.agrees.read (by simp)).trans ((e2.agrees.read (by simp)).trans ((e1.agrees.read (by simp)).trans (rfl)))))))
  have mr8 : MemReadable s7 (((Operand.reg 1 : Operand 64).read s7) + 0) 8 := by
    rw [r7b1]
    exact pre.readable8.of_external_eq m7
  have mv8 : (Operand.mem (((Operand.reg 1 : Operand 64).read s7) + 0) : Operand 64).read s7 = ((Operand.mem (((Operand.reg 1 : Operand 64).read s) + 0) : Operand 64).read s) := by
    change memLoad _ _ 64 = memLoad _ _ 64
    rw [m7, r7b1]
  have r7b9 : ((Operand.reg 9 : Operand 64).read s7) = ((Operand.reg 9 : Operand 64).read s) := (e7.agrees.read (by simp)).trans ((e6.agrees.read (by simp)).trans ((e5.agrees.read (by simp)).trans ((e4.agrees.read (by simp)).trans ((e3.agrees.read (by simp)).trans ((e2.agrees.read (by simp)).trans ((e1.agrees.read (by simp)).trans (rfl)))))))
  obtain ⟨s8, a8, ready8, e8⟩ :=
    (add_r64_m64_effect_step 0x113c88 0x4c (by simp [RexWPrefix]) 1 (.base 1 .none) (by decide) rfl rfl).advances ready7 ((code 23 3).of_external_eq m7)
      ⟨e7.rip, mr8⟩ (next 0x13c8b (by decide))
  change (addR64M64Effect 0x113c88 9 (.base 1 .none) s7).Holds s7 s8 at e8
  have m8 : s8.external = s.external := (e8.agrees.external (by simp [Component.Covers])).trans m7
  have v8r9 : ((Operand.reg 9 : Operand 64).read s8) = q8.1 := by
    have h : ((Operand.reg 9 : Operand 64).read s8) = (addSpec ((Operand.reg 9 : Operand 64).read s7) ((Operand.mem (((Operand.reg 1 : Operand 64).read s7) + 0) : Operand 64).read s7) ).1 := e8.writes
    rw [mv8, r7b9] at h
    exact h
  have c8 : (StatusFlags.ofRFLAGS s8.RFLAGS).CF = q8.2.CF := by
    have h : (StatusFlags.ofRFLAGS s8.RFLAGS).CF = (addSpec ((Operand.reg 9 : Operand 64).read s7) ((Operand.mem (((Operand.reg 1 : Operand 64).read s7) + 0) : Operand 64).read s7) ).2.CF := e8.flags.1
    rw [mv8, r7b9] at h
    exact h
  have r8b12 : ((Operand.reg 12 : Operand 64).read s8) = ((Operand.reg 12 : Operand 64).read s) := (e8.agrees.read (by simp)).trans ((e7.agrees.read (by simp)).trans ((e6.agrees.read (by simp)).trans ((e5.agrees.read (by simp)).trans ((e4.agrees.read (by simp)).trans ((e3.agrees.read (by simp)).trans ((e2.agrees.read (by simp)).trans ((e1.agrees.read (by simp)).trans (rfl))))))))
  have cf8in : (StatusFlags.ofRFLAGS s8.RFLAGS).CF = q8.2.CF := by
    exact c8
  obtain ⟨s9, a9, ready9, e9⟩ :=
    (adc_r64_imm8_effect_step 0x113c8b 0x49 0xd4 0 (by simp [RexWPrefix]) (by decide) (by decide)).advances ready8 ((code 26 4).of_external_eq m8)
      e8.rip (next 0x13c8f (by decide))
  change (adcR64Imm8Effect 0x113c8b 12 0 s8).Holds s8 s9 at e9
  have m9 : s9.external = s.external := (e9.agrees.external (by simp [Component.Covers])).trans m8
  have v9r12 : ((Operand.reg 12 : Operand 64).read s9) = q9.1 := by
    have h : ((Operand.reg 12 : Operand 64).read s9) = (adcSpec ((Operand.reg 12 : Operand 64).read s8) 0 (s8.RFLAGS.extractLsb' 0 1)).1 := e9.writes
    rw [r8b12, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf8in] at h
    exact h
  have c9 : (StatusFlags.ofRFLAGS s9.RFLAGS).CF = q9.2.CF := by
    have h : (StatusFlags.ofRFLAGS s9.RFLAGS).CF = (adcSpec ((Operand.reg 12 : Operand 64).read s8) 0 (s8.RFLAGS.extractLsb' 0 1)).2.CF := e9.flags.1
    rw [r8b12, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf8in] at h
    exact h
  have r9b2 : ((Operand.reg 2 : Operand 64).read s9) = h6 := (e9.agrees.read (by simp)).trans ((e8.agrees.read (by simp)).trans ((e7.agrees.read (by simp)).trans (v6r2)))
  have cf9in : (StatusFlags.ofRFLAGS s9.RFLAGS).CF = q9.2.CF := by
    exact c9
  obtain ⟨s10, a10, ready10, e10⟩ :=
    (setcc_r8_effect_step 0x113c8f 0x92 0xc2 (by simp [SupportedOpcode]) (by decide) (by decide)).advances ready9 ((code 30 3).of_external_eq m9)
      e9.rip (next 0x13c92 (by decide))
  change (setccR8Effect 0x113c8f 3 2 2 s9).Holds s9 s10 at e10
  have m10 : s10.external = s.external := (e10.agrees.external (by simp [Component.Covers])).trans m9
  have v10r2 : ((Operand.reg 2 : Operand 64).read s10) = v10 := by
    have h : ((Operand.reg 2 : Operand 64).read s10) = mergeGPR 8 (if (StatusFlags.ofRFLAGS s9.RFLAGS).CF then 1 else 0) ((Operand.reg 2 : Operand 64).read s9) := e10.writes
    rw [r9b2, cf9in] at h
    exact h
  have r10b0 : ((Operand.reg 0 : Operand 64).read s10) = v6 := (e10.agrees.read (by simp)).trans ((e9.agrees.read (by simp)).trans ((e8.agrees.read (by simp)).trans ((e7.agrees.read (by simp)).trans (v6r0))))
  have r10b9 : ((Operand.reg 9 : Operand 64).read s10) = q8.1 := (e10.agrees.read (by simp)).trans ((e9.agrees.read (by simp)).trans (v8r9))
  obtain ⟨s11, a11, ready11, e11⟩ :=
    (add_r64_r64_effect_step 0x113c92 0x49 0xc1 (by simp [RexWPrefix]) (by decide)).advances ready10 ((code 33 3).of_external_eq m10)
      e10.rip (next 0x13c95 (by decide))
  change (addR64R64Effect 0x113c92 9 0 s10).Holds s10 s11 at e11
  have m11 : s11.external = s.external := (e11.agrees.external (by simp [Component.Covers])).trans m10
  have v11r9 : ((Operand.reg 9 : Operand 64).read s11) = q11.1 := by
    have h : ((Operand.reg 9 : Operand 64).read s11) = (addSpec ((Operand.reg 9 : Operand 64).read s10) ((Operand.reg 0 : Operand 64).read s10) ).1 := e11.writes
    rw [r10b0, r10b9] at h
    exact h
  have c11 : (StatusFlags.ofRFLAGS s11.RFLAGS).CF = q11.2.CF := by
    have h : (StatusFlags.ofRFLAGS s11.RFLAGS).CF = (addSpec ((Operand.reg 9 : Operand 64).read s10) ((Operand.reg 0 : Operand 64).read s10) ).2.CF := e11.flags.1
    rw [r10b0, r10b9] at h
    exact h
  have r11b8 : ((Operand.reg 8 : Operand 64).read s11) = h6 := (e11.agrees.read (by simp)).trans ((e10.agrees.read (by simp)).trans ((e9.agrees.read (by simp)).trans ((e8.agrees.read (by simp)).trans (v7r8))))
  have cf11in : (StatusFlags.ofRFLAGS s11.RFLAGS).CF = q11.2.CF := by
    exact c11
  obtain ⟨s12, a12, ready12, e12⟩ :=
    (adc_r64_imm8_effect_step 0x113c95 0x49 0xd0 0 (by simp [RexWPrefix]) (by decide) (by decide)).advances ready11 ((code 36 4).of_external_eq m11)
      e11.rip (next 0x13c99 (by decide))
  change (adcR64Imm8Effect 0x113c95 8 0 s11).Holds s11 s12 at e12
  have m12 : s12.external = s.external := (e12.agrees.external (by simp [Component.Covers])).trans m11
  have v12r8 : ((Operand.reg 8 : Operand 64).read s12) = q12.1 := by
    have h : ((Operand.reg 8 : Operand 64).read s12) = (adcSpec ((Operand.reg 8 : Operand 64).read s11) 0 (s11.RFLAGS.extractLsb' 0 1)).1 := e12.writes
    rw [r11b8, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf11in] at h
    exact h
  have c12 : (StatusFlags.ofRFLAGS s12.RFLAGS).CF = q12.2.CF := by
    have h : (StatusFlags.ofRFLAGS s12.RFLAGS).CF = (adcSpec ((Operand.reg 8 : Operand 64).read s11) 0 (s11.RFLAGS.extractLsb' 0 1)).2.CF := e12.flags.1
    rw [r11b8, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf11in] at h
    exact h
  have r12b14 : ((Operand.reg 14 : Operand 64).read s12) = ((Operand.reg 14 : Operand 64).read s) := (e12.agrees.read (by simp)).trans ((e11.agrees.read (by simp)).trans ((e10.agrees.read (by simp)).trans ((e9.agrees.read (by simp)).trans ((e8.agrees.read (by simp)).trans ((e7.agrees.read (by simp)).trans ((e6.agrees.read (by simp)).trans ((e5.agrees.read (by simp)).trans ((e4.agrees.read (by simp)).trans ((e3.agrees.read (by simp)).trans ((e2.agrees.read (by simp)).trans ((e1.agrees.read (by simp)).trans (rfl))))))))))))
  have r12b6 : ((Operand.reg 6 : Operand 64).read s12) = v4 := (e12.agrees.read (by simp)).trans ((e11.agrees.read (by simp)).trans ((e10.agrees.read (by simp)).trans ((e9.agrees.read (by simp)).trans ((e8.agrees.read (by simp)).trans ((e7.agrees.read (by simp)).trans ((e6.agrees.read (by simp)).trans ((e5.agrees.read (by simp)).trans (v4r6))))))))
  obtain ⟨s13, a13, ready13, e13⟩ :=
    (add_r64_r64_effect_step 0x113c99 0x4c 0xf6 (by simp [RexWPrefix]) (by decide)).advances ready12 ((code 40 3).of_external_eq m12)
      e12.rip (next 0x13c9c (by decide))
  change (addR64R64Effect 0x113c99 6 14 s12).Holds s12 s13 at e13
  have m13 : s13.external = s.external := (e13.agrees.external (by simp [Component.Covers])).trans m12
  have v13r6 : ((Operand.reg 6 : Operand 64).read s13) = q13.1 := by
    have h : ((Operand.reg 6 : Operand 64).read s13) = (addSpec ((Operand.reg 6 : Operand 64).read s12) ((Operand.reg 14 : Operand 64).read s12) ).1 := e13.writes
    rw [r12b14, r12b6] at h
    exact h
  have c13 : (StatusFlags.ofRFLAGS s13.RFLAGS).CF = q13.2.CF := by
    have h : (StatusFlags.ofRFLAGS s13.RFLAGS).CF = (addSpec ((Operand.reg 6 : Operand 64).read s12) ((Operand.reg 14 : Operand 64).read s12) ).2.CF := e13.flags.1
    rw [r12b14, r12b6] at h
    exact h
  have r13b10 : ((Operand.reg 10 : Operand 64).read s13) = ((Operand.reg 10 : Operand 64).read s) := (e13.agrees.read (by simp)).trans ((e12.agrees.read (by simp)).trans ((e11.agrees.read (by simp)).trans ((e10.agrees.read (by simp)).trans ((e9.agrees.read (by simp)).trans ((e8.agrees.read (by simp)).trans ((e7.agrees.read (by simp)).trans ((e6.agrees.read (by simp)).trans ((e5.agrees.read (by simp)).trans ((e4.agrees.read (by simp)).trans ((e3.agrees.read (by simp)).trans ((e2.agrees.read (by simp)).trans ((e1.agrees.read (by simp)).trans (rfl)))))))))))))
  have r13b15 : ((Operand.reg 15 : Operand 64).read s13) = v3 := (e13.agrees.read (by simp)).trans ((e12.agrees.read (by simp)).trans ((e11.agrees.read (by simp)).trans ((e10.agrees.read (by simp)).trans ((e9.agrees.read (by simp)).trans ((e8.agrees.read (by simp)).trans ((e7.agrees.read (by simp)).trans ((e6.agrees.read (by simp)).trans ((e5.agrees.read (by simp)).trans ((e4.agrees.read (by simp)).trans (v3r15))))))))))
  have cf13in : (StatusFlags.ofRFLAGS s13.RFLAGS).CF = q13.2.CF := by
    exact c13
  obtain ⟨s14, a14, ready14, e14⟩ :=
    (adc_r64_r64_effect_step 0x113c9c 0x4d 0xd7 (by simp [RexWPrefix]) (by decide)).advances ready13 ((code 43 3).of_external_eq m13)
      e13.rip (next 0x13c9f (by decide))
  change (adcR64R64Effect 0x113c9c 15 10 s13).Holds s13 s14 at e14
  have m14 : s14.external = s.external := (e14.agrees.external (by simp [Component.Covers])).trans m13
  have v14r15 : ((Operand.reg 15 : Operand 64).read s14) = q14.1 := by
    have h : ((Operand.reg 15 : Operand 64).read s14) = (adcSpec ((Operand.reg 15 : Operand 64).read s13) ((Operand.reg 10 : Operand 64).read s13) (s13.RFLAGS.extractLsb' 0 1)).1 := e14.writes
    rw [r13b10, r13b15, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf13in] at h
    exact h
  have c14 : (StatusFlags.ofRFLAGS s14.RFLAGS).CF = q14.2.CF := by
    have h : (StatusFlags.ofRFLAGS s14.RFLAGS).CF = (adcSpec ((Operand.reg 15 : Operand 64).read s13) ((Operand.reg 10 : Operand 64).read s13) (s13.RFLAGS.extractLsb' 0 1)).2.CF := e14.flags.1
    rw [r13b10, r13b15, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf13in] at h
    exact h
  have r14b9 : ((Operand.reg 9 : Operand 64).read s14) = q11.1 := (e14.agrees.read (by simp)).trans ((e13.agrees.read (by simp)).trans ((e12.agrees.read (by simp)).trans (v11r9)))
  have cf14in : (StatusFlags.ofRFLAGS s14.RFLAGS).CF = q14.2.CF := by
    exact c14
  obtain ⟨s15, a15, ready15, e15⟩ :=
    (adc_r64_imm8_effect_step 0x113c9f 0x49 0xd1 0 (by simp [RexWPrefix]) (by decide) (by decide)).advances ready14 ((code 46 4).of_external_eq m14)
      e14.rip (next 0x13ca3 (by decide))
  change (adcR64Imm8Effect 0x113c9f 9 0 s14).Holds s14 s15 at e15
  have m15 : s15.external = s.external := (e15.agrees.external (by simp [Component.Covers])).trans m14
  have v15r9 : ((Operand.reg 9 : Operand 64).read s15) = q15.1 := by
    have h : ((Operand.reg 9 : Operand 64).read s15) = (adcSpec ((Operand.reg 9 : Operand 64).read s14) 0 (s14.RFLAGS.extractLsb' 0 1)).1 := e15.writes
    rw [r14b9, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf14in] at h
    exact h
  have c15 : (StatusFlags.ofRFLAGS s15.RFLAGS).CF = q15.2.CF := by
    have h : (StatusFlags.ofRFLAGS s15.RFLAGS).CF = (adcSpec ((Operand.reg 9 : Operand 64).read s14) 0 (s14.RFLAGS.extractLsb' 0 1)).2.CF := e15.flags.1
    rw [r14b9, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf14in] at h
    exact h
  have r15b8 : ((Operand.reg 8 : Operand 64).read s15) = q12.1 := (e15.agrees.read (by simp)).trans ((e14.agrees.read (by simp)).trans ((e13.agrees.read (by simp)).trans (v12r8)))
  have cf15in : (StatusFlags.ofRFLAGS s15.RFLAGS).CF = q15.2.CF := by
    exact c15
  obtain ⟨s16, a16, ready16, e16⟩ :=
    (adc_r64_imm8_effect_step 0x113ca3 0x49 0xd0 0 (by simp [RexWPrefix]) (by decide) (by decide)).advances ready15 ((code 50 4).of_external_eq m15)
      e15.rip (next 0x13ca7 (by decide))
  change (adcR64Imm8Effect 0x113ca3 8 0 s15).Holds s15 s16 at e16
  have m16 : s16.external = s.external := (e16.agrees.external (by simp [Component.Covers])).trans m15
  have v16r8 : ((Operand.reg 8 : Operand 64).read s16) = q16.1 := by
    have h : ((Operand.reg 8 : Operand 64).read s16) = (adcSpec ((Operand.reg 8 : Operand 64).read s15) 0 (s15.RFLAGS.extractLsb' 0 1)).1 := e16.writes
    rw [r15b8, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf15in] at h
    exact h
  have c16 : (StatusFlags.ofRFLAGS s16.RFLAGS).CF = q16.2.CF := by
    have h : (StatusFlags.ofRFLAGS s16.RFLAGS).CF = (adcSpec ((Operand.reg 8 : Operand 64).read s15) 0 (s15.RFLAGS.extractLsb' 0 1)).2.CF := e16.flags.1
    rw [r15b8, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf15in] at h
    exact h
  have flags16 : (StatusFlagsOutcome.ofStatusFlags q16.2).Allows (StatusFlags.ofRFLAGS s16.RFLAGS) := by
    have h : (StatusFlagsOutcome.ofStatusFlags (adcSpec ((Operand.reg 8 : Operand 64).read s15) 0 (s15.RFLAGS.extractLsb' 0 1)).2).Allows _ := e16.flags
    rw [r15b8, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf15in] at h
    exact h
  have r16b0 : ((Operand.reg 0 : Operand 64).read s16) = v6 := (e16.agrees.read (by simp)).trans ((e15.agrees.read (by simp)).trans ((e14.agrees.read (by simp)).trans ((e13.agrees.read (by simp)).trans ((e12.agrees.read (by simp)).trans ((e11.agrees.read (by simp)).trans ((e10.agrees.read (by simp)).trans ((e9.agrees.read (by simp)).trans ((e8.agrees.read (by simp)).trans ((e7.agrees.read (by simp)).trans (v6r0))))))))))
  have r16b2 : ((Operand.reg 2 : Operand 64).read s16) = v10 := (e16.agrees.read (by simp)).trans ((e15.agrees.read (by simp)).trans ((e14.agrees.read (by simp)).trans ((e13.agrees.read (by simp)).trans ((e12.agrees.read (by simp)).trans ((e11.agrees.read (by simp)).trans (v10r2))))))
  have r16b6 : ((Operand.reg 6 : Operand 64).read s16) = q13.1 := (e16.agrees.read (by simp)).trans ((e15.agrees.read (by simp)).trans ((e14.agrees.read (by simp)).trans (v13r6)))
  have r16b8 : ((Operand.reg 8 : Operand 64).read s16) = q16.1 := v16r8
  have r16b9 : ((Operand.reg 9 : Operand 64).read s16) = q15.1 := (e16.agrees.read (by simp)).trans (v15r9)
  have r16b12 : ((Operand.reg 12 : Operand 64).read s16) = q9.1 := (e16.agrees.read (by simp)).trans ((e15.agrees.read (by simp)).trans ((e14.agrees.read (by simp)).trans ((e13.agrees.read (by simp)).trans ((e12.agrees.read (by simp)).trans ((e11.agrees.read (by simp)).trans ((e10.agrees.read (by simp)).trans (v9r12)))))))
  have r16b15 : ((Operand.reg 15 : Operand 64).read s16) = q14.1 := (e16.agrees.read (by simp)).trans ((e15.agrees.read (by simp)).trans (v14r15))
  refine ⟨16, s16, (((((((((((((((a1).trans a2).trans a3).trans a4).trans a5).trans a6).trans a7).trans a8).trans a9).trans a10).trans a11).trans a12).trans a13).trans a14).trans a15).trans a16, ready16, loaded.of_external_eq m16, e16.rip, ?_, ?_, ?_⟩
  · exact ⟨r16b0, r16b2, r16b6, r16b8, r16b9, r16b12, r16b15⟩
  · exact flags16
  · apply ((((((((((((((((e1.agrees).trans e2.agrees).trans e3.agrees).trans e4.agrees).trans e5.agrees).trans e6.agrees).trans e7.agrees).trans e8.agrees).trans e9.agrees).trans e10.agrees).trans e11.agrees).trans e12.agrees).trans e13.agrees).trans e14.agrees).trans e15.agrees).trans e16.agrees).mono
    simp only [movR64R64Effect_components, shrR64Effect_components, shlR64Effect_components, mulR64Effect_components, addR64M64Effect_components, adcR64Imm8Effect_components, setccR8Effect_components, addR64R64Effect_components, adcR64R64Effect_components]
    simp [secondRoundEffect, Effect.components]

theorem secondRound_bytes :
    Extracted.textBytes.toListFrom 0x13c71 secondRoundBytes.length = secondRoundBytes := by
  decide +kernel

end P256.Proofs.Field.Montgomery.Reduction
