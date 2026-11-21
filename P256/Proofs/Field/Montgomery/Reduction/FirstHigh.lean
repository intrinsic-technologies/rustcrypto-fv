import P256.Proofs.Common.Field.Montgomery.Schoolbook.CarryCompose
import P256.Proofs.Common.Instructions.ShiftLeft.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import P256.Proofs.Program.Code

set_option autoImplicit false

open P256.Proofs.Common.Instructions (addR64M64Effect addR64M64Effect_components add_r64_m64_effect_step mulHigh64 mulR64Effect mulR64Effect_components mul_r64_effect_step)
open P256.Proofs.Common.Instructions.Carry (adcR64Imm8Effect adcR64Imm8Effect_components adcR64M64Effect_components adcR64R64Effect_components adcSpec adc_r64_imm8_effect_step)
open P256.Proofs.Common.Instructions.Setb (setccR8Effect_components)
open P256.Proofs.Common.Instructions.ShiftLeft (shlR64Effect_components)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Field.Montgomery.Reduction

open P256.Spec.Program.Routines
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

attribute [local simp] mulR64Effect_components adcR64R64Effect_components adcR64Imm8Effect_components
  adcR64M64Effect_components addR64M64Effect_components setccR8Effect_components shlR64Effect_components

structure FirstHighPre (s : RamState) : Prop where
  rip : s.RIP = 0x113c43
  readable6 : MemReadable s (((Operand.reg 6 : Operand 64).read s) + 24) 8
  readable8 : MemReadable s (((Operand.reg 6 : Operand 64).read s) + 16) 8
  readable10 : MemReadable s (((Operand.reg 1 : Operand 64).read s) + 8) 8

def firstHighBytes : List UInt8 :=
  [0x49, 0xbb, 0x1, 0x0, 0x0, 0x0, 0xff, 0xff, 0xff, 0xff, 0x4c, 0x89, 0xc8, 0x49, 0xf7, 0xe3, 0x49, 0x89, 0xd1, 0x49, 0x89, 0xc2, 0x4c, 0x3, 0x56, 0x18, 0x49, 0x83, 0xd1, 0x0, 0x4c, 0x3, 0x76, 0x10, 0x49, 0x83, 0xd2, 0x0, 0x4c, 0x8b, 0x61, 0x8, 0x49, 0x83, 0xd1, 0x0]

def firstHighEffect (s : RamState) : Effect :=
  let v3 := ((Operand.reg 9 : Operand 64).read s) * 18446744069414584321
  let h3 := mulHigh64 ((Operand.reg 9 : Operand 64).read s) 18446744069414584321
  let q6 := addSpec v3 ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 24) : Operand 64).read s)
  let q7 := adcSpec h3 0 (BitVec.ofBool q6.2.CF)
  let q8 := addSpec ((Operand.reg 14 : Operand 64).read s) ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 16) : Operand 64).read s)
  let q9 := adcSpec q6.1 0 (BitVec.ofBool q8.2.CF)
  let q11 := adcSpec q7.1 0 (BitVec.ofBool q9.2.CF)
  { rip := 0x113c71
    writes := [⟨(.reg 0 : Operand 64), v3⟩,
      ⟨(.reg 2 : Operand 64), h3⟩,
      ⟨(.reg 9 : Operand 64), q11.1⟩,
      ⟨(.reg 10 : Operand 64), q9.1⟩,
      ⟨(.reg 11 : Operand 64), 18446744069414584321⟩,
      ⟨(.reg 12 : Operand 64), ((Operand.mem (((Operand.reg 1 : Operand 64).read s) + 8) : Operand 64).read s)⟩,
      ⟨(.reg 14 : Operand 64), q8.1⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem firstHigh_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary FirstHighPre (codeRange 0x113c43 firstHighBytes)
      (Effect.post firstHighEffect) := by
  intro s ready loaded pre
  have next (offset : Nat) (h : offset < 118431) :=
    boundary_ne_program hout (inProgram_of_textOffset offset h)
  have code (offset len : Nat) := loaded.mono (codeRange_slice_subset 0x113c43 firstHighBytes offset len)
  let v3 := ((Operand.reg 9 : Operand 64).read s) * 18446744069414584321
  let h3 := mulHigh64 ((Operand.reg 9 : Operand 64).read s) 18446744069414584321
  let q6 := addSpec v3 ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 24) : Operand 64).read s)
  let q7 := adcSpec h3 0 (BitVec.ofBool q6.2.CF)
  let q8 := addSpec ((Operand.reg 14 : Operand 64).read s) ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 16) : Operand 64).read s)
  let q9 := adcSpec q6.1 0 (BitVec.ofBool q8.2.CF)
  let q11 := adcSpec q7.1 0 (BitVec.ofBool q9.2.CF)
  obtain ⟨s1, a1, ready1, e1⟩ :=
    (mov_r64_imm64_effect_step 0x113c43 0x49 0xbb (by simp [RexWPrefix]) (by decide) 18446744069414584321).advances ready (code 0 10)
      pre.rip (next 0x13c4d (by decide))
  change (movR64Imm64Effect 0x113c43 11 18446744069414584321 s).Holds s s1 at e1
  have m1 : s1.external = s.external := (e1.agrees.external (by simp [Component.Covers]))
  have v1r11 : ((Operand.reg 11 : Operand 64).read s1) = 18446744069414584321 := by
    have h : ((Operand.reg 11 : Operand 64).read s1) = 18446744069414584321 := e1.writes
    exact h
  have r1b9 : ((Operand.reg 9 : Operand 64).read s1) = ((Operand.reg 9 : Operand 64).read s) := (e1.agrees.read (by simp)).trans (rfl)
  obtain ⟨s2, a2, ready2, e2⟩ :=
    (mov_r64_r64_effect_step 0x113c4d 0x4c 0xc8 (by simp [RexWPrefix]) (by decide)).advances ready1 ((code 10 3).of_external_eq m1)
      e1.rip (next 0x13c50 (by decide))
  change (movR64R64Effect 0x113c4d 0 9 s1).Holds s1 s2 at e2
  have m2 : s2.external = s.external := (e2.agrees.external (by simp [Component.Covers])).trans m1
  have v2r0 : ((Operand.reg 0 : Operand 64).read s2) = ((Operand.reg 9 : Operand 64).read s) := by
    have h : ((Operand.reg 0 : Operand 64).read s2) = ((Operand.reg 9 : Operand 64).read s1) := e2.writes
    rw [r1b9] at h
    exact h
  have r2b11 : ((Operand.reg 11 : Operand 64).read s2) = 18446744069414584321 := (e2.agrees.read (by simp)).trans (v1r11)
  have r2b0 : ((Operand.reg 0 : Operand 64).read s2) = ((Operand.reg 9 : Operand 64).read s) := v2r0
  obtain ⟨s3, a3, ready3, e3⟩ :=
    (mul_r64_effect_step 0x113c50 0x49 0xe3 (by simp [RexWPrefix]) (by decide) (by decide)).advances ready2 ((code 13 3).of_external_eq m2)
      e2.rip (next 0x13c53 (by decide))
  change (mulR64Effect 0x113c50 11 s2).Holds s2 s3 at e3
  have m3 : s3.external = s.external := (e3.agrees.external (by simp [Component.Covers])).trans m2
  have v3r0 : ((Operand.reg 0 : Operand 64).read s3) = v3 := by
    have h : ((Operand.reg 0 : Operand 64).read s3) = ((Operand.reg 0 : Operand 64).read s2) * ((Operand.reg 11 : Operand 64).read s2) := e3.writes.1
    rw [r2b11, r2b0] at h
    exact h
  have v3r2 : ((Operand.reg 2 : Operand 64).read s3) = h3 := by
    have h : ((Operand.reg 2 : Operand 64).read s3) = mulHigh64 ((Operand.reg 0 : Operand 64).read s2) ((Operand.reg 11 : Operand 64).read s2) := e3.writes.2
    rw [r2b11, r2b0] at h
    exact h
  have r3b2 : ((Operand.reg 2 : Operand 64).read s3) = h3 := v3r2
  obtain ⟨s4, a4, ready4, e4⟩ :=
    (mov_r64_r64_effect_step 0x113c53 0x49 0xd1 (by simp [RexWPrefix]) (by decide)).advances ready3 ((code 16 3).of_external_eq m3)
      e3.rip (next 0x13c56 (by decide))
  change (movR64R64Effect 0x113c53 9 2 s3).Holds s3 s4 at e4
  have m4 : s4.external = s.external := (e4.agrees.external (by simp [Component.Covers])).trans m3
  have v4r9 : ((Operand.reg 9 : Operand 64).read s4) = h3 := by
    have h : ((Operand.reg 9 : Operand 64).read s4) = ((Operand.reg 2 : Operand 64).read s3) := e4.writes
    rw [r3b2] at h
    exact h
  have r4b0 : ((Operand.reg 0 : Operand 64).read s4) = v3 := (e4.agrees.read (by simp)).trans (v3r0)
  obtain ⟨s5, a5, ready5, e5⟩ :=
    (mov_r64_r64_effect_step 0x113c56 0x49 0xc2 (by simp [RexWPrefix]) (by decide)).advances ready4 ((code 19 3).of_external_eq m4)
      e4.rip (next 0x13c59 (by decide))
  change (movR64R64Effect 0x113c56 10 0 s4).Holds s4 s5 at e5
  have m5 : s5.external = s.external := (e5.agrees.external (by simp [Component.Covers])).trans m4
  have v5r10 : ((Operand.reg 10 : Operand 64).read s5) = v3 := by
    have h : ((Operand.reg 10 : Operand 64).read s5) = ((Operand.reg 0 : Operand 64).read s4) := e5.writes
    rw [r4b0] at h
    exact h
  have r5b6 : ((Operand.reg 6 : Operand 64).read s5) = ((Operand.reg 6 : Operand 64).read s) := (e5.agrees.read (by simp)).trans ((e4.agrees.read (by simp)).trans ((e3.agrees.read (by simp)).trans ((e2.agrees.read (by simp)).trans ((e1.agrees.read (by simp)).trans (rfl)))))
  have mr6 : MemReadable s5 (((Operand.reg 6 : Operand 64).read s5) + 24) 8 := by
    rw [r5b6]
    exact pre.readable6.of_external_eq m5
  have mv6 : (Operand.mem (((Operand.reg 6 : Operand 64).read s5) + 24) : Operand 64).read s5 = ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 24) : Operand 64).read s) := by
    change memLoad _ _ 64 = memLoad _ _ 64
    rw [m5, r5b6]
  have r5b10 : ((Operand.reg 10 : Operand 64).read s5) = v3 := v5r10
  obtain ⟨s6, a6, ready6, e6⟩ :=
    (add_r64_m64_effect_step 0x113c59 0x4c (by simp [RexWPrefix]) 2 (.base 6 (.d8 24)) (by decide) rfl rfl).advances ready5 ((code 22 4).of_external_eq m5)
      ⟨e5.rip, mr6⟩ (next 0x13c5d (by decide))
  change (addR64M64Effect 0x113c59 10 (.base 6 (.d8 24)) s5).Holds s5 s6 at e6
  have m6 : s6.external = s.external := (e6.agrees.external (by simp [Component.Covers])).trans m5
  have v6r10 : ((Operand.reg 10 : Operand 64).read s6) = q6.1 := by
    have h : ((Operand.reg 10 : Operand 64).read s6) = (addSpec ((Operand.reg 10 : Operand 64).read s5) ((Operand.mem (((Operand.reg 6 : Operand 64).read s5) + 24) : Operand 64).read s5) ).1 := e6.writes
    rw [mv6, r5b10] at h
    exact h
  have c6 : (StatusFlags.ofRFLAGS s6.RFLAGS).CF = q6.2.CF := by
    have h : (StatusFlags.ofRFLAGS s6.RFLAGS).CF = (addSpec ((Operand.reg 10 : Operand 64).read s5) ((Operand.mem (((Operand.reg 6 : Operand 64).read s5) + 24) : Operand 64).read s5) ).2.CF := e6.flags.1
    rw [mv6, r5b10] at h
    exact h
  have r6b9 : ((Operand.reg 9 : Operand 64).read s6) = h3 := (e6.agrees.read (by simp)).trans ((e5.agrees.read (by simp)).trans (v4r9))
  have cf6in : (StatusFlags.ofRFLAGS s6.RFLAGS).CF = q6.2.CF := by
    exact c6
  obtain ⟨s7, a7, ready7, e7⟩ :=
    (adc_r64_imm8_effect_step 0x113c5d 0x49 0xd1 0 (by simp [RexWPrefix]) (by decide) (by decide)).advances ready6 ((code 26 4).of_external_eq m6)
      e6.rip (next 0x13c61 (by decide))
  change (adcR64Imm8Effect 0x113c5d 9 0 s6).Holds s6 s7 at e7
  have m7 : s7.external = s.external := (e7.agrees.external (by simp [Component.Covers])).trans m6
  have v7r9 : ((Operand.reg 9 : Operand 64).read s7) = q7.1 := by
    have h : ((Operand.reg 9 : Operand 64).read s7) = (adcSpec ((Operand.reg 9 : Operand 64).read s6) 0 (s6.RFLAGS.extractLsb' 0 1)).1 := e7.writes
    rw [r6b9, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf6in] at h
    exact h
  have c7 : (StatusFlags.ofRFLAGS s7.RFLAGS).CF = q7.2.CF := by
    have h : (StatusFlags.ofRFLAGS s7.RFLAGS).CF = (adcSpec ((Operand.reg 9 : Operand 64).read s6) 0 (s6.RFLAGS.extractLsb' 0 1)).2.CF := e7.flags.1
    rw [r6b9, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf6in] at h
    exact h
  have r7b6 : ((Operand.reg 6 : Operand 64).read s7) = ((Operand.reg 6 : Operand 64).read s) := (e7.agrees.read (by simp)).trans ((e6.agrees.read (by simp)).trans ((e5.agrees.read (by simp)).trans ((e4.agrees.read (by simp)).trans ((e3.agrees.read (by simp)).trans ((e2.agrees.read (by simp)).trans ((e1.agrees.read (by simp)).trans (rfl)))))))
  have mr8 : MemReadable s7 (((Operand.reg 6 : Operand 64).read s7) + 16) 8 := by
    rw [r7b6]
    exact pre.readable8.of_external_eq m7
  have mv8 : (Operand.mem (((Operand.reg 6 : Operand 64).read s7) + 16) : Operand 64).read s7 = ((Operand.mem (((Operand.reg 6 : Operand 64).read s) + 16) : Operand 64).read s) := by
    change memLoad _ _ 64 = memLoad _ _ 64
    rw [m7, r7b6]
  have r7b14 : ((Operand.reg 14 : Operand 64).read s7) = ((Operand.reg 14 : Operand 64).read s) := (e7.agrees.read (by simp)).trans ((e6.agrees.read (by simp)).trans ((e5.agrees.read (by simp)).trans ((e4.agrees.read (by simp)).trans ((e3.agrees.read (by simp)).trans ((e2.agrees.read (by simp)).trans ((e1.agrees.read (by simp)).trans (rfl)))))))
  obtain ⟨s8, a8, ready8, e8⟩ :=
    (add_r64_m64_effect_step 0x113c61 0x4c (by simp [RexWPrefix]) 6 (.base 6 (.d8 16)) (by decide) rfl rfl).advances ready7 ((code 30 4).of_external_eq m7)
      ⟨e7.rip, mr8⟩ (next 0x13c65 (by decide))
  change (addR64M64Effect 0x113c61 14 (.base 6 (.d8 16)) s7).Holds s7 s8 at e8
  have m8 : s8.external = s.external := (e8.agrees.external (by simp [Component.Covers])).trans m7
  have v8r14 : ((Operand.reg 14 : Operand 64).read s8) = q8.1 := by
    have h : ((Operand.reg 14 : Operand 64).read s8) = (addSpec ((Operand.reg 14 : Operand 64).read s7) ((Operand.mem (((Operand.reg 6 : Operand 64).read s7) + 16) : Operand 64).read s7) ).1 := e8.writes
    rw [mv8, r7b14] at h
    exact h
  have c8 : (StatusFlags.ofRFLAGS s8.RFLAGS).CF = q8.2.CF := by
    have h : (StatusFlags.ofRFLAGS s8.RFLAGS).CF = (addSpec ((Operand.reg 14 : Operand 64).read s7) ((Operand.mem (((Operand.reg 6 : Operand 64).read s7) + 16) : Operand 64).read s7) ).2.CF := e8.flags.1
    rw [mv8, r7b14] at h
    exact h
  have r8b10 : ((Operand.reg 10 : Operand 64).read s8) = q6.1 := (e8.agrees.read (by simp)).trans ((e7.agrees.read (by simp)).trans (v6r10))
  have cf8in : (StatusFlags.ofRFLAGS s8.RFLAGS).CF = q8.2.CF := by
    exact c8
  obtain ⟨s9, a9, ready9, e9⟩ :=
    (adc_r64_imm8_effect_step 0x113c65 0x49 0xd2 0 (by simp [RexWPrefix]) (by decide) (by decide)).advances ready8 ((code 34 4).of_external_eq m8)
      e8.rip (next 0x13c69 (by decide))
  change (adcR64Imm8Effect 0x113c65 10 0 s8).Holds s8 s9 at e9
  have m9 : s9.external = s.external := (e9.agrees.external (by simp [Component.Covers])).trans m8
  have v9r10 : ((Operand.reg 10 : Operand 64).read s9) = q9.1 := by
    have h : ((Operand.reg 10 : Operand 64).read s9) = (adcSpec ((Operand.reg 10 : Operand 64).read s8) 0 (s8.RFLAGS.extractLsb' 0 1)).1 := e9.writes
    rw [r8b10, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf8in] at h
    exact h
  have c9 : (StatusFlags.ofRFLAGS s9.RFLAGS).CF = q9.2.CF := by
    have h : (StatusFlags.ofRFLAGS s9.RFLAGS).CF = (adcSpec ((Operand.reg 10 : Operand 64).read s8) 0 (s8.RFLAGS.extractLsb' 0 1)).2.CF := e9.flags.1
    rw [r8b10, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf8in] at h
    exact h
  have r9b1 : ((Operand.reg 1 : Operand 64).read s9) = ((Operand.reg 1 : Operand 64).read s) := (e9.agrees.read (by simp)).trans ((e8.agrees.read (by simp)).trans ((e7.agrees.read (by simp)).trans ((e6.agrees.read (by simp)).trans ((e5.agrees.read (by simp)).trans ((e4.agrees.read (by simp)).trans ((e3.agrees.read (by simp)).trans ((e2.agrees.read (by simp)).trans ((e1.agrees.read (by simp)).trans (rfl)))))))))
  have mr10 : MemReadable s9 (((Operand.reg 1 : Operand 64).read s9) + 8) 8 := by
    rw [r9b1]
    exact pre.readable10.of_external_eq m9
  have mv10 : (Operand.mem (((Operand.reg 1 : Operand 64).read s9) + 8) : Operand 64).read s9 = ((Operand.mem (((Operand.reg 1 : Operand 64).read s) + 8) : Operand 64).read s) := by
    change memLoad _ _ 64 = memLoad _ _ 64
    rw [m9, r9b1]
  obtain ⟨s10, a10, ready10, e10⟩ :=
    (mov_r64_m64_effect_step 0x113c69 0x4c (by simp [RexWPrefix]) 4 (.base 1 (.d8 8)) (by decide) rfl rfl).advances ready9 ((code 38 4).of_external_eq m9)
      ⟨e9.rip, mr10⟩ (next 0x13c6d (by decide))
  change (movR64M64Effect 0x113c69 12 (.base 1 (.d8 8)) s9).Holds s9 s10 at e10
  have m10 : s10.external = s.external := (e10.agrees.external (by simp [Component.Covers])).trans m9
  have v10r12 : ((Operand.reg 12 : Operand 64).read s10) = ((Operand.mem (((Operand.reg 1 : Operand 64).read s) + 8) : Operand 64).read s) := by
    have h : ((Operand.reg 12 : Operand 64).read s10) = ((Operand.mem (((Operand.reg 1 : Operand 64).read s9) + 8) : Operand 64).read s9) := e10.writes
    rw [mv10] at h
    exact h
  have r10b9 : ((Operand.reg 9 : Operand 64).read s10) = q7.1 := (e10.agrees.read (by simp)).trans ((e9.agrees.read (by simp)).trans ((e8.agrees.read (by simp)).trans (v7r9)))
  have cf10in : (StatusFlags.ofRFLAGS s10.RFLAGS).CF = q9.2.CF := by
    rw [e10.agrees.rflags (by simp) (by simp)]
    exact c9
  obtain ⟨s11, a11, ready11, e11⟩ :=
    (adc_r64_imm8_effect_step 0x113c6d 0x49 0xd1 0 (by simp [RexWPrefix]) (by decide) (by decide)).advances ready10 ((code 42 4).of_external_eq m10)
      e10.rip (next 0x13c71 (by decide))
  change (adcR64Imm8Effect 0x113c6d 9 0 s10).Holds s10 s11 at e11
  have m11 : s11.external = s.external := (e11.agrees.external (by simp [Component.Covers])).trans m10
  have v11r9 : ((Operand.reg 9 : Operand 64).read s11) = q11.1 := by
    have h : ((Operand.reg 9 : Operand 64).read s11) = (adcSpec ((Operand.reg 9 : Operand 64).read s10) 0 (s10.RFLAGS.extractLsb' 0 1)).1 := e11.writes
    rw [r10b9, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf10in] at h
    exact h
  have c11 : (StatusFlags.ofRFLAGS s11.RFLAGS).CF = q11.2.CF := by
    have h : (StatusFlags.ofRFLAGS s11.RFLAGS).CF = (adcSpec ((Operand.reg 9 : Operand 64).read s10) 0 (s10.RFLAGS.extractLsb' 0 1)).2.CF := e11.flags.1
    rw [r10b9, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf10in] at h
    exact h
  have r11b0 : ((Operand.reg 0 : Operand 64).read s11) = v3 := (e11.agrees.read (by simp)).trans ((e10.agrees.read (by simp)).trans ((e9.agrees.read (by simp)).trans ((e8.agrees.read (by simp)).trans ((e7.agrees.read (by simp)).trans ((e6.agrees.read (by simp)).trans ((e5.agrees.read (by simp)).trans ((e4.agrees.read (by simp)).trans (v3r0))))))))
  have r11b2 : ((Operand.reg 2 : Operand 64).read s11) = h3 := (e11.agrees.read (by simp)).trans ((e10.agrees.read (by simp)).trans ((e9.agrees.read (by simp)).trans ((e8.agrees.read (by simp)).trans ((e7.agrees.read (by simp)).trans ((e6.agrees.read (by simp)).trans ((e5.agrees.read (by simp)).trans ((e4.agrees.read (by simp)).trans (v3r2))))))))
  have r11b9 : ((Operand.reg 9 : Operand 64).read s11) = q11.1 := v11r9
  have r11b10 : ((Operand.reg 10 : Operand 64).read s11) = q9.1 := (e11.agrees.read (by simp)).trans ((e10.agrees.read (by simp)).trans (v9r10))
  have r11b11 : ((Operand.reg 11 : Operand 64).read s11) = 18446744069414584321 := (e11.agrees.read (by simp)).trans ((e10.agrees.read (by simp)).trans ((e9.agrees.read (by simp)).trans ((e8.agrees.read (by simp)).trans ((e7.agrees.read (by simp)).trans ((e6.agrees.read (by simp)).trans ((e5.agrees.read (by simp)).trans ((e4.agrees.read (by simp)).trans ((e3.agrees.read (by simp)).trans ((e2.agrees.read (by simp)).trans (v1r11))))))))))
  have r11b12 : ((Operand.reg 12 : Operand 64).read s11) = ((Operand.mem (((Operand.reg 1 : Operand 64).read s) + 8) : Operand 64).read s) := (e11.agrees.read (by simp)).trans (v10r12)
  have r11b14 : ((Operand.reg 14 : Operand 64).read s11) = q8.1 := (e11.agrees.read (by simp)).trans ((e10.agrees.read (by simp)).trans ((e9.agrees.read (by simp)).trans (v8r14)))
  refine ⟨11, s11, ((((((((((a1).trans a2).trans a3).trans a4).trans a5).trans a6).trans a7).trans a8).trans a9).trans a10).trans a11, ready11, loaded.of_external_eq m11, e11.rip, ?_, ?_, ?_⟩
  · exact ⟨r11b0, r11b2, r11b9, r11b10, r11b11, r11b12, r11b14⟩
  · exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  · apply (((((((((((e1.agrees).trans e2.agrees).trans e3.agrees).trans e4.agrees).trans e5.agrees).trans e6.agrees).trans e7.agrees).trans e8.agrees).trans e9.agrees).trans e10.agrees).trans e11.agrees).mono
    simp only [movR64Imm64Effect_components, movR64R64Effect_components, mulR64Effect_components, addR64M64Effect_components, adcR64Imm8Effect_components, movR64M64Effect_components]
    simp [firstHighEffect, Effect.components]

theorem firstHigh_bytes :
    Extracted.textBytes.toListFrom 0x13c43 firstHighBytes.length = firstHighBytes := by
  decide +kernel

end P256.Proofs.Field.Montgomery.Reduction
