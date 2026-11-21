import P256.Proofs.Common.Field.Montgomery.Schoolbook.CarryCompose
import P256.Proofs.Common.Instructions.ShiftLeft.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import P256.Proofs.Program.Code
import P256.Proofs.Common.Instructions.MovzxByte
import P256.Proofs.Common.Instructions.Neg64

set_option autoImplicit false

open P256.Proofs.Common.Instructions (addR64M64Effect_components mulHigh64 mulR64Effect mulR64Effect_components mul_r64_effect_step)
open P256.Proofs.Common.Instructions.AddByte (addR8Imm8Effect)
open P256.Proofs.Common.Instructions.Carry (adcR64Imm8Effect adcR64Imm8Effect_components adcR64M64Effect adcR64M64Effect_components adcR64R64Effect adcR64R64Effect_components adcSpec adc_r64_imm8_effect_step adc_r64_m64_effect_step adc_r64_r64_effect_step)
open P256.Proofs.Common.Instructions.MovzxByte (movzxR32R8Effect movzx_r32_r8_rex_effect_step)
open P256.Proofs.Common.Instructions.Neg64 (negR64Effect)
open P256.Proofs.Common.Instructions.Setb (SupportedOpcode setccR8Effect setccR8Effect_components setcc_r8_effect_step)
open P256.Proofs.Common.Instructions.ShiftLeft (shlR64Effect shlR64Effect_components shl_r64_imm8_effect_step)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Field.Montgomery.Reduction

open P256.Spec.Program.Routines
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

attribute [local simp] movzxR32R8Effect addR8Imm8Effect negR64Effect

attribute [local simp] mulR64Effect_components adcR64R64Effect_components adcR64Imm8Effect_components
  adcR64M64Effect_components addR64M64Effect_components setccR8Effect_components shlR64Effect_components

structure FourthRoundPre (s : RamState) : Prop where
  rip : s.RIP = 0x113ce1
  readable9 : MemReadable s (((Operand.reg 1 : Operand 64).read s) + 24) 8

def fourthRoundBytes : List UInt8 :=
  [0x44, 0xf, 0xb6, 0xca, 0x4d, 0x89, 0xd4, 0x4d, 0x89, 0xd7, 0x49, 0xc1, 0xef, 0x20, 0x49, 0xc1, 0xe4, 0x20, 0x4c, 0x89, 0xd0, 0x49, 0xf7, 0xe3, 0x4c, 0x1, 0xee, 0x4c, 0x13, 0x49, 0x18, 0xf, 0x92, 0xc1, 0x48, 0x1, 0xc6, 0x48, 0x83, 0xd2, 0x0, 0x4d, 0x1, 0xf4, 0x4d, 0x11, 0xc7]

def fourthRoundEffect (s : RamState) : Effect :=
  let v1 := (((Operand.reg 2 : Operand 64).read s).setWidth 8).setWidth 64
  let v4 := ((Operand.reg 10 : Operand 64).read s) >>> 32
  let v5 := ((Operand.reg 10 : Operand 64).read s) <<< 32
  let v7 := ((Operand.reg 10 : Operand 64).read s) * ((Operand.reg 11 : Operand 64).read s)
  let h7 := mulHigh64 ((Operand.reg 10 : Operand 64).read s) ((Operand.reg 11 : Operand 64).read s)
  let q8 := addSpec ((Operand.reg 6 : Operand 64).read s) ((Operand.reg 13 : Operand 64).read s)
  let q9 := adcSpec v1 ((Operand.mem (((Operand.reg 1 : Operand 64).read s) + 24) : Operand 64).read s) (BitVec.ofBool q8.2.CF)
  let v10 := mergeGPR 8 (if q9.2.CF then 1 else 0) ((Operand.reg 1 : Operand 64).read s)
  let q11 := addSpec q8.1 v7
  let q12 := adcSpec h7 0 (BitVec.ofBool q11.2.CF)
  let q13 := addSpec v5 ((Operand.reg 14 : Operand 64).read s)
  let q14 := adcSpec v4 ((Operand.reg 8 : Operand 64).read s) (BitVec.ofBool q13.2.CF)
  { rip := 0x113d10
    writes := [⟨(.reg 0 : Operand 64), v7⟩,
      ⟨(.reg 1 : Operand 64), v10⟩,
      ⟨(.reg 2 : Operand 64), q12.1⟩,
      ⟨(.reg 6 : Operand 64), q11.1⟩,
      ⟨(.reg 9 : Operand 64), q9.1⟩,
      ⟨(.reg 12 : Operand 64), q13.1⟩,
      ⟨(.reg 15 : Operand 64), q14.1⟩]
    flags := some (.ofStatusFlags q14.2) }

theorem fourthRound_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary FourthRoundPre (codeRange 0x113ce1 fourthRoundBytes)
      (Effect.post fourthRoundEffect) := by
  intro s ready loaded pre
  have next (offset : Nat) (h : offset < 118431) :=
    boundary_ne_program hout (inProgram_of_textOffset offset h)
  have code (offset len : Nat) := loaded.mono (codeRange_slice_subset 0x113ce1 fourthRoundBytes offset len)
  let v1 := (((Operand.reg 2 : Operand 64).read s).setWidth 8).setWidth 64
  let v4 := ((Operand.reg 10 : Operand 64).read s) >>> 32
  let v5 := ((Operand.reg 10 : Operand 64).read s) <<< 32
  let v7 := ((Operand.reg 10 : Operand 64).read s) * ((Operand.reg 11 : Operand 64).read s)
  let h7 := mulHigh64 ((Operand.reg 10 : Operand 64).read s) ((Operand.reg 11 : Operand 64).read s)
  let q8 := addSpec ((Operand.reg 6 : Operand 64).read s) ((Operand.reg 13 : Operand 64).read s)
  let q9 := adcSpec v1 ((Operand.mem (((Operand.reg 1 : Operand 64).read s) + 24) : Operand 64).read s) (BitVec.ofBool q8.2.CF)
  let v10 := mergeGPR 8 (if q9.2.CF then 1 else 0) ((Operand.reg 1 : Operand 64).read s)
  let q11 := addSpec q8.1 v7
  let q12 := adcSpec h7 0 (BitVec.ofBool q11.2.CF)
  let q13 := addSpec v5 ((Operand.reg 14 : Operand 64).read s)
  let q14 := adcSpec v4 ((Operand.reg 8 : Operand 64).read s) (BitVec.ofBool q13.2.CF)
  obtain ⟨s1, a1, ready1, e1⟩ :=
    (movzx_r32_r8_rex_effect_step 0x113ce1 0x44 0xca (by simp [RexNoWPrefix]) (by decide)).advances ready (code 0 4)
      pre.rip (next 0x13ce5 (by decide))
  change (movzxR32R8Effect 0x113ce1 4 9 2 s).Holds s s1 at e1
  have m1 : s1.external = s.external := (e1.agrees.external (by simp [Component.Covers] <;> simp [Effect.components]))
  have v1r9 : ((Operand.reg 9 : Operand 64).read s1) = v1 := by
    have h : ((Operand.reg 9 : Operand 64).read s1) = (((Operand.reg 2 : Operand 64).read s).setWidth 8).setWidth 64 := e1.writes
    exact h
  have r1b10 : ((Operand.reg 10 : Operand 64).read s1) = ((Operand.reg 10 : Operand 64).read s) := (e1.agrees.read (by simp <;> simp [Effect.components])).trans (rfl)
  obtain ⟨s2, a2, ready2, e2⟩ :=
    (mov_r64_r64_effect_step 0x113ce5 0x4d 0xd4 (by simp [RexWPrefix]) (by decide)).advances ready1 ((code 4 3).of_external_eq m1)
      e1.rip (next 0x13ce8 (by decide))
  change (movR64R64Effect 0x113ce5 12 10 s1).Holds s1 s2 at e2
  have m2 : s2.external = s.external := (e2.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])).trans m1
  have v2r12 : ((Operand.reg 12 : Operand 64).read s2) = ((Operand.reg 10 : Operand 64).read s) := by
    have h : ((Operand.reg 12 : Operand 64).read s2) = ((Operand.reg 10 : Operand 64).read s1) := e2.writes
    rw [r1b10] at h
    exact h
  have r2b10 : ((Operand.reg 10 : Operand 64).read s2) = ((Operand.reg 10 : Operand 64).read s) := (e2.agrees.read (by simp <;> simp [Effect.components])).trans ((e1.agrees.read (by simp <;> simp [Effect.components])).trans (rfl))
  obtain ⟨s3, a3, ready3, e3⟩ :=
    (mov_r64_r64_effect_step 0x113ce8 0x4d 0xd7 (by simp [RexWPrefix]) (by decide)).advances ready2 ((code 7 3).of_external_eq m2)
      e2.rip (next 0x13ceb (by decide))
  change (movR64R64Effect 0x113ce8 15 10 s2).Holds s2 s3 at e3
  have m3 : s3.external = s.external := (e3.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])).trans m2
  have v3r15 : ((Operand.reg 15 : Operand 64).read s3) = ((Operand.reg 10 : Operand 64).read s) := by
    have h : ((Operand.reg 15 : Operand 64).read s3) = ((Operand.reg 10 : Operand 64).read s2) := e3.writes
    rw [r2b10] at h
    exact h
  have r3b15 : ((Operand.reg 15 : Operand 64).read s3) = ((Operand.reg 10 : Operand 64).read s) := v3r15
  obtain ⟨s4, a4, ready4, e4⟩ :=
    (shr_r64_imm8_effect_step 0x113ceb 0x49 0xef 32 (by simp [RexWPrefix]) (by decide) (by decide)).advances ready3 ((code 10 4).of_external_eq m3)
      e3.rip (next 0x13cef (by decide))
  change (shrR64Effect 0x113ceb 4 15 32 s3).Holds s3 s4 at e4
  have m4 : s4.external = s.external := (e4.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])).trans m3
  have v4r15 : ((Operand.reg 15 : Operand 64).read s4) = v4 := by
    have h : ((Operand.reg 15 : Operand 64).read s4) = ((Operand.reg 15 : Operand 64).read s3) >>> 32 := e4.writes
    rw [r3b15] at h
    exact h
  have r4b12 : ((Operand.reg 12 : Operand 64).read s4) = ((Operand.reg 10 : Operand 64).read s) := (e4.agrees.read (by simp <;> simp [Effect.components])).trans ((e3.agrees.read (by simp <;> simp [Effect.components])).trans (v2r12))
  obtain ⟨s5, a5, ready5, e5⟩ :=
    (shl_r64_imm8_effect_step 0x113cef 0x49 0xe4 32 (by simp [RexWPrefix]) (by decide) (by decide)).advances ready4 ((code 14 4).of_external_eq m4)
      e4.rip (next 0x13cf3 (by decide))
  change (shlR64Effect 0x113cef 4 12 32 s4).Holds s4 s5 at e5
  have m5 : s5.external = s.external := (e5.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])).trans m4
  have v5r12 : ((Operand.reg 12 : Operand 64).read s5) = v5 := by
    have h : ((Operand.reg 12 : Operand 64).read s5) = ((Operand.reg 12 : Operand 64).read s4) <<< 32 := e5.writes
    rw [r4b12] at h
    exact h
  have r5b10 : ((Operand.reg 10 : Operand 64).read s5) = ((Operand.reg 10 : Operand 64).read s) := (e5.agrees.read (by simp <;> simp [Effect.components])).trans ((e4.agrees.read (by simp <;> simp [Effect.components])).trans ((e3.agrees.read (by simp <;> simp [Effect.components])).trans ((e2.agrees.read (by simp <;> simp [Effect.components])).trans ((e1.agrees.read (by simp <;> simp [Effect.components])).trans (rfl)))))
  obtain ⟨s6, a6, ready6, e6⟩ :=
    (mov_r64_r64_effect_step 0x113cf3 0x4c 0xd0 (by simp [RexWPrefix]) (by decide)).advances ready5 ((code 18 3).of_external_eq m5)
      e5.rip (next 0x13cf6 (by decide))
  change (movR64R64Effect 0x113cf3 0 10 s5).Holds s5 s6 at e6
  have m6 : s6.external = s.external := (e6.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])).trans m5
  have v6r0 : ((Operand.reg 0 : Operand 64).read s6) = ((Operand.reg 10 : Operand 64).read s) := by
    have h : ((Operand.reg 0 : Operand 64).read s6) = ((Operand.reg 10 : Operand 64).read s5) := e6.writes
    rw [r5b10] at h
    exact h
  have r6b11 : ((Operand.reg 11 : Operand 64).read s6) = ((Operand.reg 11 : Operand 64).read s) := (e6.agrees.read (by simp <;> simp [Effect.components])).trans ((e5.agrees.read (by simp <;> simp [Effect.components])).trans ((e4.agrees.read (by simp <;> simp [Effect.components])).trans ((e3.agrees.read (by simp <;> simp [Effect.components])).trans ((e2.agrees.read (by simp <;> simp [Effect.components])).trans ((e1.agrees.read (by simp <;> simp [Effect.components])).trans (rfl))))))
  have r6b0 : ((Operand.reg 0 : Operand 64).read s6) = ((Operand.reg 10 : Operand 64).read s) := v6r0
  obtain ⟨s7, a7, ready7, e7⟩ :=
    (mul_r64_effect_step 0x113cf6 0x49 0xe3 (by simp [RexWPrefix]) (by decide) (by decide)).advances ready6 ((code 21 3).of_external_eq m6)
      e6.rip (next 0x13cf9 (by decide))
  change (mulR64Effect 0x113cf6 11 s6).Holds s6 s7 at e7
  have m7 : s7.external = s.external := (e7.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])).trans m6
  have v7r0 : ((Operand.reg 0 : Operand 64).read s7) = v7 := by
    have h : ((Operand.reg 0 : Operand 64).read s7) = ((Operand.reg 0 : Operand 64).read s6) * ((Operand.reg 11 : Operand 64).read s6) := e7.writes.1
    rw [r6b11, r6b0] at h
    exact h
  have v7r2 : ((Operand.reg 2 : Operand 64).read s7) = h7 := by
    have h : ((Operand.reg 2 : Operand 64).read s7) = mulHigh64 ((Operand.reg 0 : Operand 64).read s6) ((Operand.reg 11 : Operand 64).read s6) := e7.writes.2
    rw [r6b11, r6b0] at h
    exact h
  have r7b13 : ((Operand.reg 13 : Operand 64).read s7) = ((Operand.reg 13 : Operand 64).read s) := (e7.agrees.read (by simp <;> simp [Effect.components])).trans ((e6.agrees.read (by simp <;> simp [Effect.components])).trans ((e5.agrees.read (by simp <;> simp [Effect.components])).trans ((e4.agrees.read (by simp <;> simp [Effect.components])).trans ((e3.agrees.read (by simp <;> simp [Effect.components])).trans ((e2.agrees.read (by simp <;> simp [Effect.components])).trans ((e1.agrees.read (by simp <;> simp [Effect.components])).trans (rfl)))))))
  have r7b6 : ((Operand.reg 6 : Operand 64).read s7) = ((Operand.reg 6 : Operand 64).read s) := (e7.agrees.read (by simp <;> simp [Effect.components])).trans ((e6.agrees.read (by simp <;> simp [Effect.components])).trans ((e5.agrees.read (by simp <;> simp [Effect.components])).trans ((e4.agrees.read (by simp <;> simp [Effect.components])).trans ((e3.agrees.read (by simp <;> simp [Effect.components])).trans ((e2.agrees.read (by simp <;> simp [Effect.components])).trans ((e1.agrees.read (by simp <;> simp [Effect.components])).trans (rfl)))))))
  obtain ⟨s8, a8, ready8, e8⟩ :=
    (add_r64_r64_effect_step 0x113cf9 0x4c 0xee (by simp [RexWPrefix]) (by decide)).advances ready7 ((code 24 3).of_external_eq m7)
      e7.rip (next 0x13cfc (by decide))
  change (addR64R64Effect 0x113cf9 6 13 s7).Holds s7 s8 at e8
  have m8 : s8.external = s.external := (e8.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])).trans m7
  have v8r6 : ((Operand.reg 6 : Operand 64).read s8) = q8.1 := by
    have h : ((Operand.reg 6 : Operand 64).read s8) = (addSpec ((Operand.reg 6 : Operand 64).read s7) ((Operand.reg 13 : Operand 64).read s7) ).1 := e8.writes
    rw [r7b13, r7b6] at h
    exact h
  have c8 : (StatusFlags.ofRFLAGS s8.RFLAGS).CF = q8.2.CF := by
    have h : (StatusFlags.ofRFLAGS s8.RFLAGS).CF = (addSpec ((Operand.reg 6 : Operand 64).read s7) ((Operand.reg 13 : Operand 64).read s7) ).2.CF := e8.flags.1
    rw [r7b13, r7b6] at h
    exact h
  have r8b1 : ((Operand.reg 1 : Operand 64).read s8) = ((Operand.reg 1 : Operand 64).read s) := (e8.agrees.read (by simp <;> simp [Effect.components])).trans ((e7.agrees.read (by simp <;> simp [Effect.components])).trans ((e6.agrees.read (by simp <;> simp [Effect.components])).trans ((e5.agrees.read (by simp <;> simp [Effect.components])).trans ((e4.agrees.read (by simp <;> simp [Effect.components])).trans ((e3.agrees.read (by simp <;> simp [Effect.components])).trans ((e2.agrees.read (by simp <;> simp [Effect.components])).trans ((e1.agrees.read (by simp <;> simp [Effect.components])).trans (rfl))))))))
  have mr9 : MemReadable s8 (((Operand.reg 1 : Operand 64).read s8) + 24) 8 := by
    rw [r8b1]
    exact pre.readable9.of_external_eq m8
  have mv9 : (Operand.mem (((Operand.reg 1 : Operand 64).read s8) + 24) : Operand 64).read s8 = ((Operand.mem (((Operand.reg 1 : Operand 64).read s) + 24) : Operand 64).read s) := by
    change memLoad _ _ 64 = memLoad _ _ 64
    rw [m8, r8b1]
  have r8b9 : ((Operand.reg 9 : Operand 64).read s8) = v1 := (e8.agrees.read (by simp <;> simp [Effect.components])).trans ((e7.agrees.read (by simp <;> simp [Effect.components])).trans ((e6.agrees.read (by simp <;> simp [Effect.components])).trans ((e5.agrees.read (by simp <;> simp [Effect.components])).trans ((e4.agrees.read (by simp <;> simp [Effect.components])).trans ((e3.agrees.read (by simp <;> simp [Effect.components])).trans ((e2.agrees.read (by simp <;> simp [Effect.components])).trans (v1r9)))))))
  have cf8in : (StatusFlags.ofRFLAGS s8.RFLAGS).CF = q8.2.CF := by
    exact c8
  obtain ⟨s9, a9, ready9, e9⟩ :=
    (adc_r64_m64_effect_step 0x113cfc 0x4c (by simp [RexWPrefix]) 1 (.base 1 (.d8 24)) (by decide) rfl rfl).advances ready8 ((code 27 4).of_external_eq m8)
      ⟨e8.rip, mr9⟩ (next 0x13d00 (by decide))
  change (adcR64M64Effect 0x113cfc 9 (.base 1 (.d8 24)) s8).Holds s8 s9 at e9
  have m9 : s9.external = s.external := (e9.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])).trans m8
  have v9r9 : ((Operand.reg 9 : Operand 64).read s9) = q9.1 := by
    have h : ((Operand.reg 9 : Operand 64).read s9) = (adcSpec ((Operand.reg 9 : Operand 64).read s8) ((Operand.mem (((Operand.reg 1 : Operand 64).read s8) + 24) : Operand 64).read s8) (s8.RFLAGS.extractLsb' 0 1)).1 := e9.writes
    rw [mv9, r8b9, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf8in] at h
    exact h
  have c9 : (StatusFlags.ofRFLAGS s9.RFLAGS).CF = q9.2.CF := by
    have h : (StatusFlags.ofRFLAGS s9.RFLAGS).CF = (adcSpec ((Operand.reg 9 : Operand 64).read s8) ((Operand.mem (((Operand.reg 1 : Operand 64).read s8) + 24) : Operand 64).read s8) (s8.RFLAGS.extractLsb' 0 1)).2.CF := e9.flags.1
    rw [mv9, r8b9, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf8in] at h
    exact h
  have r9b1 : ((Operand.reg 1 : Operand 64).read s9) = ((Operand.reg 1 : Operand 64).read s) := (e9.agrees.read (by simp <;> simp [Effect.components])).trans ((e8.agrees.read (by simp <;> simp [Effect.components])).trans ((e7.agrees.read (by simp <;> simp [Effect.components])).trans ((e6.agrees.read (by simp <;> simp [Effect.components])).trans ((e5.agrees.read (by simp <;> simp [Effect.components])).trans ((e4.agrees.read (by simp <;> simp [Effect.components])).trans ((e3.agrees.read (by simp <;> simp [Effect.components])).trans ((e2.agrees.read (by simp <;> simp [Effect.components])).trans ((e1.agrees.read (by simp <;> simp [Effect.components])).trans (rfl)))))))))
  have cf9in : (StatusFlags.ofRFLAGS s9.RFLAGS).CF = q9.2.CF := by
    exact c9
  obtain ⟨s10, a10, ready10, e10⟩ :=
    (setcc_r8_effect_step 0x113d00 0x92 0xc1 (by simp [SupportedOpcode]) (by decide) (by decide)).advances ready9 ((code 31 3).of_external_eq m9)
      e9.rip (next 0x13d03 (by decide))
  change (setccR8Effect 0x113d00 3 1 2 s9).Holds s9 s10 at e10
  have m10 : s10.external = s.external := (e10.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])).trans m9
  have v10r1 : ((Operand.reg 1 : Operand 64).read s10) = v10 := by
    have h : ((Operand.reg 1 : Operand 64).read s10) = mergeGPR 8 (if (StatusFlags.ofRFLAGS s9.RFLAGS).CF then 1 else 0) ((Operand.reg 1 : Operand 64).read s9) := e10.writes
    rw [r9b1, cf9in] at h
    exact h
  have r10b0 : ((Operand.reg 0 : Operand 64).read s10) = v7 := (e10.agrees.read (by simp <;> simp [Effect.components])).trans ((e9.agrees.read (by simp <;> simp [Effect.components])).trans ((e8.agrees.read (by simp <;> simp [Effect.components])).trans (v7r0)))
  have r10b6 : ((Operand.reg 6 : Operand 64).read s10) = q8.1 := (e10.agrees.read (by simp <;> simp [Effect.components])).trans ((e9.agrees.read (by simp <;> simp [Effect.components])).trans (v8r6))
  obtain ⟨s11, a11, ready11, e11⟩ :=
    (add_r64_r64_effect_step 0x113d03 0x48 0xc6 (by simp [RexWPrefix]) (by decide)).advances ready10 ((code 34 3).of_external_eq m10)
      e10.rip (next 0x13d06 (by decide))
  change (addR64R64Effect 0x113d03 6 0 s10).Holds s10 s11 at e11
  have m11 : s11.external = s.external := (e11.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])).trans m10
  have v11r6 : ((Operand.reg 6 : Operand 64).read s11) = q11.1 := by
    have h : ((Operand.reg 6 : Operand 64).read s11) = (addSpec ((Operand.reg 6 : Operand 64).read s10) ((Operand.reg 0 : Operand 64).read s10) ).1 := e11.writes
    rw [r10b0, r10b6] at h
    exact h
  have c11 : (StatusFlags.ofRFLAGS s11.RFLAGS).CF = q11.2.CF := by
    have h : (StatusFlags.ofRFLAGS s11.RFLAGS).CF = (addSpec ((Operand.reg 6 : Operand 64).read s10) ((Operand.reg 0 : Operand 64).read s10) ).2.CF := e11.flags.1
    rw [r10b0, r10b6] at h
    exact h
  have r11b2 : ((Operand.reg 2 : Operand 64).read s11) = h7 := (e11.agrees.read (by simp <;> simp [Effect.components])).trans ((e10.agrees.read (by simp <;> simp [Effect.components])).trans ((e9.agrees.read (by simp <;> simp [Effect.components])).trans ((e8.agrees.read (by simp <;> simp [Effect.components])).trans (v7r2))))
  have cf11in : (StatusFlags.ofRFLAGS s11.RFLAGS).CF = q11.2.CF := by
    exact c11
  obtain ⟨s12, a12, ready12, e12⟩ :=
    (adc_r64_imm8_effect_step 0x113d06 0x48 0xd2 0 (by simp [RexWPrefix]) (by decide) (by decide)).advances ready11 ((code 37 4).of_external_eq m11)
      e11.rip (next 0x13d0a (by decide))
  change (adcR64Imm8Effect 0x113d06 2 0 s11).Holds s11 s12 at e12
  have m12 : s12.external = s.external := (e12.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])).trans m11
  have v12r2 : ((Operand.reg 2 : Operand 64).read s12) = q12.1 := by
    have h : ((Operand.reg 2 : Operand 64).read s12) = (adcSpec ((Operand.reg 2 : Operand 64).read s11) 0 (s11.RFLAGS.extractLsb' 0 1)).1 := e12.writes
    rw [r11b2, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf11in] at h
    exact h
  have c12 : (StatusFlags.ofRFLAGS s12.RFLAGS).CF = q12.2.CF := by
    have h : (StatusFlags.ofRFLAGS s12.RFLAGS).CF = (adcSpec ((Operand.reg 2 : Operand 64).read s11) 0 (s11.RFLAGS.extractLsb' 0 1)).2.CF := e12.flags.1
    rw [r11b2, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf11in] at h
    exact h
  have r12b14 : ((Operand.reg 14 : Operand 64).read s12) = ((Operand.reg 14 : Operand 64).read s) := (e12.agrees.read (by simp <;> simp [Effect.components])).trans ((e11.agrees.read (by simp <;> simp [Effect.components])).trans ((e10.agrees.read (by simp <;> simp [Effect.components])).trans ((e9.agrees.read (by simp <;> simp [Effect.components])).trans ((e8.agrees.read (by simp <;> simp [Effect.components])).trans ((e7.agrees.read (by simp <;> simp [Effect.components])).trans ((e6.agrees.read (by simp <;> simp [Effect.components])).trans ((e5.agrees.read (by simp <;> simp [Effect.components])).trans ((e4.agrees.read (by simp <;> simp [Effect.components])).trans ((e3.agrees.read (by simp <;> simp [Effect.components])).trans ((e2.agrees.read (by simp <;> simp [Effect.components])).trans ((e1.agrees.read (by simp <;> simp [Effect.components])).trans (rfl))))))))))))
  have r12b12 : ((Operand.reg 12 : Operand 64).read s12) = v5 := (e12.agrees.read (by simp <;> simp [Effect.components])).trans ((e11.agrees.read (by simp <;> simp [Effect.components])).trans ((e10.agrees.read (by simp <;> simp [Effect.components])).trans ((e9.agrees.read (by simp <;> simp [Effect.components])).trans ((e8.agrees.read (by simp <;> simp [Effect.components])).trans ((e7.agrees.read (by simp <;> simp [Effect.components])).trans ((e6.agrees.read (by simp <;> simp [Effect.components])).trans (v5r12)))))))
  obtain ⟨s13, a13, ready13, e13⟩ :=
    (add_r64_r64_effect_step 0x113d0a 0x4d 0xf4 (by simp [RexWPrefix]) (by decide)).advances ready12 ((code 41 3).of_external_eq m12)
      e12.rip (next 0x13d0d (by decide))
  change (addR64R64Effect 0x113d0a 12 14 s12).Holds s12 s13 at e13
  have m13 : s13.external = s.external := (e13.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])).trans m12
  have v13r12 : ((Operand.reg 12 : Operand 64).read s13) = q13.1 := by
    have h : ((Operand.reg 12 : Operand 64).read s13) = (addSpec ((Operand.reg 12 : Operand 64).read s12) ((Operand.reg 14 : Operand 64).read s12) ).1 := e13.writes
    rw [r12b14, r12b12] at h
    exact h
  have c13 : (StatusFlags.ofRFLAGS s13.RFLAGS).CF = q13.2.CF := by
    have h : (StatusFlags.ofRFLAGS s13.RFLAGS).CF = (addSpec ((Operand.reg 12 : Operand 64).read s12) ((Operand.reg 14 : Operand 64).read s12) ).2.CF := e13.flags.1
    rw [r12b14, r12b12] at h
    exact h
  have r13b8 : ((Operand.reg 8 : Operand 64).read s13) = ((Operand.reg 8 : Operand 64).read s) := (e13.agrees.read (by simp <;> simp [Effect.components])).trans ((e12.agrees.read (by simp <;> simp [Effect.components])).trans ((e11.agrees.read (by simp <;> simp [Effect.components])).trans ((e10.agrees.read (by simp <;> simp [Effect.components])).trans ((e9.agrees.read (by simp <;> simp [Effect.components])).trans ((e8.agrees.read (by simp <;> simp [Effect.components])).trans ((e7.agrees.read (by simp <;> simp [Effect.components])).trans ((e6.agrees.read (by simp <;> simp [Effect.components])).trans ((e5.agrees.read (by simp <;> simp [Effect.components])).trans ((e4.agrees.read (by simp <;> simp [Effect.components])).trans ((e3.agrees.read (by simp <;> simp [Effect.components])).trans ((e2.agrees.read (by simp <;> simp [Effect.components])).trans ((e1.agrees.read (by simp <;> simp [Effect.components])).trans (rfl)))))))))))))
  have r13b15 : ((Operand.reg 15 : Operand 64).read s13) = v4 := (e13.agrees.read (by simp <;> simp [Effect.components])).trans ((e12.agrees.read (by simp <;> simp [Effect.components])).trans ((e11.agrees.read (by simp <;> simp [Effect.components])).trans ((e10.agrees.read (by simp <;> simp [Effect.components])).trans ((e9.agrees.read (by simp <;> simp [Effect.components])).trans ((e8.agrees.read (by simp <;> simp [Effect.components])).trans ((e7.agrees.read (by simp <;> simp [Effect.components])).trans ((e6.agrees.read (by simp <;> simp [Effect.components])).trans ((e5.agrees.read (by simp <;> simp [Effect.components])).trans (v4r15)))))))))
  have cf13in : (StatusFlags.ofRFLAGS s13.RFLAGS).CF = q13.2.CF := by
    exact c13
  obtain ⟨s14, a14, ready14, e14⟩ :=
    (adc_r64_r64_effect_step 0x113d0d 0x4d 0xc7 (by simp [RexWPrefix]) (by decide)).advances ready13 ((code 44 3).of_external_eq m13)
      e13.rip (next 0x13d10 (by decide))
  change (adcR64R64Effect 0x113d0d 15 8 s13).Holds s13 s14 at e14
  have m14 : s14.external = s.external := (e14.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])).trans m13
  have v14r15 : ((Operand.reg 15 : Operand 64).read s14) = q14.1 := by
    have h : ((Operand.reg 15 : Operand 64).read s14) = (adcSpec ((Operand.reg 15 : Operand 64).read s13) ((Operand.reg 8 : Operand 64).read s13) (s13.RFLAGS.extractLsb' 0 1)).1 := e14.writes
    rw [r13b8, r13b15, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf13in] at h
    exact h
  have c14 : (StatusFlags.ofRFLAGS s14.RFLAGS).CF = q14.2.CF := by
    have h : (StatusFlags.ofRFLAGS s14.RFLAGS).CF = (adcSpec ((Operand.reg 15 : Operand 64).read s13) ((Operand.reg 8 : Operand 64).read s13) (s13.RFLAGS.extractLsb' 0 1)).2.CF := e14.flags.1
    rw [r13b8, r13b15, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf13in] at h
    exact h
  have flags14 : (StatusFlagsOutcome.ofStatusFlags q14.2).Allows (StatusFlags.ofRFLAGS s14.RFLAGS) := by
    have h : (StatusFlagsOutcome.ofStatusFlags (adcSpec ((Operand.reg 15 : Operand 64).read s13) ((Operand.reg 8 : Operand 64).read s13) (s13.RFLAGS.extractLsb' 0 1)).2).Allows _ := e14.flags
    rw [r13b8, r13b15, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf13in] at h
    exact h
  have r14b0 : ((Operand.reg 0 : Operand 64).read s14) = v7 := (e14.agrees.read (by simp <;> simp [Effect.components])).trans ((e13.agrees.read (by simp <;> simp [Effect.components])).trans ((e12.agrees.read (by simp <;> simp [Effect.components])).trans ((e11.agrees.read (by simp <;> simp [Effect.components])).trans ((e10.agrees.read (by simp <;> simp [Effect.components])).trans ((e9.agrees.read (by simp <;> simp [Effect.components])).trans ((e8.agrees.read (by simp <;> simp [Effect.components])).trans (v7r0)))))))
  have r14b1 : ((Operand.reg 1 : Operand 64).read s14) = v10 := (e14.agrees.read (by simp <;> simp [Effect.components])).trans ((e13.agrees.read (by simp <;> simp [Effect.components])).trans ((e12.agrees.read (by simp <;> simp [Effect.components])).trans ((e11.agrees.read (by simp <;> simp [Effect.components])).trans (v10r1))))
  have r14b2 : ((Operand.reg 2 : Operand 64).read s14) = q12.1 := (e14.agrees.read (by simp <;> simp [Effect.components])).trans ((e13.agrees.read (by simp <;> simp [Effect.components])).trans (v12r2))
  have r14b6 : ((Operand.reg 6 : Operand 64).read s14) = q11.1 := (e14.agrees.read (by simp <;> simp [Effect.components])).trans ((e13.agrees.read (by simp <;> simp [Effect.components])).trans ((e12.agrees.read (by simp <;> simp [Effect.components])).trans (v11r6)))
  have r14b9 : ((Operand.reg 9 : Operand 64).read s14) = q9.1 := (e14.agrees.read (by simp <;> simp [Effect.components])).trans ((e13.agrees.read (by simp <;> simp [Effect.components])).trans ((e12.agrees.read (by simp <;> simp [Effect.components])).trans ((e11.agrees.read (by simp <;> simp [Effect.components])).trans ((e10.agrees.read (by simp <;> simp [Effect.components])).trans (v9r9)))))
  have r14b12 : ((Operand.reg 12 : Operand 64).read s14) = q13.1 := (e14.agrees.read (by simp <;> simp [Effect.components])).trans (v13r12)
  have r14b15 : ((Operand.reg 15 : Operand 64).read s14) = q14.1 := v14r15
  refine ⟨14, s14, (((((((((((((a1).trans a2).trans a3).trans a4).trans a5).trans a6).trans a7).trans a8).trans a9).trans a10).trans a11).trans a12).trans a13).trans a14, ready14, loaded.of_external_eq m14, e14.rip, ?_, ?_, ?_⟩
  · exact ⟨r14b0, r14b1, r14b2, r14b6, r14b9, r14b12, r14b15⟩
  · exact flags14
  · apply ((((((((((((((e1.agrees).trans e2.agrees).trans e3.agrees).trans e4.agrees).trans e5.agrees).trans e6.agrees).trans e7.agrees).trans e8.agrees).trans e9.agrees).trans e10.agrees).trans e11.agrees).trans e12.agrees).trans e13.agrees).trans e14.agrees).mono
    simp only [movR64R64Effect_components, shrR64Effect_components, shlR64Effect_components, mulR64Effect_components, addR64R64Effect_components, adcR64M64Effect_components, setccR8Effect_components, adcR64Imm8Effect_components, adcR64R64Effect_components]
    simp [fourthRoundEffect, Effect.components]

theorem fourthRound_bytes :
    Extracted.textBytes.toListFrom 0x13ce1 fourthRoundBytes.length = fourthRoundBytes := by
  decide +kernel

end P256.Proofs.Field.Montgomery.Reduction
