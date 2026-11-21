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

structure ThirdRoundPre (s : RamState) : Prop where
  rip : s.RIP = 0x113ca7
  readable10 : MemReadable s (((Operand.reg 1 : Operand 64).read s) + 16) 8

def thirdRoundBytes : List UInt8 :=
  [0x44, 0xf, 0xb6, 0xea, 0x49, 0x89, 0xf2, 0x49, 0x89, 0xf6, 0x49, 0xc1, 0xee, 0x20, 0x49, 0xc1, 0xe2, 0x20, 0x48, 0x89, 0xf0, 0x49, 0xf7, 0xe3, 0x48, 0x89, 0xd6, 0x4d, 0x1, 0xe0, 0x4c, 0x13, 0x69, 0x10, 0xf, 0x92, 0xc2, 0x49, 0x1, 0xc0, 0x48, 0x83, 0xd6, 0x0, 0x4d, 0x1, 0xfa, 0x4d, 0x11, 0xce, 0x49, 0x83, 0xd0, 0x0, 0x48, 0x83, 0xd6, 0x0]

def thirdRoundEffect (s : RamState) : Effect :=
  let v1 := (((Operand.reg 2 : Operand 64).read s).setWidth 8).setWidth 64
  let v4 := ((Operand.reg 6 : Operand 64).read s) >>> 32
  let v5 := ((Operand.reg 6 : Operand 64).read s) <<< 32
  let v7 := ((Operand.reg 6 : Operand 64).read s) * ((Operand.reg 11 : Operand 64).read s)
  let h7 := mulHigh64 ((Operand.reg 6 : Operand 64).read s) ((Operand.reg 11 : Operand 64).read s)
  let q9 := addSpec ((Operand.reg 8 : Operand 64).read s) ((Operand.reg 12 : Operand 64).read s)
  let q10 := adcSpec v1 ((Operand.mem (((Operand.reg 1 : Operand 64).read s) + 16) : Operand 64).read s) (BitVec.ofBool q9.2.CF)
  let v11 := mergeGPR 8 (if q10.2.CF then 1 else 0) h7
  let q12 := addSpec q9.1 v7
  let q13 := adcSpec h7 0 (BitVec.ofBool q12.2.CF)
  let q14 := addSpec v5 ((Operand.reg 15 : Operand 64).read s)
  let q15 := adcSpec v4 ((Operand.reg 9 : Operand 64).read s) (BitVec.ofBool q14.2.CF)
  let q16 := adcSpec q12.1 0 (BitVec.ofBool q15.2.CF)
  let q17 := adcSpec q13.1 0 (BitVec.ofBool q16.2.CF)
  { rip := 0x113ce1
    writes := [⟨(.reg 0 : Operand 64), v7⟩,
      ⟨(.reg 2 : Operand 64), v11⟩,
      ⟨(.reg 6 : Operand 64), q17.1⟩,
      ⟨(.reg 8 : Operand 64), q16.1⟩,
      ⟨(.reg 10 : Operand 64), q14.1⟩,
      ⟨(.reg 13 : Operand 64), q10.1⟩,
      ⟨(.reg 14 : Operand 64), q15.1⟩]
    flags := some (.ofStatusFlags q17.2) }

theorem thirdRound_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary ThirdRoundPre (codeRange 0x113ca7 thirdRoundBytes)
      (Effect.post thirdRoundEffect) := by
  intro s ready loaded pre
  have next (offset : Nat) (h : offset < 118431) :=
    boundary_ne_program hout (inProgram_of_textOffset offset h)
  have code (offset len : Nat) := loaded.mono (codeRange_slice_subset 0x113ca7 thirdRoundBytes offset len)
  let v1 := (((Operand.reg 2 : Operand 64).read s).setWidth 8).setWidth 64
  let v4 := ((Operand.reg 6 : Operand 64).read s) >>> 32
  let v5 := ((Operand.reg 6 : Operand 64).read s) <<< 32
  let v7 := ((Operand.reg 6 : Operand 64).read s) * ((Operand.reg 11 : Operand 64).read s)
  let h7 := mulHigh64 ((Operand.reg 6 : Operand 64).read s) ((Operand.reg 11 : Operand 64).read s)
  let q9 := addSpec ((Operand.reg 8 : Operand 64).read s) ((Operand.reg 12 : Operand 64).read s)
  let q10 := adcSpec v1 ((Operand.mem (((Operand.reg 1 : Operand 64).read s) + 16) : Operand 64).read s) (BitVec.ofBool q9.2.CF)
  let v11 := mergeGPR 8 (if q10.2.CF then 1 else 0) h7
  let q12 := addSpec q9.1 v7
  let q13 := adcSpec h7 0 (BitVec.ofBool q12.2.CF)
  let q14 := addSpec v5 ((Operand.reg 15 : Operand 64).read s)
  let q15 := adcSpec v4 ((Operand.reg 9 : Operand 64).read s) (BitVec.ofBool q14.2.CF)
  let q16 := adcSpec q12.1 0 (BitVec.ofBool q15.2.CF)
  let q17 := adcSpec q13.1 0 (BitVec.ofBool q16.2.CF)
  obtain ⟨s1, a1, ready1, e1⟩ :=
    (movzx_r32_r8_rex_effect_step 0x113ca7 0x44 0xea (by simp [RexNoWPrefix]) (by decide)).advances ready (code 0 4)
      pre.rip (next 0x13cab (by decide))
  change (movzxR32R8Effect 0x113ca7 4 13 2 s).Holds s s1 at e1
  have m1 : s1.external = s.external := (e1.agrees.external (by simp [Component.Covers] <;> simp [Effect.components]))
  have v1r13 : ((Operand.reg 13 : Operand 64).read s1) = v1 := by
    have h : ((Operand.reg 13 : Operand 64).read s1) = (((Operand.reg 2 : Operand 64).read s).setWidth 8).setWidth 64 := e1.writes
    exact h
  have r1b6 : ((Operand.reg 6 : Operand 64).read s1) = ((Operand.reg 6 : Operand 64).read s) := (e1.agrees.read (by simp <;> simp [Effect.components])).trans (rfl)
  obtain ⟨s2, a2, ready2, e2⟩ :=
    (mov_r64_r64_effect_step 0x113cab 0x49 0xf2 (by simp [RexWPrefix]) (by decide)).advances ready1 ((code 4 3).of_external_eq m1)
      e1.rip (next 0x13cae (by decide))
  change (movR64R64Effect 0x113cab 10 6 s1).Holds s1 s2 at e2
  have m2 : s2.external = s.external := (e2.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])).trans m1
  have v2r10 : ((Operand.reg 10 : Operand 64).read s2) = ((Operand.reg 6 : Operand 64).read s) := by
    have h : ((Operand.reg 10 : Operand 64).read s2) = ((Operand.reg 6 : Operand 64).read s1) := e2.writes
    rw [r1b6] at h
    exact h
  have r2b6 : ((Operand.reg 6 : Operand 64).read s2) = ((Operand.reg 6 : Operand 64).read s) := (e2.agrees.read (by simp <;> simp [Effect.components])).trans ((e1.agrees.read (by simp <;> simp [Effect.components])).trans (rfl))
  obtain ⟨s3, a3, ready3, e3⟩ :=
    (mov_r64_r64_effect_step 0x113cae 0x49 0xf6 (by simp [RexWPrefix]) (by decide)).advances ready2 ((code 7 3).of_external_eq m2)
      e2.rip (next 0x13cb1 (by decide))
  change (movR64R64Effect 0x113cae 14 6 s2).Holds s2 s3 at e3
  have m3 : s3.external = s.external := (e3.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])).trans m2
  have v3r14 : ((Operand.reg 14 : Operand 64).read s3) = ((Operand.reg 6 : Operand 64).read s) := by
    have h : ((Operand.reg 14 : Operand 64).read s3) = ((Operand.reg 6 : Operand 64).read s2) := e3.writes
    rw [r2b6] at h
    exact h
  have r3b14 : ((Operand.reg 14 : Operand 64).read s3) = ((Operand.reg 6 : Operand 64).read s) := v3r14
  obtain ⟨s4, a4, ready4, e4⟩ :=
    (shr_r64_imm8_effect_step 0x113cb1 0x49 0xee 32 (by simp [RexWPrefix]) (by decide) (by decide)).advances ready3 ((code 10 4).of_external_eq m3)
      e3.rip (next 0x13cb5 (by decide))
  change (shrR64Effect 0x113cb1 4 14 32 s3).Holds s3 s4 at e4
  have m4 : s4.external = s.external := (e4.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])).trans m3
  have v4r14 : ((Operand.reg 14 : Operand 64).read s4) = v4 := by
    have h : ((Operand.reg 14 : Operand 64).read s4) = ((Operand.reg 14 : Operand 64).read s3) >>> 32 := e4.writes
    rw [r3b14] at h
    exact h
  have r4b10 : ((Operand.reg 10 : Operand 64).read s4) = ((Operand.reg 6 : Operand 64).read s) := (e4.agrees.read (by simp <;> simp [Effect.components])).trans ((e3.agrees.read (by simp <;> simp [Effect.components])).trans (v2r10))
  obtain ⟨s5, a5, ready5, e5⟩ :=
    (shl_r64_imm8_effect_step 0x113cb5 0x49 0xe2 32 (by simp [RexWPrefix]) (by decide) (by decide)).advances ready4 ((code 14 4).of_external_eq m4)
      e4.rip (next 0x13cb9 (by decide))
  change (shlR64Effect 0x113cb5 4 10 32 s4).Holds s4 s5 at e5
  have m5 : s5.external = s.external := (e5.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])).trans m4
  have v5r10 : ((Operand.reg 10 : Operand 64).read s5) = v5 := by
    have h : ((Operand.reg 10 : Operand 64).read s5) = ((Operand.reg 10 : Operand 64).read s4) <<< 32 := e5.writes
    rw [r4b10] at h
    exact h
  have r5b6 : ((Operand.reg 6 : Operand 64).read s5) = ((Operand.reg 6 : Operand 64).read s) := (e5.agrees.read (by simp <;> simp [Effect.components])).trans ((e4.agrees.read (by simp <;> simp [Effect.components])).trans ((e3.agrees.read (by simp <;> simp [Effect.components])).trans ((e2.agrees.read (by simp <;> simp [Effect.components])).trans ((e1.agrees.read (by simp <;> simp [Effect.components])).trans (rfl)))))
  obtain ⟨s6, a6, ready6, e6⟩ :=
    (mov_r64_r64_effect_step 0x113cb9 0x48 0xf0 (by simp [RexWPrefix]) (by decide)).advances ready5 ((code 18 3).of_external_eq m5)
      e5.rip (next 0x13cbc (by decide))
  change (movR64R64Effect 0x113cb9 0 6 s5).Holds s5 s6 at e6
  have m6 : s6.external = s.external := (e6.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])).trans m5
  have v6r0 : ((Operand.reg 0 : Operand 64).read s6) = ((Operand.reg 6 : Operand 64).read s) := by
    have h : ((Operand.reg 0 : Operand 64).read s6) = ((Operand.reg 6 : Operand 64).read s5) := e6.writes
    rw [r5b6] at h
    exact h
  have r6b11 : ((Operand.reg 11 : Operand 64).read s6) = ((Operand.reg 11 : Operand 64).read s) := (e6.agrees.read (by simp <;> simp [Effect.components])).trans ((e5.agrees.read (by simp <;> simp [Effect.components])).trans ((e4.agrees.read (by simp <;> simp [Effect.components])).trans ((e3.agrees.read (by simp <;> simp [Effect.components])).trans ((e2.agrees.read (by simp <;> simp [Effect.components])).trans ((e1.agrees.read (by simp <;> simp [Effect.components])).trans (rfl))))))
  have r6b0 : ((Operand.reg 0 : Operand 64).read s6) = ((Operand.reg 6 : Operand 64).read s) := v6r0
  obtain ⟨s7, a7, ready7, e7⟩ :=
    (mul_r64_effect_step 0x113cbc 0x49 0xe3 (by simp [RexWPrefix]) (by decide) (by decide)).advances ready6 ((code 21 3).of_external_eq m6)
      e6.rip (next 0x13cbf (by decide))
  change (mulR64Effect 0x113cbc 11 s6).Holds s6 s7 at e7
  have m7 : s7.external = s.external := (e7.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])).trans m6
  have v7r0 : ((Operand.reg 0 : Operand 64).read s7) = v7 := by
    have h : ((Operand.reg 0 : Operand 64).read s7) = ((Operand.reg 0 : Operand 64).read s6) * ((Operand.reg 11 : Operand 64).read s6) := e7.writes.1
    rw [r6b11, r6b0] at h
    exact h
  have v7r2 : ((Operand.reg 2 : Operand 64).read s7) = h7 := by
    have h : ((Operand.reg 2 : Operand 64).read s7) = mulHigh64 ((Operand.reg 0 : Operand 64).read s6) ((Operand.reg 11 : Operand 64).read s6) := e7.writes.2
    rw [r6b11, r6b0] at h
    exact h
  have r7b2 : ((Operand.reg 2 : Operand 64).read s7) = h7 := v7r2
  obtain ⟨s8, a8, ready8, e8⟩ :=
    (mov_r64_r64_effect_step 0x113cbf 0x48 0xd6 (by simp [RexWPrefix]) (by decide)).advances ready7 ((code 24 3).of_external_eq m7)
      e7.rip (next 0x13cc2 (by decide))
  change (movR64R64Effect 0x113cbf 6 2 s7).Holds s7 s8 at e8
  have m8 : s8.external = s.external := (e8.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])).trans m7
  have v8r6 : ((Operand.reg 6 : Operand 64).read s8) = h7 := by
    have h : ((Operand.reg 6 : Operand 64).read s8) = ((Operand.reg 2 : Operand 64).read s7) := e8.writes
    rw [r7b2] at h
    exact h
  have r8b12 : ((Operand.reg 12 : Operand 64).read s8) = ((Operand.reg 12 : Operand 64).read s) := (e8.agrees.read (by simp <;> simp [Effect.components])).trans ((e7.agrees.read (by simp <;> simp [Effect.components])).trans ((e6.agrees.read (by simp <;> simp [Effect.components])).trans ((e5.agrees.read (by simp <;> simp [Effect.components])).trans ((e4.agrees.read (by simp <;> simp [Effect.components])).trans ((e3.agrees.read (by simp <;> simp [Effect.components])).trans ((e2.agrees.read (by simp <;> simp [Effect.components])).trans ((e1.agrees.read (by simp <;> simp [Effect.components])).trans (rfl))))))))
  have r8b8 : ((Operand.reg 8 : Operand 64).read s8) = ((Operand.reg 8 : Operand 64).read s) := (e8.agrees.read (by simp <;> simp [Effect.components])).trans ((e7.agrees.read (by simp <;> simp [Effect.components])).trans ((e6.agrees.read (by simp <;> simp [Effect.components])).trans ((e5.agrees.read (by simp <;> simp [Effect.components])).trans ((e4.agrees.read (by simp <;> simp [Effect.components])).trans ((e3.agrees.read (by simp <;> simp [Effect.components])).trans ((e2.agrees.read (by simp <;> simp [Effect.components])).trans ((e1.agrees.read (by simp <;> simp [Effect.components])).trans (rfl))))))))
  obtain ⟨s9, a9, ready9, e9⟩ :=
    (add_r64_r64_effect_step 0x113cc2 0x4d 0xe0 (by simp [RexWPrefix]) (by decide)).advances ready8 ((code 27 3).of_external_eq m8)
      e8.rip (next 0x13cc5 (by decide))
  change (addR64R64Effect 0x113cc2 8 12 s8).Holds s8 s9 at e9
  have m9 : s9.external = s.external := (e9.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])).trans m8
  have v9r8 : ((Operand.reg 8 : Operand 64).read s9) = q9.1 := by
    have h : ((Operand.reg 8 : Operand 64).read s9) = (addSpec ((Operand.reg 8 : Operand 64).read s8) ((Operand.reg 12 : Operand 64).read s8) ).1 := e9.writes
    rw [r8b12, r8b8] at h
    exact h
  have c9 : (StatusFlags.ofRFLAGS s9.RFLAGS).CF = q9.2.CF := by
    have h : (StatusFlags.ofRFLAGS s9.RFLAGS).CF = (addSpec ((Operand.reg 8 : Operand 64).read s8) ((Operand.reg 12 : Operand 64).read s8) ).2.CF := e9.flags.1
    rw [r8b12, r8b8] at h
    exact h
  have r9b1 : ((Operand.reg 1 : Operand 64).read s9) = ((Operand.reg 1 : Operand 64).read s) := (e9.agrees.read (by simp <;> simp [Effect.components])).trans ((e8.agrees.read (by simp <;> simp [Effect.components])).trans ((e7.agrees.read (by simp <;> simp [Effect.components])).trans ((e6.agrees.read (by simp <;> simp [Effect.components])).trans ((e5.agrees.read (by simp <;> simp [Effect.components])).trans ((e4.agrees.read (by simp <;> simp [Effect.components])).trans ((e3.agrees.read (by simp <;> simp [Effect.components])).trans ((e2.agrees.read (by simp <;> simp [Effect.components])).trans ((e1.agrees.read (by simp <;> simp [Effect.components])).trans (rfl)))))))))
  have mr10 : MemReadable s9 (((Operand.reg 1 : Operand 64).read s9) + 16) 8 := by
    rw [r9b1]
    exact pre.readable10.of_external_eq m9
  have mv10 : (Operand.mem (((Operand.reg 1 : Operand 64).read s9) + 16) : Operand 64).read s9 = ((Operand.mem (((Operand.reg 1 : Operand 64).read s) + 16) : Operand 64).read s) := by
    change memLoad _ _ 64 = memLoad _ _ 64
    rw [m9, r9b1]
  have r9b13 : ((Operand.reg 13 : Operand 64).read s9) = v1 := (e9.agrees.read (by simp <;> simp [Effect.components])).trans ((e8.agrees.read (by simp <;> simp [Effect.components])).trans ((e7.agrees.read (by simp <;> simp [Effect.components])).trans ((e6.agrees.read (by simp <;> simp [Effect.components])).trans ((e5.agrees.read (by simp <;> simp [Effect.components])).trans ((e4.agrees.read (by simp <;> simp [Effect.components])).trans ((e3.agrees.read (by simp <;> simp [Effect.components])).trans ((e2.agrees.read (by simp <;> simp [Effect.components])).trans (v1r13))))))))
  have cf9in : (StatusFlags.ofRFLAGS s9.RFLAGS).CF = q9.2.CF := by
    exact c9
  obtain ⟨s10, a10, ready10, e10⟩ :=
    (adc_r64_m64_effect_step 0x113cc5 0x4c (by simp [RexWPrefix]) 5 (.base 1 (.d8 16)) (by decide) rfl rfl).advances ready9 ((code 30 4).of_external_eq m9)
      ⟨e9.rip, mr10⟩ (next 0x13cc9 (by decide))
  change (adcR64M64Effect 0x113cc5 13 (.base 1 (.d8 16)) s9).Holds s9 s10 at e10
  have m10 : s10.external = s.external := (e10.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])).trans m9
  have v10r13 : ((Operand.reg 13 : Operand 64).read s10) = q10.1 := by
    have h : ((Operand.reg 13 : Operand 64).read s10) = (adcSpec ((Operand.reg 13 : Operand 64).read s9) ((Operand.mem (((Operand.reg 1 : Operand 64).read s9) + 16) : Operand 64).read s9) (s9.RFLAGS.extractLsb' 0 1)).1 := e10.writes
    rw [mv10, r9b13, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf9in] at h
    exact h
  have c10 : (StatusFlags.ofRFLAGS s10.RFLAGS).CF = q10.2.CF := by
    have h : (StatusFlags.ofRFLAGS s10.RFLAGS).CF = (adcSpec ((Operand.reg 13 : Operand 64).read s9) ((Operand.mem (((Operand.reg 1 : Operand 64).read s9) + 16) : Operand 64).read s9) (s9.RFLAGS.extractLsb' 0 1)).2.CF := e10.flags.1
    rw [mv10, r9b13, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf9in] at h
    exact h
  have r10b2 : ((Operand.reg 2 : Operand 64).read s10) = h7 := (e10.agrees.read (by simp <;> simp [Effect.components])).trans ((e9.agrees.read (by simp <;> simp [Effect.components])).trans ((e8.agrees.read (by simp <;> simp [Effect.components])).trans (v7r2)))
  have cf10in : (StatusFlags.ofRFLAGS s10.RFLAGS).CF = q10.2.CF := by
    exact c10
  obtain ⟨s11, a11, ready11, e11⟩ :=
    (setcc_r8_effect_step 0x113cc9 0x92 0xc2 (by simp [SupportedOpcode]) (by decide) (by decide)).advances ready10 ((code 34 3).of_external_eq m10)
      e10.rip (next 0x13ccc (by decide))
  change (setccR8Effect 0x113cc9 3 2 2 s10).Holds s10 s11 at e11
  have m11 : s11.external = s.external := (e11.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])).trans m10
  have v11r2 : ((Operand.reg 2 : Operand 64).read s11) = v11 := by
    have h : ((Operand.reg 2 : Operand 64).read s11) = mergeGPR 8 (if (StatusFlags.ofRFLAGS s10.RFLAGS).CF then 1 else 0) ((Operand.reg 2 : Operand 64).read s10) := e11.writes
    rw [r10b2, cf10in] at h
    exact h
  have r11b0 : ((Operand.reg 0 : Operand 64).read s11) = v7 := (e11.agrees.read (by simp <;> simp [Effect.components])).trans ((e10.agrees.read (by simp <;> simp [Effect.components])).trans ((e9.agrees.read (by simp <;> simp [Effect.components])).trans ((e8.agrees.read (by simp <;> simp [Effect.components])).trans (v7r0))))
  have r11b8 : ((Operand.reg 8 : Operand 64).read s11) = q9.1 := (e11.agrees.read (by simp <;> simp [Effect.components])).trans ((e10.agrees.read (by simp <;> simp [Effect.components])).trans (v9r8))
  obtain ⟨s12, a12, ready12, e12⟩ :=
    (add_r64_r64_effect_step 0x113ccc 0x49 0xc0 (by simp [RexWPrefix]) (by decide)).advances ready11 ((code 37 3).of_external_eq m11)
      e11.rip (next 0x13ccf (by decide))
  change (addR64R64Effect 0x113ccc 8 0 s11).Holds s11 s12 at e12
  have m12 : s12.external = s.external := (e12.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])).trans m11
  have v12r8 : ((Operand.reg 8 : Operand 64).read s12) = q12.1 := by
    have h : ((Operand.reg 8 : Operand 64).read s12) = (addSpec ((Operand.reg 8 : Operand 64).read s11) ((Operand.reg 0 : Operand 64).read s11) ).1 := e12.writes
    rw [r11b0, r11b8] at h
    exact h
  have c12 : (StatusFlags.ofRFLAGS s12.RFLAGS).CF = q12.2.CF := by
    have h : (StatusFlags.ofRFLAGS s12.RFLAGS).CF = (addSpec ((Operand.reg 8 : Operand 64).read s11) ((Operand.reg 0 : Operand 64).read s11) ).2.CF := e12.flags.1
    rw [r11b0, r11b8] at h
    exact h
  have r12b6 : ((Operand.reg 6 : Operand 64).read s12) = h7 := (e12.agrees.read (by simp <;> simp [Effect.components])).trans ((e11.agrees.read (by simp <;> simp [Effect.components])).trans ((e10.agrees.read (by simp <;> simp [Effect.components])).trans ((e9.agrees.read (by simp <;> simp [Effect.components])).trans (v8r6))))
  have cf12in : (StatusFlags.ofRFLAGS s12.RFLAGS).CF = q12.2.CF := by
    exact c12
  obtain ⟨s13, a13, ready13, e13⟩ :=
    (adc_r64_imm8_effect_step 0x113ccf 0x48 0xd6 0 (by simp [RexWPrefix]) (by decide) (by decide)).advances ready12 ((code 40 4).of_external_eq m12)
      e12.rip (next 0x13cd3 (by decide))
  change (adcR64Imm8Effect 0x113ccf 6 0 s12).Holds s12 s13 at e13
  have m13 : s13.external = s.external := (e13.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])).trans m12
  have v13r6 : ((Operand.reg 6 : Operand 64).read s13) = q13.1 := by
    have h : ((Operand.reg 6 : Operand 64).read s13) = (adcSpec ((Operand.reg 6 : Operand 64).read s12) 0 (s12.RFLAGS.extractLsb' 0 1)).1 := e13.writes
    rw [r12b6, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf12in] at h
    exact h
  have c13 : (StatusFlags.ofRFLAGS s13.RFLAGS).CF = q13.2.CF := by
    have h : (StatusFlags.ofRFLAGS s13.RFLAGS).CF = (adcSpec ((Operand.reg 6 : Operand 64).read s12) 0 (s12.RFLAGS.extractLsb' 0 1)).2.CF := e13.flags.1
    rw [r12b6, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf12in] at h
    exact h
  have r13b15 : ((Operand.reg 15 : Operand 64).read s13) = ((Operand.reg 15 : Operand 64).read s) := (e13.agrees.read (by simp <;> simp [Effect.components])).trans ((e12.agrees.read (by simp <;> simp [Effect.components])).trans ((e11.agrees.read (by simp <;> simp [Effect.components])).trans ((e10.agrees.read (by simp <;> simp [Effect.components])).trans ((e9.agrees.read (by simp <;> simp [Effect.components])).trans ((e8.agrees.read (by simp <;> simp [Effect.components])).trans ((e7.agrees.read (by simp <;> simp [Effect.components])).trans ((e6.agrees.read (by simp <;> simp [Effect.components])).trans ((e5.agrees.read (by simp <;> simp [Effect.components])).trans ((e4.agrees.read (by simp <;> simp [Effect.components])).trans ((e3.agrees.read (by simp <;> simp [Effect.components])).trans ((e2.agrees.read (by simp <;> simp [Effect.components])).trans ((e1.agrees.read (by simp <;> simp [Effect.components])).trans (rfl)))))))))))))
  have r13b10 : ((Operand.reg 10 : Operand 64).read s13) = v5 := (e13.agrees.read (by simp <;> simp [Effect.components])).trans ((e12.agrees.read (by simp <;> simp [Effect.components])).trans ((e11.agrees.read (by simp <;> simp [Effect.components])).trans ((e10.agrees.read (by simp <;> simp [Effect.components])).trans ((e9.agrees.read (by simp <;> simp [Effect.components])).trans ((e8.agrees.read (by simp <;> simp [Effect.components])).trans ((e7.agrees.read (by simp <;> simp [Effect.components])).trans ((e6.agrees.read (by simp <;> simp [Effect.components])).trans (v5r10))))))))
  obtain ⟨s14, a14, ready14, e14⟩ :=
    (add_r64_r64_effect_step 0x113cd3 0x4d 0xfa (by simp [RexWPrefix]) (by decide)).advances ready13 ((code 44 3).of_external_eq m13)
      e13.rip (next 0x13cd6 (by decide))
  change (addR64R64Effect 0x113cd3 10 15 s13).Holds s13 s14 at e14
  have m14 : s14.external = s.external := (e14.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])).trans m13
  have v14r10 : ((Operand.reg 10 : Operand 64).read s14) = q14.1 := by
    have h : ((Operand.reg 10 : Operand 64).read s14) = (addSpec ((Operand.reg 10 : Operand 64).read s13) ((Operand.reg 15 : Operand 64).read s13) ).1 := e14.writes
    rw [r13b15, r13b10] at h
    exact h
  have c14 : (StatusFlags.ofRFLAGS s14.RFLAGS).CF = q14.2.CF := by
    have h : (StatusFlags.ofRFLAGS s14.RFLAGS).CF = (addSpec ((Operand.reg 10 : Operand 64).read s13) ((Operand.reg 15 : Operand 64).read s13) ).2.CF := e14.flags.1
    rw [r13b15, r13b10] at h
    exact h
  have r14b9 : ((Operand.reg 9 : Operand 64).read s14) = ((Operand.reg 9 : Operand 64).read s) := (e14.agrees.read (by simp <;> simp [Effect.components])).trans ((e13.agrees.read (by simp <;> simp [Effect.components])).trans ((e12.agrees.read (by simp <;> simp [Effect.components])).trans ((e11.agrees.read (by simp <;> simp [Effect.components])).trans ((e10.agrees.read (by simp <;> simp [Effect.components])).trans ((e9.agrees.read (by simp <;> simp [Effect.components])).trans ((e8.agrees.read (by simp <;> simp [Effect.components])).trans ((e7.agrees.read (by simp <;> simp [Effect.components])).trans ((e6.agrees.read (by simp <;> simp [Effect.components])).trans ((e5.agrees.read (by simp <;> simp [Effect.components])).trans ((e4.agrees.read (by simp <;> simp [Effect.components])).trans ((e3.agrees.read (by simp <;> simp [Effect.components])).trans ((e2.agrees.read (by simp <;> simp [Effect.components])).trans ((e1.agrees.read (by simp <;> simp [Effect.components])).trans (rfl))))))))))))))
  have r14b14 : ((Operand.reg 14 : Operand 64).read s14) = v4 := (e14.agrees.read (by simp <;> simp [Effect.components])).trans ((e13.agrees.read (by simp <;> simp [Effect.components])).trans ((e12.agrees.read (by simp <;> simp [Effect.components])).trans ((e11.agrees.read (by simp <;> simp [Effect.components])).trans ((e10.agrees.read (by simp <;> simp [Effect.components])).trans ((e9.agrees.read (by simp <;> simp [Effect.components])).trans ((e8.agrees.read (by simp <;> simp [Effect.components])).trans ((e7.agrees.read (by simp <;> simp [Effect.components])).trans ((e6.agrees.read (by simp <;> simp [Effect.components])).trans ((e5.agrees.read (by simp <;> simp [Effect.components])).trans (v4r14))))))))))
  have cf14in : (StatusFlags.ofRFLAGS s14.RFLAGS).CF = q14.2.CF := by
    exact c14
  obtain ⟨s15, a15, ready15, e15⟩ :=
    (adc_r64_r64_effect_step 0x113cd6 0x4d 0xce (by simp [RexWPrefix]) (by decide)).advances ready14 ((code 47 3).of_external_eq m14)
      e14.rip (next 0x13cd9 (by decide))
  change (adcR64R64Effect 0x113cd6 14 9 s14).Holds s14 s15 at e15
  have m15 : s15.external = s.external := (e15.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])).trans m14
  have v15r14 : ((Operand.reg 14 : Operand 64).read s15) = q15.1 := by
    have h : ((Operand.reg 14 : Operand 64).read s15) = (adcSpec ((Operand.reg 14 : Operand 64).read s14) ((Operand.reg 9 : Operand 64).read s14) (s14.RFLAGS.extractLsb' 0 1)).1 := e15.writes
    rw [r14b9, r14b14, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf14in] at h
    exact h
  have c15 : (StatusFlags.ofRFLAGS s15.RFLAGS).CF = q15.2.CF := by
    have h : (StatusFlags.ofRFLAGS s15.RFLAGS).CF = (adcSpec ((Operand.reg 14 : Operand 64).read s14) ((Operand.reg 9 : Operand 64).read s14) (s14.RFLAGS.extractLsb' 0 1)).2.CF := e15.flags.1
    rw [r14b9, r14b14, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf14in] at h
    exact h
  have r15b8 : ((Operand.reg 8 : Operand 64).read s15) = q12.1 := (e15.agrees.read (by simp <;> simp [Effect.components])).trans ((e14.agrees.read (by simp <;> simp [Effect.components])).trans ((e13.agrees.read (by simp <;> simp [Effect.components])).trans (v12r8)))
  have cf15in : (StatusFlags.ofRFLAGS s15.RFLAGS).CF = q15.2.CF := by
    exact c15
  obtain ⟨s16, a16, ready16, e16⟩ :=
    (adc_r64_imm8_effect_step 0x113cd9 0x49 0xd0 0 (by simp [RexWPrefix]) (by decide) (by decide)).advances ready15 ((code 50 4).of_external_eq m15)
      e15.rip (next 0x13cdd (by decide))
  change (adcR64Imm8Effect 0x113cd9 8 0 s15).Holds s15 s16 at e16
  have m16 : s16.external = s.external := (e16.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])).trans m15
  have v16r8 : ((Operand.reg 8 : Operand 64).read s16) = q16.1 := by
    have h : ((Operand.reg 8 : Operand 64).read s16) = (adcSpec ((Operand.reg 8 : Operand 64).read s15) 0 (s15.RFLAGS.extractLsb' 0 1)).1 := e16.writes
    rw [r15b8, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf15in] at h
    exact h
  have c16 : (StatusFlags.ofRFLAGS s16.RFLAGS).CF = q16.2.CF := by
    have h : (StatusFlags.ofRFLAGS s16.RFLAGS).CF = (adcSpec ((Operand.reg 8 : Operand 64).read s15) 0 (s15.RFLAGS.extractLsb' 0 1)).2.CF := e16.flags.1
    rw [r15b8, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf15in] at h
    exact h
  have r16b6 : ((Operand.reg 6 : Operand 64).read s16) = q13.1 := (e16.agrees.read (by simp <;> simp [Effect.components])).trans ((e15.agrees.read (by simp <;> simp [Effect.components])).trans ((e14.agrees.read (by simp <;> simp [Effect.components])).trans (v13r6)))
  have cf16in : (StatusFlags.ofRFLAGS s16.RFLAGS).CF = q16.2.CF := by
    exact c16
  obtain ⟨s17, a17, ready17, e17⟩ :=
    (adc_r64_imm8_effect_step 0x113cdd 0x48 0xd6 0 (by simp [RexWPrefix]) (by decide) (by decide)).advances ready16 ((code 54 4).of_external_eq m16)
      e16.rip (next 0x13ce1 (by decide))
  change (adcR64Imm8Effect 0x113cdd 6 0 s16).Holds s16 s17 at e17
  have m17 : s17.external = s.external := (e17.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])).trans m16
  have v17r6 : ((Operand.reg 6 : Operand 64).read s17) = q17.1 := by
    have h : ((Operand.reg 6 : Operand 64).read s17) = (adcSpec ((Operand.reg 6 : Operand 64).read s16) 0 (s16.RFLAGS.extractLsb' 0 1)).1 := e17.writes
    rw [r16b6, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf16in] at h
    exact h
  have c17 : (StatusFlags.ofRFLAGS s17.RFLAGS).CF = q17.2.CF := by
    have h : (StatusFlags.ofRFLAGS s17.RFLAGS).CF = (adcSpec ((Operand.reg 6 : Operand 64).read s16) 0 (s16.RFLAGS.extractLsb' 0 1)).2.CF := e17.flags.1
    rw [r16b6, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf16in] at h
    exact h
  have flags17 : (StatusFlagsOutcome.ofStatusFlags q17.2).Allows (StatusFlags.ofRFLAGS s17.RFLAGS) := by
    have h : (StatusFlagsOutcome.ofStatusFlags (adcSpec ((Operand.reg 6 : Operand 64).read s16) 0 (s16.RFLAGS.extractLsb' 0 1)).2).Allows _ := e17.flags
    rw [r16b6, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf16in] at h
    exact h
  have r17b0 : ((Operand.reg 0 : Operand 64).read s17) = v7 := (e17.agrees.read (by simp <;> simp [Effect.components])).trans ((e16.agrees.read (by simp <;> simp [Effect.components])).trans ((e15.agrees.read (by simp <;> simp [Effect.components])).trans ((e14.agrees.read (by simp <;> simp [Effect.components])).trans ((e13.agrees.read (by simp <;> simp [Effect.components])).trans ((e12.agrees.read (by simp <;> simp [Effect.components])).trans ((e11.agrees.read (by simp <;> simp [Effect.components])).trans ((e10.agrees.read (by simp <;> simp [Effect.components])).trans ((e9.agrees.read (by simp <;> simp [Effect.components])).trans ((e8.agrees.read (by simp <;> simp [Effect.components])).trans (v7r0))))))))))
  have r17b2 : ((Operand.reg 2 : Operand 64).read s17) = v11 := (e17.agrees.read (by simp <;> simp [Effect.components])).trans ((e16.agrees.read (by simp <;> simp [Effect.components])).trans ((e15.agrees.read (by simp <;> simp [Effect.components])).trans ((e14.agrees.read (by simp <;> simp [Effect.components])).trans ((e13.agrees.read (by simp <;> simp [Effect.components])).trans ((e12.agrees.read (by simp <;> simp [Effect.components])).trans (v11r2))))))
  have r17b6 : ((Operand.reg 6 : Operand 64).read s17) = q17.1 := v17r6
  have r17b8 : ((Operand.reg 8 : Operand 64).read s17) = q16.1 := (e17.agrees.read (by simp <;> simp [Effect.components])).trans (v16r8)
  have r17b10 : ((Operand.reg 10 : Operand 64).read s17) = q14.1 := (e17.agrees.read (by simp <;> simp [Effect.components])).trans ((e16.agrees.read (by simp <;> simp [Effect.components])).trans ((e15.agrees.read (by simp <;> simp [Effect.components])).trans (v14r10)))
  have r17b13 : ((Operand.reg 13 : Operand 64).read s17) = q10.1 := (e17.agrees.read (by simp <;> simp [Effect.components])).trans ((e16.agrees.read (by simp <;> simp [Effect.components])).trans ((e15.agrees.read (by simp <;> simp [Effect.components])).trans ((e14.agrees.read (by simp <;> simp [Effect.components])).trans ((e13.agrees.read (by simp <;> simp [Effect.components])).trans ((e12.agrees.read (by simp <;> simp [Effect.components])).trans ((e11.agrees.read (by simp <;> simp [Effect.components])).trans (v10r13)))))))
  have r17b14 : ((Operand.reg 14 : Operand 64).read s17) = q15.1 := (e17.agrees.read (by simp <;> simp [Effect.components])).trans ((e16.agrees.read (by simp <;> simp [Effect.components])).trans (v15r14))
  refine ⟨17, s17, ((((((((((((((((a1).trans a2).trans a3).trans a4).trans a5).trans a6).trans a7).trans a8).trans a9).trans a10).trans a11).trans a12).trans a13).trans a14).trans a15).trans a16).trans a17, ready17, loaded.of_external_eq m17, e17.rip, ?_, ?_, ?_⟩
  · exact ⟨r17b0, r17b2, r17b6, r17b8, r17b10, r17b13, r17b14⟩
  · exact flags17
  · apply (((((((((((((((((e1.agrees).trans e2.agrees).trans e3.agrees).trans e4.agrees).trans e5.agrees).trans e6.agrees).trans e7.agrees).trans e8.agrees).trans e9.agrees).trans e10.agrees).trans e11.agrees).trans e12.agrees).trans e13.agrees).trans e14.agrees).trans e15.agrees).trans e16.agrees).trans e17.agrees).mono
    simp only [movR64R64Effect_components, shrR64Effect_components, shlR64Effect_components, mulR64Effect_components, addR64R64Effect_components, adcR64M64Effect_components, setccR8Effect_components, adcR64Imm8Effect_components, adcR64R64Effect_components]
    simp [thirdRoundEffect, Effect.components]

theorem thirdRound_bytes :
    Extracted.textBytes.toListFrom 0x13ca7 thirdRoundBytes.length = thirdRoundBytes := by
  decide +kernel

end P256.Proofs.Field.Montgomery.Reduction
