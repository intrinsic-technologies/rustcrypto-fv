import P256.Proofs.Common.Field.Montgomery.Schoolbook.CarryCompose
import P256.Proofs.Common.Instructions.ShiftLeft.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import P256.Proofs.Program.Code
import P256.Proofs.Common.Instructions.MovzxByte
import P256.Proofs.Common.Instructions.Neg64
import P256.Proofs.Field.Montgomery.Reduction.Slot
import P256.Proofs.Common.Field.Operations.Neg.Borrow.Or

set_option autoImplicit false

open P256.Proofs.Common.Field.FieldNeg.Instructions (orR64R64Effect_components)
open P256.Proofs.Common.Field.Instructions (subR64M64Effect subR64M64Effect_components sub_r64_m64_effect_step)
open P256.Proofs.Common.Instructions (addR64M64Effect_components mulR64Effect_components sarR64Effect sarR64Effect_components sar_r64_imm8_effect_step)
open P256.Proofs.Common.Instructions.AddByte (addR8Imm8Effect add_r8_imm8_effect_step)
open P256.Proofs.Common.Instructions.Carry (adcR64Imm8Effect adcR64Imm8Effect_components adcR64M64Effect_components adcR64R64Effect adcR64R64Effect_components adcSpec adc_r64_imm8_effect_step adc_r64_r64_effect_step)
open P256.Proofs.Common.Instructions.MovzxByte (movzxR32R8Effect)
open P256.Proofs.Common.Instructions.Neg64 (negR64Effect)
open P256.Proofs.Common.Instructions.Setb (setccR8Effect_components)
open P256.Proofs.Common.Instructions.ShiftLeft (shlR64Effect_components)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Field.Montgomery.Reduction

open P256.Spec.Program.Routines
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

attribute [local simp] movzxR32R8Effect addR8Imm8Effect negR64Effect

attribute [local simp] mulR64Effect_components adcR64R64Effect_components adcR64Imm8Effect_components
  adcR64M64Effect_components addR64M64Effect_components setccR8Effect_components shlR64Effect_components
  orR64R64Effect_components sarR64Effect_components subR64M64Effect_components

def borrowHighBytes : List UInt8 :=
  [0x41, 0x89, 0xef, 0x41, 0x80, 0xc7, 0xff, 0x49, 0x11, 0xf2, 0x40, 0x80, 0xc5, 0xff, 0x48, 0x83, 0xd6, 0x0, 0x48, 0x83, 0xd2, 0x0, 0x4d, 0x8d, 0x3c, 0x11, 0x48, 0xf7, 0xd6, 0x4c, 0x21, 0xd6, 0x48, 0xc1, 0xee, 0x3f, 0x48, 0x89, 0x34, 0x24, 0x48, 0x89, 0xe6, 0x31, 0xf6, 0x48, 0x2b, 0x34, 0x24, 0x48, 0xc1, 0xfe, 0x3f]

def borrowHighEffect (s : RamState) : Effect :=
  let v1 := (((Operand.reg 5 : Operand 64).read s).setWidth 32).setWidth 64
  let q2 := addSpec (v1.setWidth 8) (255 : BitVec 8)
  let q3 := adcSpec ((Operand.reg 10 : Operand 64).read s) ((Operand.reg 6 : Operand 64).read s) (BitVec.ofBool q2.2.CF)
  let q4 := addSpec (((Operand.reg 5 : Operand 64).read s).setWidth 8) (255 : BitVec 8)
  let v4 := mergeGPR 8 q4.1 ((Operand.reg 5 : Operand 64).read s)
  let q5 := adcSpec ((Operand.reg 6 : Operand 64).read s) 0 (BitVec.ofBool q4.2.CF)
  let q6 := adcSpec ((Operand.reg 2 : Operand 64).read s) 0 (BitVec.ofBool q5.2.CF)
  let v7 := ((Operand.reg 9 : Operand 64).read s) + q6.1 + 0
  let v8 := ~~~q5.1
  let v9 := v8 &&& q3.1
  let v10 := v9 >>> 63
  let q14 := subSpec (0 : BitVec 64) v10
  let v15 := (q14.1).sshiftRight 63
  { rip := 0x113d8f
    writes := [⟨(.reg 2 : Operand 64), q6.1⟩,
      ⟨(.reg 5 : Operand 64), v4⟩,
      ⟨(.reg 6 : Operand 64), v15⟩,
      ⟨(.reg 10 : Operand 64), q3.1⟩,
      ⟨(.reg 15 : Operand 64), v7⟩,
      ⟨(.mem (stackPtr s) : Operand 64), v10⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem borrowHigh_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (BorrowSlotPre 0x113d5a) (codeRange 0x113d5a borrowHighBytes)
      (Effect.post borrowHighEffect) := by
  intro s ready loaded pre
  have next (offset : Nat) (h : offset < 118431) :=
    boundary_ne_program hout (inProgram_of_textOffset offset h)
  have code (offset len : Nat) := loaded.mono (codeRange_slice_subset 0x113d5a borrowHighBytes offset len)
  have loaded0 := loaded
  have w0 := pre.writable
  have m0 : s.external = s.external := rfl
  have c0 : (StatusFlags.ofRFLAGS s.RFLAGS).CF = (StatusFlags.ofRFLAGS s.RFLAGS).CF := rfl
  let v1 := (((Operand.reg 5 : Operand 64).read s).setWidth 32).setWidth 64
  let q2 := addSpec (v1.setWidth 8) (255 : BitVec 8)
  let v2 := mergeGPR 8 q2.1 v1
  let q3 := adcSpec ((Operand.reg 10 : Operand 64).read s) ((Operand.reg 6 : Operand 64).read s) (BitVec.ofBool q2.2.CF)
  let q4 := addSpec (((Operand.reg 5 : Operand 64).read s).setWidth 8) (255 : BitVec 8)
  let v4 := mergeGPR 8 q4.1 ((Operand.reg 5 : Operand 64).read s)
  let q5 := adcSpec ((Operand.reg 6 : Operand 64).read s) 0 (BitVec.ofBool q4.2.CF)
  let q6 := adcSpec ((Operand.reg 2 : Operand 64).read s) 0 (BitVec.ofBool q5.2.CF)
  let v7 := ((Operand.reg 9 : Operand 64).read s) + q6.1 + 0
  let v8 := ~~~q5.1
  let v9 := v8 &&& q3.1
  let v10 := v9 >>> 63
  let q14 := subSpec (0 : BitVec 64) v10
  let v15 := (q14.1).sshiftRight 63
  obtain ⟨s1, a1, ready1, e1⟩ :=
    (mov_r32_r32_rex_effect_step 0x113d5a 0x41 0xef (by simp [RexNoWPrefix]) (by decide)).advances ready (loaded0.mono (codeRange_slice_subset 0x113d5a borrowHighBytes 0 3))
      pre.rip (next 0x13d5d (by decide))
  change (movR32R32Effect 0x113d5a 3 15 5 s).Holds s s1 at e1
  have mx1 : s1.external = s.external := e1.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])
  have m1 : s1.external = s.external := mx1.trans m0
  have loaded1 := loaded0.of_external_eq mx1
  have w1 := MemWritable.of_holds e1 w0
  have v1r15 : ((Operand.reg 15 : Operand 64).read s1) = v1 := by
    have h : ((Operand.reg 15 : Operand 64).read s1) = (((Operand.reg 5 : Operand 64).read s).setWidth 32).setWidth 64 := e1.writes
    exact h
  have r1b15 : ((Operand.reg 15 : Operand 64).read s1) = v1 := v1r15
  obtain ⟨s2, a2, ready2, e2⟩ :=
    (add_r8_imm8_effect_step 0x113d5d 0x41 0xc7 255 (by simp [RexPrefix]) (by decide) (by decide)).advances ready1 (loaded1.mono (codeRange_slice_subset 0x113d5a borrowHighBytes 3 4))
      e1.rip (next 0x13d61 (by decide))
  change (addR8Imm8Effect 0x113d5d 15 255 s1).Holds s1 s2 at e2
  have mx2 : s2.external = s1.external := e2.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])
  have m2 : s2.external = s.external := mx2.trans m1
  have loaded2 := loaded1.of_external_eq mx2
  have w2 := MemWritable.of_holds e2 w1
  have v2r15 : ((Operand.reg 15 : Operand 64).read s2) = v2 := by
    have h : ((Operand.reg 15 : Operand 64).read s2) = mergeGPR 8 (addSpec (((Operand.reg 15 : Operand 64).read s1).setWidth 8) (255 : BitVec 8)).1 ((Operand.reg 15 : Operand 64).read s1) := e2.writes
    rw [r1b15] at h
    exact h
  have c2 : (StatusFlags.ofRFLAGS s2.RFLAGS).CF = q2.2.CF := by
    have h : (StatusFlags.ofRFLAGS s2.RFLAGS).CF = (addSpec (((Operand.reg 15 : Operand 64).read s1).setWidth 8) (255 : BitVec 8)).2.CF := e2.flags.1
    rw [r1b15] at h
    exact h
  have r2b6 : ((Operand.reg 6 : Operand 64).read s2) = ((Operand.reg 6 : Operand 64).read s) := (e2.agrees.read (by simp <;> simp [Effect.components])).trans ((e1.agrees.read (by simp <;> simp [Effect.components])).trans (rfl))
  have r2b10 : ((Operand.reg 10 : Operand 64).read s2) = ((Operand.reg 10 : Operand 64).read s) := (e2.agrees.read (by simp <;> simp [Effect.components])).trans ((e1.agrees.read (by simp <;> simp [Effect.components])).trans (rfl))
  have cf2in : (StatusFlags.ofRFLAGS s2.RFLAGS).CF = q2.2.CF := by
    try exact c2
  obtain ⟨s3, a3, ready3, e3⟩ :=
    (adc_r64_r64_effect_step 0x113d61 0x49 0xf2 (by simp [RexWPrefix]) (by decide)).advances ready2 (loaded2.mono (codeRange_slice_subset 0x113d5a borrowHighBytes 7 3))
      e2.rip (next 0x13d64 (by decide))
  change (adcR64R64Effect 0x113d61 10 6 s2).Holds s2 s3 at e3
  have mx3 : s3.external = s2.external := e3.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])
  have m3 : s3.external = s.external := mx3.trans m2
  have loaded3 := loaded2.of_external_eq mx3
  have w3 := MemWritable.of_holds e3 w2
  have v3r10 : ((Operand.reg 10 : Operand 64).read s3) = q3.1 := by
    have h : ((Operand.reg 10 : Operand 64).read s3) = (adcSpec ((Operand.reg 10 : Operand 64).read s2) ((Operand.reg 6 : Operand 64).read s2) (s2.RFLAGS.extractLsb' 0 1)).1 := e3.writes
    rw [r2b6, r2b10, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf2in] at h
    exact h
  have c3 : (StatusFlags.ofRFLAGS s3.RFLAGS).CF = q3.2.CF := by
    have h : (StatusFlags.ofRFLAGS s3.RFLAGS).CF = (adcSpec ((Operand.reg 10 : Operand 64).read s2) ((Operand.reg 6 : Operand 64).read s2) (s2.RFLAGS.extractLsb' 0 1)).2.CF := e3.flags.1
    rw [r2b6, r2b10, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf2in] at h
    exact h
  have r3b5 : ((Operand.reg 5 : Operand 64).read s3) = ((Operand.reg 5 : Operand 64).read s) := (e3.agrees.read (by simp <;> simp [Effect.components])).trans ((e2.agrees.read (by simp <;> simp [Effect.components])).trans ((e1.agrees.read (by simp <;> simp [Effect.components])).trans (rfl)))
  obtain ⟨s4, a4, ready4, e4⟩ :=
    (add_r8_imm8_effect_step 0x113d64 0x40 0xc5 255 (by simp [RexPrefix]) (by decide) (by decide)).advances ready3 (loaded3.mono (codeRange_slice_subset 0x113d5a borrowHighBytes 10 4))
      e3.rip (next 0x13d68 (by decide))
  change (addR8Imm8Effect 0x113d64 5 255 s3).Holds s3 s4 at e4
  have mx4 : s4.external = s3.external := e4.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])
  have m4 : s4.external = s.external := mx4.trans m3
  have loaded4 := loaded3.of_external_eq mx4
  have w4 := MemWritable.of_holds e4 w3
  have v4r5 : ((Operand.reg 5 : Operand 64).read s4) = v4 := by
    have h : ((Operand.reg 5 : Operand 64).read s4) = mergeGPR 8 (addSpec (((Operand.reg 5 : Operand 64).read s3).setWidth 8) (255 : BitVec 8)).1 ((Operand.reg 5 : Operand 64).read s3) := e4.writes
    rw [r3b5] at h
    exact h
  have c4 : (StatusFlags.ofRFLAGS s4.RFLAGS).CF = q4.2.CF := by
    have h : (StatusFlags.ofRFLAGS s4.RFLAGS).CF = (addSpec (((Operand.reg 5 : Operand 64).read s3).setWidth 8) (255 : BitVec 8)).2.CF := e4.flags.1
    rw [r3b5] at h
    exact h
  have r4b6 : ((Operand.reg 6 : Operand 64).read s4) = ((Operand.reg 6 : Operand 64).read s) := (e4.agrees.read (by simp <;> simp [Effect.components])).trans ((e3.agrees.read (by simp <;> simp [Effect.components])).trans ((e2.agrees.read (by simp <;> simp [Effect.components])).trans ((e1.agrees.read (by simp <;> simp [Effect.components])).trans (rfl))))
  have cf4in : (StatusFlags.ofRFLAGS s4.RFLAGS).CF = q4.2.CF := by
    try exact c4
  obtain ⟨s5, a5, ready5, e5⟩ :=
    (adc_r64_imm8_effect_step 0x113d68 0x48 0xd6 0 (by simp [RexWPrefix]) (by decide) (by decide)).advances ready4 (loaded4.mono (codeRange_slice_subset 0x113d5a borrowHighBytes 14 4))
      e4.rip (next 0x13d6c (by decide))
  change (adcR64Imm8Effect 0x113d68 6 0 s4).Holds s4 s5 at e5
  have mx5 : s5.external = s4.external := e5.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])
  have m5 : s5.external = s.external := mx5.trans m4
  have loaded5 := loaded4.of_external_eq mx5
  have w5 := MemWritable.of_holds e5 w4
  have v5r6 : ((Operand.reg 6 : Operand 64).read s5) = q5.1 := by
    have h : ((Operand.reg 6 : Operand 64).read s5) = (adcSpec ((Operand.reg 6 : Operand 64).read s4) 0 (s4.RFLAGS.extractLsb' 0 1)).1 := e5.writes
    rw [r4b6, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf4in] at h
    exact h
  have c5 : (StatusFlags.ofRFLAGS s5.RFLAGS).CF = q5.2.CF := by
    have h : (StatusFlags.ofRFLAGS s5.RFLAGS).CF = (adcSpec ((Operand.reg 6 : Operand 64).read s4) 0 (s4.RFLAGS.extractLsb' 0 1)).2.CF := e5.flags.1
    rw [r4b6, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf4in] at h
    exact h
  have r5b2 : ((Operand.reg 2 : Operand 64).read s5) = ((Operand.reg 2 : Operand 64).read s) := (e5.agrees.read (by simp <;> simp [Effect.components])).trans ((e4.agrees.read (by simp <;> simp [Effect.components])).trans ((e3.agrees.read (by simp <;> simp [Effect.components])).trans ((e2.agrees.read (by simp <;> simp [Effect.components])).trans ((e1.agrees.read (by simp <;> simp [Effect.components])).trans (rfl)))))
  have cf5in : (StatusFlags.ofRFLAGS s5.RFLAGS).CF = q5.2.CF := by
    try exact c5
  obtain ⟨s6, a6, ready6, e6⟩ :=
    (adc_r64_imm8_effect_step 0x113d6c 0x48 0xd2 0 (by simp [RexWPrefix]) (by decide) (by decide)).advances ready5 (loaded5.mono (codeRange_slice_subset 0x113d5a borrowHighBytes 18 4))
      e5.rip (next 0x13d70 (by decide))
  change (adcR64Imm8Effect 0x113d6c 2 0 s5).Holds s5 s6 at e6
  have mx6 : s6.external = s5.external := e6.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])
  have m6 : s6.external = s.external := mx6.trans m5
  have loaded6 := loaded5.of_external_eq mx6
  have w6 := MemWritable.of_holds e6 w5
  have v6r2 : ((Operand.reg 2 : Operand 64).read s6) = q6.1 := by
    have h : ((Operand.reg 2 : Operand 64).read s6) = (adcSpec ((Operand.reg 2 : Operand 64).read s5) 0 (s5.RFLAGS.extractLsb' 0 1)).1 := e6.writes
    rw [r5b2, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf5in] at h
    exact h
  have c6 : (StatusFlags.ofRFLAGS s6.RFLAGS).CF = q6.2.CF := by
    have h : (StatusFlags.ofRFLAGS s6.RFLAGS).CF = (adcSpec ((Operand.reg 2 : Operand 64).read s5) 0 (s5.RFLAGS.extractLsb' 0 1)).2.CF := e6.flags.1
    rw [r5b2, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf5in] at h
    exact h
  have r6b9 : ((Operand.reg 9 : Operand 64).read s6) = ((Operand.reg 9 : Operand 64).read s) := (e6.agrees.read (by simp <;> simp [Effect.components])).trans ((e5.agrees.read (by simp <;> simp [Effect.components])).trans ((e4.agrees.read (by simp <;> simp [Effect.components])).trans ((e3.agrees.read (by simp <;> simp [Effect.components])).trans ((e2.agrees.read (by simp <;> simp [Effect.components])).trans ((e1.agrees.read (by simp <;> simp [Effect.components])).trans (rfl))))))
  have r6b2 : ((Operand.reg 2 : Operand 64).read s6) = q6.1 := v6r2
  obtain ⟨s7, a7, ready7, e7⟩ :=
    (lea_r64_effect_step 0x113d70 0x4d (by simp [RexWPrefix]) 7 (.sib 9 (some 2) 0 .none) (by decide) rfl rfl).advances ready6 (loaded6.mono (codeRange_slice_subset 0x113d5a borrowHighBytes 22 4))
      e6.rip (next 0x13d74 (by decide))
  change (leaR64Effect 0x113d70 15 (.sib 9 (some 2) 0 .none) s6).Holds s6 s7 at e7
  have mx7 : s7.external = s6.external := e7.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])
  have m7 : s7.external = s.external := mx7.trans m6
  have loaded7 := loaded6.of_external_eq mx7
  have w7 := MemWritable.of_holds e7 w6
  have v7r15 : ((Operand.reg 15 : Operand 64).read s7) = v7 := by
    have h : ((Operand.reg 15 : Operand 64).read s7) = ((Operand.reg 9 : Operand 64).read s6) + ((Operand.reg 2 : Operand 64).read s6) + 0 := (by have h : ((Operand.reg 15 : Operand 64).read s7) = ((Operand.reg 9 : Operand 64).read s6) + (((Operand.reg 2 : Operand 64).read s6) <<< 0) + 0 := e7.writes; simpa only [BitVec.shiftLeft_zero] using h)
    rw [r6b9, r6b2] at h
    exact h
  have r7b6 : ((Operand.reg 6 : Operand 64).read s7) = q5.1 := (e7.agrees.read (by simp <;> simp [Effect.components])).trans ((e6.agrees.read (by simp <;> simp [Effect.components])).trans (v5r6))
  obtain ⟨s8, a8, ready8, e8⟩ :=
    (not_r64_effect_step 0x113d74 0x48 0xd6 (by simp [RexWPrefix]) (by decide) (by decide)).advances ready7 (loaded7.mono (codeRange_slice_subset 0x113d5a borrowHighBytes 26 3))
      e7.rip (next 0x13d77 (by decide))
  change (notR64Effect 0x113d74 6 s7).Holds s7 s8 at e8
  have mx8 : s8.external = s7.external := e8.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])
  have m8 : s8.external = s.external := mx8.trans m7
  have loaded8 := loaded7.of_external_eq mx8
  have w8 := MemWritable.of_holds e8 w7
  have v8r6 : ((Operand.reg 6 : Operand 64).read s8) = v8 := by
    have h : ((Operand.reg 6 : Operand 64).read s8) = ~~~((Operand.reg 6 : Operand 64).read s7) := e8.writes
    rw [r7b6] at h
    exact h
  have r8b10 : ((Operand.reg 10 : Operand 64).read s8) = q3.1 := (e8.agrees.read (by simp <;> simp [Effect.components])).trans ((e7.agrees.read (by simp <;> simp [Effect.components])).trans ((e6.agrees.read (by simp <;> simp [Effect.components])).trans ((e5.agrees.read (by simp <;> simp [Effect.components])).trans ((e4.agrees.read (by simp <;> simp [Effect.components])).trans (v3r10)))))
  have r8b6 : ((Operand.reg 6 : Operand 64).read s8) = v8 := v8r6
  obtain ⟨s9, a9, ready9, e9⟩ :=
    (and_r64_r64_effect_step 0x113d77 0x4c 0xd6 (by simp [RexWPrefix]) (by decide)).advances ready8 (loaded8.mono (codeRange_slice_subset 0x113d5a borrowHighBytes 29 3))
      e8.rip (next 0x13d7a (by decide))
  change (andR64R64Effect 0x113d77 6 10 s8).Holds s8 s9 at e9
  have mx9 : s9.external = s8.external := e9.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])
  have m9 : s9.external = s.external := mx9.trans m8
  have loaded9 := loaded8.of_external_eq mx9
  have w9 := MemWritable.of_holds e9 w8
  have v9r6 : ((Operand.reg 6 : Operand 64).read s9) = v9 := by
    have h : ((Operand.reg 6 : Operand 64).read s9) = ((Operand.reg 6 : Operand 64).read s8) &&& ((Operand.reg 10 : Operand 64).read s8) := e9.writes
    rw [r8b10, r8b6] at h
    exact h
  have r9b6 : ((Operand.reg 6 : Operand 64).read s9) = v9 := v9r6
  obtain ⟨s10, a10, ready10, e10⟩ :=
    (shr_r64_imm8_effect_step 0x113d7a 0x48 0xee 63 (by simp [RexWPrefix]) (by decide) (by decide)).advances ready9 (loaded9.mono (codeRange_slice_subset 0x113d5a borrowHighBytes 32 4))
      e9.rip (next 0x13d7e (by decide))
  change (shrR64Effect 0x113d7a 4 6 63 s9).Holds s9 s10 at e10
  have mx10 : s10.external = s9.external := e10.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])
  have m10 : s10.external = s.external := mx10.trans m9
  have loaded10 := loaded9.of_external_eq mx10
  have w10 := MemWritable.of_holds e10 w9
  have v10r6 : ((Operand.reg 6 : Operand 64).read s10) = v10 := by
    have h : ((Operand.reg 6 : Operand 64).read s10) = ((Operand.reg 6 : Operand 64).read s9) >>> 63 := e10.writes
    rw [r9b6] at h
    exact h
  have r10b6 : ((Operand.reg 6 : Operand 64).read s10) = v10 := v10r6
  have r10b4 : ((Operand.reg 4 : Operand 64).read s10) = ((Operand.reg 4 : Operand 64).read s) := (e10.agrees.read (by simp <;> simp [Effect.components])).trans ((e9.agrees.read (by simp <;> simp [Effect.components])).trans ((e8.agrees.read (by simp <;> simp [Effect.components])).trans ((e7.agrees.read (by simp <;> simp [Effect.components])).trans ((e6.agrees.read (by simp <;> simp [Effect.components])).trans ((e5.agrees.read (by simp <;> simp [Effect.components])).trans ((e4.agrees.read (by simp <;> simp [Effect.components])).trans ((e3.agrees.read (by simp <;> simp [Effect.components])).trans ((e2.agrees.read (by simp <;> simp [Effect.components])).trans ((e1.agrees.read (by simp <;> simp [Effect.components])).trans (rfl))))))))))
  have st11 : StorePre 0x113d7e 4 (fun t => ((Operand.reg 4 : Operand 64).read t) + 0) 8 s10 := by
    refine ⟨e10.rip, ?_, ?_⟩
    · rw [r10b4]
      change MemWritable s10 (stackPtr s + 0#64) 8
      rw [BitVec.add_zero]
      exact w10
    · rw [r10b4]
      change RangeApart (stackPtr s + 0#64) 8 0x113d7e 4
      rw [BitVec.add_zero]
      exact pre.apart 0x13d7e 4 (by decide)
  obtain ⟨s11, a11, ready11, e11⟩ :=
    (mov_m64_r64_effect_step 0x113d7e 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 .none) (by decide) rfl rfl).advances ready10 (loaded10.mono (codeRange_slice_subset 0x113d5a borrowHighBytes 36 4))
      st11 (next 0x13d82 (by decide))
  change (movM64R64Effect 0x113d7e 6 (.sib 4 none 0 .none) s10).Holds s10 s11 at e11
  change ({ rip := 0x113d82, writes := [⟨(.mem (((Operand.reg 4 : Operand 64).read s10) + 0) : Operand 64), ((Operand.reg 6 : Operand 64).read s10)⟩] } : Effect).Holds s10 s11 at e11
  rw [r10b4] at e11
  rw [r10b6] at e11
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at e11
  have m11 : s11.external = s11.external := rfl
  have loaded11 := e11.codeIn (pre.avoids_code 0x13d5a borrowHighBytes (by decide) (by
    intro c hc a len he
    simp only [Effect.components, List.map_cons, List.map_nil, Write.component_mem, List.append_nil, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · cases he; exact ⟨rfl, rfl⟩
    · cases he)) loaded10
  have w11 := MemWritable.of_holds e11 w10
  have r11b4 : ((Operand.reg 4 : Operand 64).read s11) = ((Operand.reg 4 : Operand 64).read s) := (e11.agrees.read (by simp <;> simp [Effect.components])).trans ((e10.agrees.read (by simp <;> simp [Effect.components])).trans ((e9.agrees.read (by simp <;> simp [Effect.components])).trans ((e8.agrees.read (by simp <;> simp [Effect.components])).trans ((e7.agrees.read (by simp <;> simp [Effect.components])).trans ((e6.agrees.read (by simp <;> simp [Effect.components])).trans ((e5.agrees.read (by simp <;> simp [Effect.components])).trans ((e4.agrees.read (by simp <;> simp [Effect.components])).trans ((e3.agrees.read (by simp <;> simp [Effect.components])).trans ((e2.agrees.read (by simp <;> simp [Effect.components])).trans ((e1.agrees.read (by simp <;> simp [Effect.components])).trans (rfl)))))))))))
  obtain ⟨s12, a12, ready12, e12⟩ :=
    (mov_r64_r64_effect_step 0x113d82 0x48 0xe6 (by simp [RexWPrefix]) (by decide)).advances ready11 (loaded11.mono (codeRange_slice_subset 0x113d5a borrowHighBytes 40 3))
      e11.rip (next 0x13d85 (by decide))
  change (movR64R64Effect 0x113d82 6 4 s11).Holds s11 s12 at e12
  have mx12 : s12.external = s11.external := e12.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])
  have m12 : s12.external = s11.external := mx12.trans m11
  have loaded12 := loaded11.of_external_eq mx12
  have w12 := MemWritable.of_holds e12 w11
  have v12r6 : ((Operand.reg 6 : Operand 64).read s12) = ((Operand.reg 4 : Operand 64).read s) := by
    have h : ((Operand.reg 6 : Operand 64).read s12) = ((Operand.reg 4 : Operand 64).read s11) := e12.writes
    rw [r11b4] at h
    exact h
  have r12b6 : ((Operand.reg 6 : Operand 64).read s12) = ((Operand.reg 4 : Operand 64).read s) := v12r6
  obtain ⟨s13, a13, ready13, e13⟩ :=
    (xor_r32_r32_effect_step 0x113d85 0xf6 (by decide)).advances ready12 (loaded12.mono (codeRange_slice_subset 0x113d5a borrowHighBytes 43 2))
      e12.rip (next 0x13d87 (by decide))
  change (xorR32R32Effect 0x113d85 2 6 6 s12).Holds s12 s13 at e13
  have mx13 : s13.external = s12.external := e13.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])
  have m13 : s13.external = s11.external := mx13.trans m12
  have loaded13 := loaded12.of_external_eq mx13
  have w13 := MemWritable.of_holds e13 w12
  have v13r6 : ((Operand.reg 6 : Operand 64).read s13) = (0 : BitVec 64) := by
    have h : ((Operand.reg 6 : Operand 64).read s13) = 0 := (by simpa only [xorR32R32Effect, BitVec.xor_self, BitVec.setWidth_zero, BitVec.ofNat_eq_ofNat, Write.AllHold] using e13.writes)
    exact h
  have r13b4 : ((Operand.reg 4 : Operand 64).read s13) = ((Operand.reg 4 : Operand 64).read s) := (e13.agrees.read (by simp <;> simp [Effect.components])).trans ((e12.agrees.read (by simp <;> simp [Effect.components])).trans ((e11.agrees.read (by simp <;> simp [Effect.components])).trans ((e10.agrees.read (by simp <;> simp [Effect.components])).trans ((e9.agrees.read (by simp <;> simp [Effect.components])).trans ((e8.agrees.read (by simp <;> simp [Effect.components])).trans ((e7.agrees.read (by simp <;> simp [Effect.components])).trans ((e6.agrees.read (by simp <;> simp [Effect.components])).trans ((e5.agrees.read (by simp <;> simp [Effect.components])).trans ((e4.agrees.read (by simp <;> simp [Effect.components])).trans ((e3.agrees.read (by simp <;> simp [Effect.components])).trans ((e2.agrees.read (by simp <;> simp [Effect.components])).trans ((e1.agrees.read (by simp <;> simp [Effect.components])).trans (rfl)))))))))))))
  have mr14 : MemReadable s13 (((Operand.reg 4 : Operand 64).read s13) + 0) 8 := by
    rw [r13b4]
    change MemReadable s13 (stackPtr s + 0#64) 8
    rw [BitVec.add_zero]
    exact w13.readable
  have mv14 : (Operand.mem (((Operand.reg 4 : Operand 64).read s13) + 0) : Operand 64).read s13 = v10 := by
    change memLoad _ _ 64 = _
    rw [r13b4]
    rw [show ((Operand.reg 4 : Operand 64).read s) + (0 : BitVec 64) = stackPtr s from BitVec.add_zero _, m13]
    exact e11.writes
  have r13b6 : ((Operand.reg 6 : Operand 64).read s13) = (0 : BitVec 64) := v13r6
  obtain ⟨s14, a14, ready14, e14⟩ :=
    (sub_r64_m64_effect_step 0x113d87 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 .none) (by decide) rfl rfl).advances ready13 (loaded13.mono (codeRange_slice_subset 0x113d5a borrowHighBytes 45 4))
      ⟨e13.rip, mr14⟩ (next 0x13d8b (by decide))
  change (subR64M64Effect 0x113d87 6 (.sib 4 none 0 .none) s13).Holds s13 s14 at e14
  have mx14 : s14.external = s13.external := e14.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])
  have m14 : s14.external = s11.external := mx14.trans m13
  have loaded14 := loaded13.of_external_eq mx14
  have w14 := MemWritable.of_holds e14 w13
  have v14r6 : ((Operand.reg 6 : Operand 64).read s14) = q14.1 := by
    have h : ((Operand.reg 6 : Operand 64).read s14) = (subSpec ((Operand.reg 6 : Operand 64).read s13) ((Operand.mem (((Operand.reg 4 : Operand 64).read s13) + 0) : Operand 64).read s13) ).1 := e14.writes
    rw [mv14, r13b6] at h
    exact h
  have c14 : (StatusFlags.ofRFLAGS s14.RFLAGS).CF = q14.2.CF := by
    have h : (StatusFlags.ofRFLAGS s14.RFLAGS).CF = (subSpec ((Operand.reg 6 : Operand 64).read s13) ((Operand.mem (((Operand.reg 4 : Operand 64).read s13) + 0) : Operand 64).read s13) ).2.CF := e14.flags.1
    rw [mv14, r13b6] at h
    exact h
  have r14b6 : ((Operand.reg 6 : Operand 64).read s14) = q14.1 := v14r6
  obtain ⟨s15, a15, ready15, e15⟩ :=
    (sar_r64_imm8_effect_step 0x113d8b 0x48 0xfe 63 (by simp [RexWPrefix]) (by decide) (by decide)).advances ready14 (loaded14.mono (codeRange_slice_subset 0x113d5a borrowHighBytes 49 4))
      e14.rip (next 0x13d8f (by decide))
  change (sarR64Effect 0x113d8b 4 6 63 s14).Holds s14 s15 at e15
  have mx15 : s15.external = s14.external := e15.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])
  have m15 : s15.external = s11.external := mx15.trans m14
  have loaded15 := loaded14.of_external_eq mx15
  have w15 := MemWritable.of_holds e15 w14
  have v15r6 : ((Operand.reg 6 : Operand 64).read s15) = v15 := by
    have h : ((Operand.reg 6 : Operand 64).read s15) = ((Operand.reg 6 : Operand 64).read s14).sshiftRight 63 := e15.writes
    rw [r14b6] at h
    exact h
  have r15b2 : ((Operand.reg 2 : Operand 64).read s15) = q6.1 := (e15.agrees.read (by simp <;> simp [Effect.components])).trans ((e14.agrees.read (by simp <;> simp [Effect.components])).trans ((e13.agrees.read (by simp <;> simp [Effect.components])).trans ((e12.agrees.read (by simp <;> simp [Effect.components])).trans ((e11.agrees.read (by simp <;> simp [Effect.components])).trans ((e10.agrees.read (by simp <;> simp [Effect.components])).trans ((e9.agrees.read (by simp <;> simp [Effect.components])).trans ((e8.agrees.read (by simp <;> simp [Effect.components])).trans ((e7.agrees.read (by simp <;> simp [Effect.components])).trans (v6r2)))))))))
  have r15b5 : ((Operand.reg 5 : Operand 64).read s15) = v4 := (e15.agrees.read (by simp <;> simp [Effect.components])).trans ((e14.agrees.read (by simp <;> simp [Effect.components])).trans ((e13.agrees.read (by simp <;> simp [Effect.components])).trans ((e12.agrees.read (by simp <;> simp [Effect.components])).trans ((e11.agrees.read (by simp <;> simp [Effect.components])).trans ((e10.agrees.read (by simp <;> simp [Effect.components])).trans ((e9.agrees.read (by simp <;> simp [Effect.components])).trans ((e8.agrees.read (by simp <;> simp [Effect.components])).trans ((e7.agrees.read (by simp <;> simp [Effect.components])).trans ((e6.agrees.read (by simp <;> simp [Effect.components])).trans ((e5.agrees.read (by simp <;> simp [Effect.components])).trans (v4r5)))))))))))
  have r15b6 : ((Operand.reg 6 : Operand 64).read s15) = v15 := v15r6
  have r15b10 : ((Operand.reg 10 : Operand 64).read s15) = q3.1 := (e15.agrees.read (by simp <;> simp [Effect.components])).trans ((e14.agrees.read (by simp <;> simp [Effect.components])).trans ((e13.agrees.read (by simp <;> simp [Effect.components])).trans ((e12.agrees.read (by simp <;> simp [Effect.components])).trans ((e11.agrees.read (by simp <;> simp [Effect.components])).trans ((e10.agrees.read (by simp <;> simp [Effect.components])).trans ((e9.agrees.read (by simp <;> simp [Effect.components])).trans ((e8.agrees.read (by simp <;> simp [Effect.components])).trans ((e7.agrees.read (by simp <;> simp [Effect.components])).trans ((e6.agrees.read (by simp <;> simp [Effect.components])).trans ((e5.agrees.read (by simp <;> simp [Effect.components])).trans ((e4.agrees.read (by simp <;> simp [Effect.components])).trans (v3r10))))))))))))
  have r15b15 : ((Operand.reg 15 : Operand 64).read s15) = v7 := (e15.agrees.read (by simp <;> simp [Effect.components])).trans ((e14.agrees.read (by simp <;> simp [Effect.components])).trans ((e13.agrees.read (by simp <;> simp [Effect.components])).trans ((e12.agrees.read (by simp <;> simp [Effect.components])).trans ((e11.agrees.read (by simp <;> simp [Effect.components])).trans ((e10.agrees.read (by simp <;> simp [Effect.components])).trans ((e9.agrees.read (by simp <;> simp [Effect.components])).trans ((e8.agrees.read (by simp <;> simp [Effect.components])).trans (v7r15))))))))
  refine ⟨15, s15, ((((((((((((((a1).trans a2).trans a3).trans a4).trans a5).trans a6).trans a7).trans a8).trans a9).trans a10).trans a11).trans a12).trans a13).trans a14).trans a15, ready15, loaded15, e15.rip, ?_, ?_, ?_⟩
  · refine ⟨r15b2, r15b5, r15b6, r15b10, r15b15, ?_⟩
    change memLoad s15.external (stackPtr s) 64 = _
    rw [m15]
    exact e11.writes
  · exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  · apply (((((((((((((((e1.agrees).trans e2.agrees).trans e3.agrees).trans e4.agrees).trans e5.agrees).trans e6.agrees).trans e7.agrees).trans e8.agrees).trans e9.agrees).trans e10.agrees).trans e11.agrees).trans e12.agrees).trans e13.agrees).trans e14.agrees).trans e15.agrees).mono
    simp only [movR32R32Effect_components, adcR64R64Effect_components, adcR64Imm8Effect_components, leaR64Effect_components, notR64Effect_components, andR64R64Effect_components, shrR64Effect_components, movR64R64Effect_components, xorR32R32Effect_components, subR64M64Effect_components, sarR64Effect_components]
    simp [borrowHighEffect, Effect.components, stackPtr, Operand.read_reg64]

theorem borrowHigh_bytes :
    Extracted.textBytes.toListFrom 0x13d5a borrowHighBytes.length = borrowHighBytes := by
  decide +kernel

end P256.Proofs.Field.Montgomery.Reduction
