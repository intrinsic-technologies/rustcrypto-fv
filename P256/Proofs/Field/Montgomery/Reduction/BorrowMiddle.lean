import P256.Proofs.Common.Field.Montgomery.Schoolbook.CarryCompose
import P256.Proofs.Common.Instructions.ShiftLeft.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import P256.Proofs.Program.Code
import P256.Proofs.Field.Montgomery.Reduction.Slot
import P256.Proofs.Common.Field.Operations.Neg.Borrow.Or

set_option autoImplicit false

open P256.Proofs.Common.Field.FieldNeg.Instructions (orR64R64Effect_components)
open P256.Proofs.Common.Field.Instructions (subR64M64Effect subR64M64Effect_components sub_r64_m64_effect_step)
open P256.Proofs.Common.Instructions (addR64M64Effect_components mulR64Effect_components sarR64Effect sarR64Effect_components sar_r64_imm8_effect_step)
open P256.Proofs.Common.Instructions.Carry (adcR64Imm8Effect_components adcR64M64Effect_components adcR64R64Effect_components)
open P256.Proofs.Common.Instructions.Setb (setccR8Effect_components)
open P256.Proofs.Common.Instructions.ShiftLeft (shlR64Effect_components)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Field.Montgomery.Reduction

open P256.Spec.Program.Routines
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

attribute [local simp] mulR64Effect_components adcR64R64Effect_components adcR64Imm8Effect_components
  adcR64M64Effect_components addR64M64Effect_components setccR8Effect_components shlR64Effect_components
  orR64R64Effect_components sarR64Effect_components subR64M64Effect_components

def borrowMiddleBytes : List UInt8 :=
  [0x4d, 0x1, 0xf8, 0x4d, 0x1, 0xd8, 0x49, 0xf7, 0xd7, 0x4d, 0x21, 0xc7, 0x49, 0xc1, 0xef, 0x3f, 0x4c, 0x89, 0x3c, 0x24, 0x49, 0x89, 0xe2, 0x45, 0x31, 0xd2, 0x4c, 0x2b, 0x14, 0x24, 0x49, 0xc1, 0xfa, 0x3f]

def borrowMiddleEffect (s : RamState) : Effect :=
  let q1 := addSpec ((Operand.reg 8 : Operand 64).read s) ((Operand.reg 15 : Operand 64).read s)
  let q2 := addSpec q1.1 ((Operand.reg 11 : Operand 64).read s)
  let v3 := ~~~((Operand.reg 15 : Operand 64).read s)
  let v4 := v3 &&& q2.1
  let v5 := v4 >>> 63
  let q9 := subSpec (0 : BitVec 64) v5
  let v10 := (q9.1).sshiftRight 63
  { rip := 0x113d5a
    writes := [⟨(.reg 8 : Operand 64), q2.1⟩,
      ⟨(.reg 10 : Operand 64), v10⟩,
      ⟨(.reg 15 : Operand 64), v5⟩,
      ⟨(.mem (stackPtr s) : Operand 64), v5⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem borrowMiddle_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (BorrowSlotPre 0x113d38) (codeRange 0x113d38 borrowMiddleBytes)
      (Effect.post borrowMiddleEffect) := by
  intro s ready loaded pre
  have next (offset : Nat) (h : offset < 118431) :=
    boundary_ne_program hout (inProgram_of_textOffset offset h)
  have code (offset len : Nat) := loaded.mono (codeRange_slice_subset 0x113d38 borrowMiddleBytes offset len)
  have loaded0 := loaded
  have w0 := pre.writable
  have m0 : s.external = s.external := rfl
  have c0 : (StatusFlags.ofRFLAGS s.RFLAGS).CF = (StatusFlags.ofRFLAGS s.RFLAGS).CF := rfl
  let q1 := addSpec ((Operand.reg 8 : Operand 64).read s) ((Operand.reg 15 : Operand 64).read s)
  let q2 := addSpec q1.1 ((Operand.reg 11 : Operand 64).read s)
  let v3 := ~~~((Operand.reg 15 : Operand 64).read s)
  let v4 := v3 &&& q2.1
  let v5 := v4 >>> 63
  let q9 := subSpec (0 : BitVec 64) v5
  let v10 := (q9.1).sshiftRight 63
  obtain ⟨s1, a1, ready1, e1⟩ :=
    (add_r64_r64_effect_step 0x113d38 0x4d 0xf8 (by simp [RexWPrefix]) (by decide)).advances ready (loaded0.mono (codeRange_slice_subset 0x113d38 borrowMiddleBytes 0 3))
      pre.rip (next 0x13d3b (by decide))
  change (addR64R64Effect 0x113d38 8 15 s).Holds s s1 at e1
  have mx1 : s1.external = s.external := e1.agrees.external (by simp [Component.Covers])
  have m1 : s1.external = s.external := mx1.trans m0
  have loaded1 := loaded0.of_external_eq mx1
  have w1 := MemWritable.of_holds e1 w0
  have v1r8 : ((Operand.reg 8 : Operand 64).read s1) = q1.1 := by
    have h : ((Operand.reg 8 : Operand 64).read s1) = (addSpec ((Operand.reg 8 : Operand 64).read s) ((Operand.reg 15 : Operand 64).read s) ).1 := e1.writes
    exact h
  have c1 : (StatusFlags.ofRFLAGS s1.RFLAGS).CF = q1.2.CF := by
    have h : (StatusFlags.ofRFLAGS s1.RFLAGS).CF = (addSpec ((Operand.reg 8 : Operand 64).read s) ((Operand.reg 15 : Operand 64).read s) ).2.CF := e1.flags.1
    exact h
  have r1b11 : ((Operand.reg 11 : Operand 64).read s1) = ((Operand.reg 11 : Operand 64).read s) := (e1.agrees.read (by simp <;> simp [Effect.components])).trans (rfl)
  have r1b8 : ((Operand.reg 8 : Operand 64).read s1) = q1.1 := v1r8
  obtain ⟨s2, a2, ready2, e2⟩ :=
    (add_r64_r64_effect_step 0x113d3b 0x4d 0xd8 (by simp [RexWPrefix]) (by decide)).advances ready1 (loaded1.mono (codeRange_slice_subset 0x113d38 borrowMiddleBytes 3 3))
      e1.rip (next 0x13d3e (by decide))
  change (addR64R64Effect 0x113d3b 8 11 s1).Holds s1 s2 at e2
  have mx2 : s2.external = s1.external := e2.agrees.external (by simp [Component.Covers])
  have m2 : s2.external = s.external := mx2.trans m1
  have loaded2 := loaded1.of_external_eq mx2
  have w2 := MemWritable.of_holds e2 w1
  have v2r8 : ((Operand.reg 8 : Operand 64).read s2) = q2.1 := by
    have h : ((Operand.reg 8 : Operand 64).read s2) = (addSpec ((Operand.reg 8 : Operand 64).read s1) ((Operand.reg 11 : Operand 64).read s1) ).1 := e2.writes
    rw [r1b11, r1b8] at h
    exact h
  have c2 : (StatusFlags.ofRFLAGS s2.RFLAGS).CF = q2.2.CF := by
    have h : (StatusFlags.ofRFLAGS s2.RFLAGS).CF = (addSpec ((Operand.reg 8 : Operand 64).read s1) ((Operand.reg 11 : Operand 64).read s1) ).2.CF := e2.flags.1
    rw [r1b11, r1b8] at h
    exact h
  have r2b15 : ((Operand.reg 15 : Operand 64).read s2) = ((Operand.reg 15 : Operand 64).read s) := (e2.agrees.read (by simp <;> simp [Effect.components])).trans ((e1.agrees.read (by simp <;> simp [Effect.components])).trans (rfl))
  obtain ⟨s3, a3, ready3, e3⟩ :=
    (not_r64_effect_step 0x113d3e 0x49 0xd7 (by simp [RexWPrefix]) (by decide) (by decide)).advances ready2 (loaded2.mono (codeRange_slice_subset 0x113d38 borrowMiddleBytes 6 3))
      e2.rip (next 0x13d41 (by decide))
  change (notR64Effect 0x113d3e 15 s2).Holds s2 s3 at e3
  have mx3 : s3.external = s2.external := e3.agrees.external (by simp [Component.Covers])
  have m3 : s3.external = s.external := mx3.trans m2
  have loaded3 := loaded2.of_external_eq mx3
  have w3 := MemWritable.of_holds e3 w2
  have v3r15 : ((Operand.reg 15 : Operand 64).read s3) = v3 := by
    have h : ((Operand.reg 15 : Operand 64).read s3) = ~~~((Operand.reg 15 : Operand 64).read s2) := e3.writes
    rw [r2b15] at h
    exact h
  have r3b8 : ((Operand.reg 8 : Operand 64).read s3) = q2.1 := (e3.agrees.read (by simp <;> simp [Effect.components])).trans (v2r8)
  have r3b15 : ((Operand.reg 15 : Operand 64).read s3) = v3 := v3r15
  obtain ⟨s4, a4, ready4, e4⟩ :=
    (and_r64_r64_effect_step 0x113d41 0x4d 0xc7 (by simp [RexWPrefix]) (by decide)).advances ready3 (loaded3.mono (codeRange_slice_subset 0x113d38 borrowMiddleBytes 9 3))
      e3.rip (next 0x13d44 (by decide))
  change (andR64R64Effect 0x113d41 15 8 s3).Holds s3 s4 at e4
  have mx4 : s4.external = s3.external := e4.agrees.external (by simp [Component.Covers])
  have m4 : s4.external = s.external := mx4.trans m3
  have loaded4 := loaded3.of_external_eq mx4
  have w4 := MemWritable.of_holds e4 w3
  have v4r15 : ((Operand.reg 15 : Operand 64).read s4) = v4 := by
    have h : ((Operand.reg 15 : Operand 64).read s4) = ((Operand.reg 15 : Operand 64).read s3) &&& ((Operand.reg 8 : Operand 64).read s3) := e4.writes
    rw [r3b8, r3b15] at h
    exact h
  have r4b15 : ((Operand.reg 15 : Operand 64).read s4) = v4 := v4r15
  obtain ⟨s5, a5, ready5, e5⟩ :=
    (shr_r64_imm8_effect_step 0x113d44 0x49 0xef 63 (by simp [RexWPrefix]) (by decide) (by decide)).advances ready4 (loaded4.mono (codeRange_slice_subset 0x113d38 borrowMiddleBytes 12 4))
      e4.rip (next 0x13d48 (by decide))
  change (shrR64Effect 0x113d44 4 15 63 s4).Holds s4 s5 at e5
  have mx5 : s5.external = s4.external := e5.agrees.external (by simp [Component.Covers])
  have m5 : s5.external = s.external := mx5.trans m4
  have loaded5 := loaded4.of_external_eq mx5
  have w5 := MemWritable.of_holds e5 w4
  have v5r15 : ((Operand.reg 15 : Operand 64).read s5) = v5 := by
    have h : ((Operand.reg 15 : Operand 64).read s5) = ((Operand.reg 15 : Operand 64).read s4) >>> 63 := e5.writes
    rw [r4b15] at h
    exact h
  have r5b15 : ((Operand.reg 15 : Operand 64).read s5) = v5 := v5r15
  have r5b4 : ((Operand.reg 4 : Operand 64).read s5) = ((Operand.reg 4 : Operand 64).read s) := (e5.agrees.read (by simp <;> simp [Effect.components])).trans ((e4.agrees.read (by simp <;> simp [Effect.components])).trans ((e3.agrees.read (by simp <;> simp [Effect.components])).trans ((e2.agrees.read (by simp <;> simp [Effect.components])).trans ((e1.agrees.read (by simp <;> simp [Effect.components])).trans (rfl)))))
  have st6 : StorePre 0x113d48 4 (fun t => ((Operand.reg 4 : Operand 64).read t) + 0) 8 s5 := by
    refine ⟨e5.rip, ?_, ?_⟩
    · rw [r5b4]
      change MemWritable s5 (stackPtr s + 0#64) 8
      rw [BitVec.add_zero]
      exact w5
    · rw [r5b4]
      change RangeApart (stackPtr s + 0#64) 8 0x113d48 4
      rw [BitVec.add_zero]
      exact pre.apart 0x13d48 4 (by decide)
  obtain ⟨s6, a6, ready6, e6⟩ :=
    (mov_m64_r64_effect_step 0x113d48 0x4c (by simp [RexWPrefix]) 7 (.sib 4 none 0 .none) (by decide) rfl rfl).advances ready5 (loaded5.mono (codeRange_slice_subset 0x113d38 borrowMiddleBytes 16 4))
      st6 (next 0x13d4c (by decide))
  change (movM64R64Effect 0x113d48 15 (.sib 4 none 0 .none) s5).Holds s5 s6 at e6
  change ({ rip := 0x113d4c, writes := [⟨(.mem (((Operand.reg 4 : Operand 64).read s5) + 0) : Operand 64), ((Operand.reg 15 : Operand 64).read s5)⟩] } : Effect).Holds s5 s6 at e6
  rw [r5b4] at e6
  rw [r5b15] at e6
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at e6
  have m6 : s6.external = s6.external := rfl
  have loaded6 := e6.codeIn (pre.avoids_code 0x13d38 borrowMiddleBytes (by decide) (by
    intro c hc a len he
    simp only [Effect.components, List.map_cons, List.map_nil, Write.component_mem, List.append_nil, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · cases he; exact ⟨rfl, rfl⟩
    · cases he)) loaded5
  have w6 := MemWritable.of_holds e6 w5
  have r6b4 : ((Operand.reg 4 : Operand 64).read s6) = ((Operand.reg 4 : Operand 64).read s) := (e6.agrees.read (by simp <;> simp [Effect.components])).trans ((e5.agrees.read (by simp <;> simp [Effect.components])).trans ((e4.agrees.read (by simp <;> simp [Effect.components])).trans ((e3.agrees.read (by simp <;> simp [Effect.components])).trans ((e2.agrees.read (by simp <;> simp [Effect.components])).trans ((e1.agrees.read (by simp <;> simp [Effect.components])).trans (rfl))))))
  obtain ⟨s7, a7, ready7, e7⟩ :=
    (mov_r64_r64_effect_step 0x113d4c 0x49 0xe2 (by simp [RexWPrefix]) (by decide)).advances ready6 (loaded6.mono (codeRange_slice_subset 0x113d38 borrowMiddleBytes 20 3))
      e6.rip (next 0x13d4f (by decide))
  change (movR64R64Effect 0x113d4c 10 4 s6).Holds s6 s7 at e7
  have mx7 : s7.external = s6.external := e7.agrees.external (by simp [Component.Covers])
  have m7 : s7.external = s6.external := mx7.trans m6
  have loaded7 := loaded6.of_external_eq mx7
  have w7 := MemWritable.of_holds e7 w6
  have v7r10 : ((Operand.reg 10 : Operand 64).read s7) = ((Operand.reg 4 : Operand 64).read s) := by
    have h : ((Operand.reg 10 : Operand 64).read s7) = ((Operand.reg 4 : Operand 64).read s6) := e7.writes
    rw [r6b4] at h
    exact h
  have r7b10 : ((Operand.reg 10 : Operand 64).read s7) = ((Operand.reg 4 : Operand 64).read s) := v7r10
  obtain ⟨s8, a8, ready8, e8⟩ :=
    (xor_r32_r32_rex_effect_step 0x113d4f 0x45 0xd2 (by simp [RexNoWPrefix]) (by decide)).advances ready7 (loaded7.mono (codeRange_slice_subset 0x113d38 borrowMiddleBytes 23 3))
      e7.rip (next 0x13d52 (by decide))
  change (xorR32R32Effect 0x113d4f 3 10 10 s7).Holds s7 s8 at e8
  have mx8 : s8.external = s7.external := e8.agrees.external (by simp [Component.Covers])
  have m8 : s8.external = s6.external := mx8.trans m7
  have loaded8 := loaded7.of_external_eq mx8
  have w8 := MemWritable.of_holds e8 w7
  have v8r10 : ((Operand.reg 10 : Operand 64).read s8) = (0 : BitVec 64) := by
    have h : ((Operand.reg 10 : Operand 64).read s8) = 0 := (by simpa only [xorR32R32Effect, BitVec.xor_self, BitVec.setWidth_zero, BitVec.ofNat_eq_ofNat, Write.AllHold] using e8.writes)
    exact h
  have r8b4 : ((Operand.reg 4 : Operand 64).read s8) = ((Operand.reg 4 : Operand 64).read s) := (e8.agrees.read (by simp <;> simp [Effect.components])).trans ((e7.agrees.read (by simp <;> simp [Effect.components])).trans ((e6.agrees.read (by simp <;> simp [Effect.components])).trans ((e5.agrees.read (by simp <;> simp [Effect.components])).trans ((e4.agrees.read (by simp <;> simp [Effect.components])).trans ((e3.agrees.read (by simp <;> simp [Effect.components])).trans ((e2.agrees.read (by simp <;> simp [Effect.components])).trans ((e1.agrees.read (by simp <;> simp [Effect.components])).trans (rfl))))))))
  have mr9 : MemReadable s8 (((Operand.reg 4 : Operand 64).read s8) + 0) 8 := by
    rw [r8b4]
    change MemReadable s8 (stackPtr s + 0#64) 8
    rw [BitVec.add_zero]
    exact w8.readable
  have mv9 : (Operand.mem (((Operand.reg 4 : Operand 64).read s8) + 0) : Operand 64).read s8 = v5 := by
    change memLoad _ _ 64 = _
    rw [r8b4]
    rw [show ((Operand.reg 4 : Operand 64).read s) + (0 : BitVec 64) = stackPtr s from BitVec.add_zero _, m8]
    exact e6.writes
  have r8b10 : ((Operand.reg 10 : Operand 64).read s8) = (0 : BitVec 64) := v8r10
  obtain ⟨s9, a9, ready9, e9⟩ :=
    (sub_r64_m64_effect_step 0x113d52 0x4c (by simp [RexWPrefix]) 2 (.sib 4 none 0 .none) (by decide) rfl rfl).advances ready8 (loaded8.mono (codeRange_slice_subset 0x113d38 borrowMiddleBytes 26 4))
      ⟨e8.rip, mr9⟩ (next 0x13d56 (by decide))
  change (subR64M64Effect 0x113d52 10 (.sib 4 none 0 .none) s8).Holds s8 s9 at e9
  have mx9 : s9.external = s8.external := e9.agrees.external (by simp [Component.Covers])
  have m9 : s9.external = s6.external := mx9.trans m8
  have loaded9 := loaded8.of_external_eq mx9
  have w9 := MemWritable.of_holds e9 w8
  have v9r10 : ((Operand.reg 10 : Operand 64).read s9) = q9.1 := by
    have h : ((Operand.reg 10 : Operand 64).read s9) = (subSpec ((Operand.reg 10 : Operand 64).read s8) ((Operand.mem (((Operand.reg 4 : Operand 64).read s8) + 0) : Operand 64).read s8) ).1 := e9.writes
    rw [mv9, r8b10] at h
    exact h
  have c9 : (StatusFlags.ofRFLAGS s9.RFLAGS).CF = q9.2.CF := by
    have h : (StatusFlags.ofRFLAGS s9.RFLAGS).CF = (subSpec ((Operand.reg 10 : Operand 64).read s8) ((Operand.mem (((Operand.reg 4 : Operand 64).read s8) + 0) : Operand 64).read s8) ).2.CF := e9.flags.1
    rw [mv9, r8b10] at h
    exact h
  have r9b10 : ((Operand.reg 10 : Operand 64).read s9) = q9.1 := v9r10
  obtain ⟨s10, a10, ready10, e10⟩ :=
    (sar_r64_imm8_effect_step 0x113d56 0x49 0xfa 63 (by simp [RexWPrefix]) (by decide) (by decide)).advances ready9 (loaded9.mono (codeRange_slice_subset 0x113d38 borrowMiddleBytes 30 4))
      e9.rip (next 0x13d5a (by decide))
  change (sarR64Effect 0x113d56 4 10 63 s9).Holds s9 s10 at e10
  have mx10 : s10.external = s9.external := e10.agrees.external (by simp [Component.Covers])
  have m10 : s10.external = s6.external := mx10.trans m9
  have loaded10 := loaded9.of_external_eq mx10
  have w10 := MemWritable.of_holds e10 w9
  have v10r10 : ((Operand.reg 10 : Operand 64).read s10) = v10 := by
    have h : ((Operand.reg 10 : Operand 64).read s10) = ((Operand.reg 10 : Operand 64).read s9).sshiftRight 63 := e10.writes
    rw [r9b10] at h
    exact h
  have r10b8 : ((Operand.reg 8 : Operand 64).read s10) = q2.1 := (e10.agrees.read (by simp <;> simp [Effect.components])).trans ((e9.agrees.read (by simp <;> simp [Effect.components])).trans ((e8.agrees.read (by simp <;> simp [Effect.components])).trans ((e7.agrees.read (by simp <;> simp [Effect.components])).trans ((e6.agrees.read (by simp <;> simp [Effect.components])).trans ((e5.agrees.read (by simp <;> simp [Effect.components])).trans ((e4.agrees.read (by simp <;> simp [Effect.components])).trans ((e3.agrees.read (by simp <;> simp [Effect.components])).trans (v2r8))))))))
  have r10b10 : ((Operand.reg 10 : Operand 64).read s10) = v10 := v10r10
  have r10b15 : ((Operand.reg 15 : Operand 64).read s10) = v5 := (e10.agrees.read (by simp <;> simp [Effect.components])).trans ((e9.agrees.read (by simp <;> simp [Effect.components])).trans ((e8.agrees.read (by simp <;> simp [Effect.components])).trans ((e7.agrees.read (by simp <;> simp [Effect.components])).trans ((e6.agrees.read (by simp <;> simp [Effect.components])).trans (v5r15)))))
  refine ⟨10, s10, (((((((((a1).trans a2).trans a3).trans a4).trans a5).trans a6).trans a7).trans a8).trans a9).trans a10, ready10, loaded10, e10.rip, ?_, ?_, ?_⟩
  · refine ⟨r10b8, r10b10, r10b15, ?_⟩
    change memLoad s10.external (stackPtr s) 64 = _
    rw [m10]
    exact e6.writes
  · exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  · apply ((((((((((e1.agrees).trans e2.agrees).trans e3.agrees).trans e4.agrees).trans e5.agrees).trans e6.agrees).trans e7.agrees).trans e8.agrees).trans e9.agrees).trans e10.agrees).mono
    simp only [addR64R64Effect_components, notR64Effect_components, andR64R64Effect_components, shrR64Effect_components, movR64R64Effect_components, xorR32R32Effect_components, subR64M64Effect_components, sarR64Effect_components]
    simp [borrowMiddleEffect, Effect.components, stackPtr, Operand.read_reg64]

theorem borrowMiddle_bytes :
    Extracted.textBytes.toListFrom 0x13d38 borrowMiddleBytes.length = borrowMiddleBytes := by
  decide +kernel

end P256.Proofs.Field.Montgomery.Reduction
