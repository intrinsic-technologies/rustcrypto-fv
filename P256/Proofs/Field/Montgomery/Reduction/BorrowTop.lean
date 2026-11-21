import P256.Proofs.Common.Field.Montgomery.Schoolbook.CarryCompose
import P256.Proofs.Common.Instructions.ShiftLeft.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import P256.Proofs.Program.Code
import P256.Proofs.Common.Instructions.MovzxByte
import P256.Proofs.Common.Instructions.Neg64
import P256.Proofs.Field.Montgomery.Reduction.Slot
import P256.Proofs.Common.Field.Operations.Neg.Borrow.Or

set_option autoImplicit false

open P256.Proofs.Common.Field.FieldNeg.Instructions (orR64R64Effect orR64R64Effect_components or_r64_r64_effect_step)
open P256.Proofs.Common.Field.Instructions (subR64M64Effect subR64M64Effect_components sub_r64_m64_effect_step)
open P256.Proofs.Common.Instructions (addR64M64Effect_components mulR64Effect_components sarR64Effect sarR64Effect_components sar_r64_imm8_effect_step)
open P256.Proofs.Common.Instructions.AddByte (addR8Imm8Effect)
open P256.Proofs.Common.Instructions.Carry (adcR64Imm8Effect_components adcR64M64Effect_components adcR64R64Effect adcR64R64Effect_components adcSpec adc_r64_r64_effect_step)
open P256.Proofs.Common.Instructions.MovzxByte (movzxR32R8Effect movzx_r32_r8_effect_step)
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

def borrowTopBytes : List UInt8 :=
  [0x4c, 0x1, 0xfe, 0x48, 0x1, 0xde, 0x49, 0xf7, 0xd7, 0x49, 0x9, 0xf7, 0x49, 0xc1, 0xef, 0x3f, 0x4c, 0x89, 0x3c, 0x24, 0x48, 0x89, 0xe3, 0x4c, 0x2b, 0x34, 0x24, 0x49, 0xc1, 0xfe, 0x3f, 0x4c, 0x1, 0xca, 0xf, 0xb6, 0xc9, 0x4c, 0x11, 0xf1, 0x48, 0xc1, 0xe9, 0x3f, 0x48, 0x89, 0xc, 0x24, 0x48, 0x89, 0xe1, 0x48, 0x8b, 0xc, 0x24]

def borrowTopEffect (s : RamState) : Effect :=
  let q1 := addSpec ((Operand.reg 6 : Operand 64).read s) ((Operand.reg 15 : Operand 64).read s)
  let q2 := addSpec q1.1 ((Operand.reg 3 : Operand 64).read s)
  let v3 := ~~~((Operand.reg 15 : Operand 64).read s)
  let v4 := v3 ||| q2.1
  let v5 := v4 >>> 63
  let q8 := subSpec ((Operand.reg 14 : Operand 64).read s) v5
  let v9 := (q8.1).sshiftRight 63
  let q10 := addSpec ((Operand.reg 2 : Operand 64).read s) ((Operand.reg 9 : Operand 64).read s)
  let v11 := (((Operand.reg 1 : Operand 64).read s).setWidth 8).setWidth 64
  let q12 := adcSpec v11 v9 (BitVec.ofBool q10.2.CF)
  let v13 := q12.1 >>> 63
  { rip := 0x113dc6
    writes := [⟨(.reg 1 : Operand 64), v13⟩,
      ⟨(.reg 2 : Operand 64), q10.1⟩,
      ⟨(.reg 3 : Operand 64), ((Operand.reg 4 : Operand 64).read s)⟩,
      ⟨(.reg 6 : Operand 64), q2.1⟩,
      ⟨(.reg 14 : Operand 64), v9⟩,
      ⟨(.reg 15 : Operand 64), v5⟩,
      ⟨(.mem (stackPtr s) : Operand 64), v13⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem borrowTop_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (BorrowSlotPre 0x113d8f) (codeRange 0x113d8f borrowTopBytes)
      (Effect.post borrowTopEffect) := by
  intro s ready loaded pre
  have next (offset : Nat) (h : offset < 118431) :=
    boundary_ne_program hout (inProgram_of_textOffset offset h)
  have code (offset len : Nat) := loaded.mono (codeRange_slice_subset 0x113d8f borrowTopBytes offset len)
  have loaded0 := loaded
  have w0 := pre.writable
  have m0 : s.external = s.external := rfl
  have c0 : (StatusFlags.ofRFLAGS s.RFLAGS).CF = (StatusFlags.ofRFLAGS s.RFLAGS).CF := rfl
  let q1 := addSpec ((Operand.reg 6 : Operand 64).read s) ((Operand.reg 15 : Operand 64).read s)
  let q2 := addSpec q1.1 ((Operand.reg 3 : Operand 64).read s)
  let v3 := ~~~((Operand.reg 15 : Operand 64).read s)
  let v4 := v3 ||| q2.1
  let v5 := v4 >>> 63
  let q8 := subSpec ((Operand.reg 14 : Operand 64).read s) v5
  let v9 := (q8.1).sshiftRight 63
  let q10 := addSpec ((Operand.reg 2 : Operand 64).read s) ((Operand.reg 9 : Operand 64).read s)
  let v11 := (((Operand.reg 1 : Operand 64).read s).setWidth 8).setWidth 64
  let q12 := adcSpec v11 v9 (BitVec.ofBool q10.2.CF)
  let v13 := q12.1 >>> 63
  obtain ⟨s1, a1, ready1, e1⟩ :=
    (add_r64_r64_effect_step 0x113d8f 0x4c 0xfe (by simp [RexWPrefix]) (by decide)).advances ready (loaded0.mono (codeRange_slice_subset 0x113d8f borrowTopBytes 0 3))
      pre.rip (next 0x13d92 (by decide))
  change (addR64R64Effect 0x113d8f 6 15 s).Holds s s1 at e1
  have mx1 : s1.external = s.external := e1.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])
  have m1 : s1.external = s.external := mx1.trans m0
  have loaded1 := loaded0.of_external_eq mx1
  have w1 := MemWritable.of_holds e1 w0
  have v1r6 : ((Operand.reg 6 : Operand 64).read s1) = q1.1 := by
    have h : ((Operand.reg 6 : Operand 64).read s1) = (addSpec ((Operand.reg 6 : Operand 64).read s) ((Operand.reg 15 : Operand 64).read s) ).1 := e1.writes
    exact h
  have c1 : (StatusFlags.ofRFLAGS s1.RFLAGS).CF = q1.2.CF := by
    have h : (StatusFlags.ofRFLAGS s1.RFLAGS).CF = (addSpec ((Operand.reg 6 : Operand 64).read s) ((Operand.reg 15 : Operand 64).read s) ).2.CF := e1.flags.1
    exact h
  have r1b3 : ((Operand.reg 3 : Operand 64).read s1) = ((Operand.reg 3 : Operand 64).read s) := (e1.agrees.read (by simp <;> simp [Effect.components])).trans (rfl)
  have r1b6 : ((Operand.reg 6 : Operand 64).read s1) = q1.1 := v1r6
  obtain ⟨s2, a2, ready2, e2⟩ :=
    (add_r64_r64_effect_step 0x113d92 0x48 0xde (by simp [RexWPrefix]) (by decide)).advances ready1 (loaded1.mono (codeRange_slice_subset 0x113d8f borrowTopBytes 3 3))
      e1.rip (next 0x13d95 (by decide))
  change (addR64R64Effect 0x113d92 6 3 s1).Holds s1 s2 at e2
  have mx2 : s2.external = s1.external := e2.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])
  have m2 : s2.external = s.external := mx2.trans m1
  have loaded2 := loaded1.of_external_eq mx2
  have w2 := MemWritable.of_holds e2 w1
  have v2r6 : ((Operand.reg 6 : Operand 64).read s2) = q2.1 := by
    have h : ((Operand.reg 6 : Operand 64).read s2) = (addSpec ((Operand.reg 6 : Operand 64).read s1) ((Operand.reg 3 : Operand 64).read s1) ).1 := e2.writes
    rw [r1b3, r1b6] at h
    exact h
  have c2 : (StatusFlags.ofRFLAGS s2.RFLAGS).CF = q2.2.CF := by
    have h : (StatusFlags.ofRFLAGS s2.RFLAGS).CF = (addSpec ((Operand.reg 6 : Operand 64).read s1) ((Operand.reg 3 : Operand 64).read s1) ).2.CF := e2.flags.1
    rw [r1b3, r1b6] at h
    exact h
  have r2b15 : ((Operand.reg 15 : Operand 64).read s2) = ((Operand.reg 15 : Operand 64).read s) := (e2.agrees.read (by simp <;> simp [Effect.components])).trans ((e1.agrees.read (by simp <;> simp [Effect.components])).trans (rfl))
  obtain ⟨s3, a3, ready3, e3⟩ :=
    (not_r64_effect_step 0x113d95 0x49 0xd7 (by simp [RexWPrefix]) (by decide) (by decide)).advances ready2 (loaded2.mono (codeRange_slice_subset 0x113d8f borrowTopBytes 6 3))
      e2.rip (next 0x13d98 (by decide))
  change (notR64Effect 0x113d95 15 s2).Holds s2 s3 at e3
  have mx3 : s3.external = s2.external := e3.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])
  have m3 : s3.external = s.external := mx3.trans m2
  have loaded3 := loaded2.of_external_eq mx3
  have w3 := MemWritable.of_holds e3 w2
  have v3r15 : ((Operand.reg 15 : Operand 64).read s3) = v3 := by
    have h : ((Operand.reg 15 : Operand 64).read s3) = ~~~((Operand.reg 15 : Operand 64).read s2) := e3.writes
    rw [r2b15] at h
    exact h
  have r3b6 : ((Operand.reg 6 : Operand 64).read s3) = q2.1 := (e3.agrees.read (by simp <;> simp [Effect.components])).trans (v2r6)
  have r3b15 : ((Operand.reg 15 : Operand 64).read s3) = v3 := v3r15
  obtain ⟨s4, a4, ready4, e4⟩ :=
    (or_r64_r64_effect_step 0x113d98 0x49 0xf7 (by simp [RexWPrefix]) (by decide)).advances ready3 (loaded3.mono (codeRange_slice_subset 0x113d8f borrowTopBytes 9 3))
      e3.rip (next 0x13d9b (by decide))
  change (orR64R64Effect 0x113d98 15 6 s3).Holds s3 s4 at e4
  have mx4 : s4.external = s3.external := e4.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])
  have m4 : s4.external = s.external := mx4.trans m3
  have loaded4 := loaded3.of_external_eq mx4
  have w4 := MemWritable.of_holds e4 w3
  have v4r15 : ((Operand.reg 15 : Operand 64).read s4) = v4 := by
    have h : ((Operand.reg 15 : Operand 64).read s4) = ((Operand.reg 15 : Operand 64).read s3) ||| ((Operand.reg 6 : Operand 64).read s3) := e4.writes
    rw [r3b6, r3b15] at h
    exact h
  have r4b15 : ((Operand.reg 15 : Operand 64).read s4) = v4 := v4r15
  obtain ⟨s5, a5, ready5, e5⟩ :=
    (shr_r64_imm8_effect_step 0x113d9b 0x49 0xef 63 (by simp [RexWPrefix]) (by decide) (by decide)).advances ready4 (loaded4.mono (codeRange_slice_subset 0x113d8f borrowTopBytes 12 4))
      e4.rip (next 0x13d9f (by decide))
  change (shrR64Effect 0x113d9b 4 15 63 s4).Holds s4 s5 at e5
  have mx5 : s5.external = s4.external := e5.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])
  have m5 : s5.external = s.external := mx5.trans m4
  have loaded5 := loaded4.of_external_eq mx5
  have w5 := MemWritable.of_holds e5 w4
  have v5r15 : ((Operand.reg 15 : Operand 64).read s5) = v5 := by
    have h : ((Operand.reg 15 : Operand 64).read s5) = ((Operand.reg 15 : Operand 64).read s4) >>> 63 := e5.writes
    rw [r4b15] at h
    exact h
  have r5b15 : ((Operand.reg 15 : Operand 64).read s5) = v5 := v5r15
  have r5b4 : ((Operand.reg 4 : Operand 64).read s5) = ((Operand.reg 4 : Operand 64).read s) := (e5.agrees.read (by simp <;> simp [Effect.components])).trans ((e4.agrees.read (by simp <;> simp [Effect.components])).trans ((e3.agrees.read (by simp <;> simp [Effect.components])).trans ((e2.agrees.read (by simp <;> simp [Effect.components])).trans ((e1.agrees.read (by simp <;> simp [Effect.components])).trans (rfl)))))
  have st6 : StorePre 0x113d9f 4 (fun t => ((Operand.reg 4 : Operand 64).read t) + 0) 8 s5 := by
    refine ⟨e5.rip, ?_, ?_⟩
    · rw [r5b4]
      change MemWritable s5 (stackPtr s + 0#64) 8
      rw [BitVec.add_zero]
      exact w5
    · rw [r5b4]
      change RangeApart (stackPtr s + 0#64) 8 0x113d9f 4
      rw [BitVec.add_zero]
      exact pre.apart 0x13d9f 4 (by decide)
  obtain ⟨s6, a6, ready6, e6⟩ :=
    (mov_m64_r64_effect_step 0x113d9f 0x4c (by simp [RexWPrefix]) 7 (.sib 4 none 0 .none) (by decide) rfl rfl).advances ready5 (loaded5.mono (codeRange_slice_subset 0x113d8f borrowTopBytes 16 4))
      st6 (next 0x13da3 (by decide))
  change (movM64R64Effect 0x113d9f 15 (.sib 4 none 0 .none) s5).Holds s5 s6 at e6
  change ({ rip := 0x113da3, writes := [⟨(.mem (((Operand.reg 4 : Operand 64).read s5) + 0) : Operand 64), ((Operand.reg 15 : Operand 64).read s5)⟩] } : Effect).Holds s5 s6 at e6
  rw [r5b4] at e6
  rw [r5b15] at e6
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at e6
  have m6 : s6.external = s6.external := rfl
  have loaded6 := e6.codeIn (pre.avoids_code 0x13d8f borrowTopBytes (by decide) (by
    intro c hc a len he
    simp only [Effect.components, List.map_cons, List.map_nil, Write.component_mem, List.append_nil, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · cases he; exact ⟨rfl, rfl⟩
    · cases he)) loaded5
  have w6 := MemWritable.of_holds e6 w5
  have r6b4 : ((Operand.reg 4 : Operand 64).read s6) = ((Operand.reg 4 : Operand 64).read s) := (e6.agrees.read (by simp <;> simp [Effect.components])).trans ((e5.agrees.read (by simp <;> simp [Effect.components])).trans ((e4.agrees.read (by simp <;> simp [Effect.components])).trans ((e3.agrees.read (by simp <;> simp [Effect.components])).trans ((e2.agrees.read (by simp <;> simp [Effect.components])).trans ((e1.agrees.read (by simp <;> simp [Effect.components])).trans (rfl))))))
  obtain ⟨s7, a7, ready7, e7⟩ :=
    (mov_r64_r64_effect_step 0x113da3 0x48 0xe3 (by simp [RexWPrefix]) (by decide)).advances ready6 (loaded6.mono (codeRange_slice_subset 0x113d8f borrowTopBytes 20 3))
      e6.rip (next 0x13da6 (by decide))
  change (movR64R64Effect 0x113da3 3 4 s6).Holds s6 s7 at e7
  have mx7 : s7.external = s6.external := e7.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])
  have m7 : s7.external = s6.external := mx7.trans m6
  have loaded7 := loaded6.of_external_eq mx7
  have w7 := MemWritable.of_holds e7 w6
  have v7r3 : ((Operand.reg 3 : Operand 64).read s7) = ((Operand.reg 4 : Operand 64).read s) := by
    have h : ((Operand.reg 3 : Operand 64).read s7) = ((Operand.reg 4 : Operand 64).read s6) := e7.writes
    rw [r6b4] at h
    exact h
  have r7b4 : ((Operand.reg 4 : Operand 64).read s7) = ((Operand.reg 4 : Operand 64).read s) := (e7.agrees.read (by simp <;> simp [Effect.components])).trans ((e6.agrees.read (by simp <;> simp [Effect.components])).trans ((e5.agrees.read (by simp <;> simp [Effect.components])).trans ((e4.agrees.read (by simp <;> simp [Effect.components])).trans ((e3.agrees.read (by simp <;> simp [Effect.components])).trans ((e2.agrees.read (by simp <;> simp [Effect.components])).trans ((e1.agrees.read (by simp <;> simp [Effect.components])).trans (rfl)))))))
  have mr8 : MemReadable s7 (((Operand.reg 4 : Operand 64).read s7) + 0) 8 := by
    rw [r7b4]
    change MemReadable s7 (stackPtr s + 0#64) 8
    rw [BitVec.add_zero]
    exact w7.readable
  have mv8 : (Operand.mem (((Operand.reg 4 : Operand 64).read s7) + 0) : Operand 64).read s7 = v5 := by
    change memLoad _ _ 64 = _
    rw [r7b4]
    rw [show ((Operand.reg 4 : Operand 64).read s) + (0 : BitVec 64) = stackPtr s from BitVec.add_zero _, m7]
    exact e6.writes
  have r7b14 : ((Operand.reg 14 : Operand 64).read s7) = ((Operand.reg 14 : Operand 64).read s) := (e7.agrees.read (by simp <;> simp [Effect.components])).trans ((e6.agrees.read (by simp <;> simp [Effect.components])).trans ((e5.agrees.read (by simp <;> simp [Effect.components])).trans ((e4.agrees.read (by simp <;> simp [Effect.components])).trans ((e3.agrees.read (by simp <;> simp [Effect.components])).trans ((e2.agrees.read (by simp <;> simp [Effect.components])).trans ((e1.agrees.read (by simp <;> simp [Effect.components])).trans (rfl)))))))
  obtain ⟨s8, a8, ready8, e8⟩ :=
    (sub_r64_m64_effect_step 0x113da6 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 .none) (by decide) rfl rfl).advances ready7 (loaded7.mono (codeRange_slice_subset 0x113d8f borrowTopBytes 23 4))
      ⟨e7.rip, mr8⟩ (next 0x13daa (by decide))
  change (subR64M64Effect 0x113da6 14 (.sib 4 none 0 .none) s7).Holds s7 s8 at e8
  have mx8 : s8.external = s7.external := e8.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])
  have m8 : s8.external = s6.external := mx8.trans m7
  have loaded8 := loaded7.of_external_eq mx8
  have w8 := MemWritable.of_holds e8 w7
  have v8r14 : ((Operand.reg 14 : Operand 64).read s8) = q8.1 := by
    have h : ((Operand.reg 14 : Operand 64).read s8) = (subSpec ((Operand.reg 14 : Operand 64).read s7) ((Operand.mem (((Operand.reg 4 : Operand 64).read s7) + 0) : Operand 64).read s7) ).1 := e8.writes
    rw [mv8, r7b14] at h
    exact h
  have c8 : (StatusFlags.ofRFLAGS s8.RFLAGS).CF = q8.2.CF := by
    have h : (StatusFlags.ofRFLAGS s8.RFLAGS).CF = (subSpec ((Operand.reg 14 : Operand 64).read s7) ((Operand.mem (((Operand.reg 4 : Operand 64).read s7) + 0) : Operand 64).read s7) ).2.CF := e8.flags.1
    rw [mv8, r7b14] at h
    exact h
  have r8b14 : ((Operand.reg 14 : Operand 64).read s8) = q8.1 := v8r14
  obtain ⟨s9, a9, ready9, e9⟩ :=
    (sar_r64_imm8_effect_step 0x113daa 0x49 0xfe 63 (by simp [RexWPrefix]) (by decide) (by decide)).advances ready8 (loaded8.mono (codeRange_slice_subset 0x113d8f borrowTopBytes 27 4))
      e8.rip (next 0x13dae (by decide))
  change (sarR64Effect 0x113daa 4 14 63 s8).Holds s8 s9 at e9
  have mx9 : s9.external = s8.external := e9.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])
  have m9 : s9.external = s6.external := mx9.trans m8
  have loaded9 := loaded8.of_external_eq mx9
  have w9 := MemWritable.of_holds e9 w8
  have v9r14 : ((Operand.reg 14 : Operand 64).read s9) = v9 := by
    have h : ((Operand.reg 14 : Operand 64).read s9) = ((Operand.reg 14 : Operand 64).read s8).sshiftRight 63 := e9.writes
    rw [r8b14] at h
    exact h
  have r9b9 : ((Operand.reg 9 : Operand 64).read s9) = ((Operand.reg 9 : Operand 64).read s) := (e9.agrees.read (by simp <;> simp [Effect.components])).trans ((e8.agrees.read (by simp <;> simp [Effect.components])).trans ((e7.agrees.read (by simp <;> simp [Effect.components])).trans ((e6.agrees.read (by simp <;> simp [Effect.components])).trans ((e5.agrees.read (by simp <;> simp [Effect.components])).trans ((e4.agrees.read (by simp <;> simp [Effect.components])).trans ((e3.agrees.read (by simp <;> simp [Effect.components])).trans ((e2.agrees.read (by simp <;> simp [Effect.components])).trans ((e1.agrees.read (by simp <;> simp [Effect.components])).trans (rfl)))))))))
  have r9b2 : ((Operand.reg 2 : Operand 64).read s9) = ((Operand.reg 2 : Operand 64).read s) := (e9.agrees.read (by simp <;> simp [Effect.components])).trans ((e8.agrees.read (by simp <;> simp [Effect.components])).trans ((e7.agrees.read (by simp <;> simp [Effect.components])).trans ((e6.agrees.read (by simp <;> simp [Effect.components])).trans ((e5.agrees.read (by simp <;> simp [Effect.components])).trans ((e4.agrees.read (by simp <;> simp [Effect.components])).trans ((e3.agrees.read (by simp <;> simp [Effect.components])).trans ((e2.agrees.read (by simp <;> simp [Effect.components])).trans ((e1.agrees.read (by simp <;> simp [Effect.components])).trans (rfl)))))))))
  obtain ⟨s10, a10, ready10, e10⟩ :=
    (add_r64_r64_effect_step 0x113dae 0x4c 0xca (by simp [RexWPrefix]) (by decide)).advances ready9 (loaded9.mono (codeRange_slice_subset 0x113d8f borrowTopBytes 31 3))
      e9.rip (next 0x13db1 (by decide))
  change (addR64R64Effect 0x113dae 2 9 s9).Holds s9 s10 at e10
  have mx10 : s10.external = s9.external := e10.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])
  have m10 : s10.external = s6.external := mx10.trans m9
  have loaded10 := loaded9.of_external_eq mx10
  have w10 := MemWritable.of_holds e10 w9
  have v10r2 : ((Operand.reg 2 : Operand 64).read s10) = q10.1 := by
    have h : ((Operand.reg 2 : Operand 64).read s10) = (addSpec ((Operand.reg 2 : Operand 64).read s9) ((Operand.reg 9 : Operand 64).read s9) ).1 := e10.writes
    rw [r9b9, r9b2] at h
    exact h
  have c10 : (StatusFlags.ofRFLAGS s10.RFLAGS).CF = q10.2.CF := by
    have h : (StatusFlags.ofRFLAGS s10.RFLAGS).CF = (addSpec ((Operand.reg 2 : Operand 64).read s9) ((Operand.reg 9 : Operand 64).read s9) ).2.CF := e10.flags.1
    rw [r9b9, r9b2] at h
    exact h
  have r10b1 : ((Operand.reg 1 : Operand 64).read s10) = ((Operand.reg 1 : Operand 64).read s) := (e10.agrees.read (by simp <;> simp [Effect.components])).trans ((e9.agrees.read (by simp <;> simp [Effect.components])).trans ((e8.agrees.read (by simp <;> simp [Effect.components])).trans ((e7.agrees.read (by simp <;> simp [Effect.components])).trans ((e6.agrees.read (by simp <;> simp [Effect.components])).trans ((e5.agrees.read (by simp <;> simp [Effect.components])).trans ((e4.agrees.read (by simp <;> simp [Effect.components])).trans ((e3.agrees.read (by simp <;> simp [Effect.components])).trans ((e2.agrees.read (by simp <;> simp [Effect.components])).trans ((e1.agrees.read (by simp <;> simp [Effect.components])).trans (rfl))))))))))
  obtain ⟨s11, a11, ready11, e11⟩ :=
    (movzx_r32_r8_effect_step 0x113db1 0xc9 (by decide) (by decide)).advances ready10 (loaded10.mono (codeRange_slice_subset 0x113d8f borrowTopBytes 34 3))
      e10.rip (next 0x13db4 (by decide))
  change (movzxR32R8Effect 0x113db1 3 1 1 s10).Holds s10 s11 at e11
  have mx11 : s11.external = s10.external := e11.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])
  have m11 : s11.external = s6.external := mx11.trans m10
  have loaded11 := loaded10.of_external_eq mx11
  have w11 := MemWritable.of_holds e11 w10
  have v11r1 : ((Operand.reg 1 : Operand 64).read s11) = v11 := by
    have h : ((Operand.reg 1 : Operand 64).read s11) = (((Operand.reg 1 : Operand 64).read s10).setWidth 8).setWidth 64 := e11.writes
    rw [r10b1] at h
    exact h
  have r11b14 : ((Operand.reg 14 : Operand 64).read s11) = v9 := (e11.agrees.read (by simp <;> simp [Effect.components])).trans ((e10.agrees.read (by simp <;> simp [Effect.components])).trans (v9r14))
  have r11b1 : ((Operand.reg 1 : Operand 64).read s11) = v11 := v11r1
  have cf11in : (StatusFlags.ofRFLAGS s11.RFLAGS).CF = q10.2.CF := by
    rw [e11.agrees.rflags (by simp <;> simp [Effect.components]) (by simp <;> simp [Effect.components])]
    try exact c10
  obtain ⟨s12, a12, ready12, e12⟩ :=
    (adc_r64_r64_effect_step 0x113db4 0x4c 0xf1 (by simp [RexWPrefix]) (by decide)).advances ready11 (loaded11.mono (codeRange_slice_subset 0x113d8f borrowTopBytes 37 3))
      e11.rip (next 0x13db7 (by decide))
  change (adcR64R64Effect 0x113db4 1 14 s11).Holds s11 s12 at e12
  have mx12 : s12.external = s11.external := e12.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])
  have m12 : s12.external = s6.external := mx12.trans m11
  have loaded12 := loaded11.of_external_eq mx12
  have w12 := MemWritable.of_holds e12 w11
  have v12r1 : ((Operand.reg 1 : Operand 64).read s12) = q12.1 := by
    have h : ((Operand.reg 1 : Operand 64).read s12) = (adcSpec ((Operand.reg 1 : Operand 64).read s11) ((Operand.reg 14 : Operand 64).read s11) (s11.RFLAGS.extractLsb' 0 1)).1 := e12.writes
    rw [r11b14, r11b1, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf11in] at h
    exact h
  have c12 : (StatusFlags.ofRFLAGS s12.RFLAGS).CF = q12.2.CF := by
    have h : (StatusFlags.ofRFLAGS s12.RFLAGS).CF = (adcSpec ((Operand.reg 1 : Operand 64).read s11) ((Operand.reg 14 : Operand 64).read s11) (s11.RFLAGS.extractLsb' 0 1)).2.CF := e12.flags.1
    rw [r11b14, r11b1, P256.Proofs.Common.Field.Montgomery.Schoolbook.carryBit_eq_ofBool, cf11in] at h
    exact h
  have r12b1 : ((Operand.reg 1 : Operand 64).read s12) = q12.1 := v12r1
  obtain ⟨s13, a13, ready13, e13⟩ :=
    (shr_r64_imm8_effect_step 0x113db7 0x48 0xe9 63 (by simp [RexWPrefix]) (by decide) (by decide)).advances ready12 (loaded12.mono (codeRange_slice_subset 0x113d8f borrowTopBytes 40 4))
      e12.rip (next 0x13dbb (by decide))
  change (shrR64Effect 0x113db7 4 1 63 s12).Holds s12 s13 at e13
  have mx13 : s13.external = s12.external := e13.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])
  have m13 : s13.external = s6.external := mx13.trans m12
  have loaded13 := loaded12.of_external_eq mx13
  have w13 := MemWritable.of_holds e13 w12
  have v13r1 : ((Operand.reg 1 : Operand 64).read s13) = v13 := by
    have h : ((Operand.reg 1 : Operand 64).read s13) = ((Operand.reg 1 : Operand 64).read s12) >>> 63 := e13.writes
    rw [r12b1] at h
    exact h
  have r13b1 : ((Operand.reg 1 : Operand 64).read s13) = v13 := v13r1
  have r13b4 : ((Operand.reg 4 : Operand 64).read s13) = ((Operand.reg 4 : Operand 64).read s) := (e13.agrees.read (by simp <;> simp [Effect.components])).trans ((e12.agrees.read (by simp <;> simp [Effect.components])).trans ((e11.agrees.read (by simp <;> simp [Effect.components])).trans ((e10.agrees.read (by simp <;> simp [Effect.components])).trans ((e9.agrees.read (by simp <;> simp [Effect.components])).trans ((e8.agrees.read (by simp <;> simp [Effect.components])).trans ((e7.agrees.read (by simp <;> simp [Effect.components])).trans ((e6.agrees.read (by simp <;> simp [Effect.components])).trans ((e5.agrees.read (by simp <;> simp [Effect.components])).trans ((e4.agrees.read (by simp <;> simp [Effect.components])).trans ((e3.agrees.read (by simp <;> simp [Effect.components])).trans ((e2.agrees.read (by simp <;> simp [Effect.components])).trans ((e1.agrees.read (by simp <;> simp [Effect.components])).trans (rfl)))))))))))))
  have st14 : StorePre 0x113dbb 4 (fun t => ((Operand.reg 4 : Operand 64).read t) + 0) 8 s13 := by
    refine ⟨e13.rip, ?_, ?_⟩
    · rw [r13b4]
      change MemWritable s13 (stackPtr s + 0#64) 8
      rw [BitVec.add_zero]
      exact w13
    · rw [r13b4]
      change RangeApart (stackPtr s + 0#64) 8 0x113dbb 4
      rw [BitVec.add_zero]
      exact pre.apart 0x13dbb 4 (by decide)
  obtain ⟨s14, a14, ready14, e14⟩ :=
    (mov_m64_r64_effect_step 0x113dbb 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 .none) (by decide) rfl rfl).advances ready13 (loaded13.mono (codeRange_slice_subset 0x113d8f borrowTopBytes 44 4))
      st14 (next 0x13dbf (by decide))
  change (movM64R64Effect 0x113dbb 1 (.sib 4 none 0 .none) s13).Holds s13 s14 at e14
  change ({ rip := 0x113dbf, writes := [⟨(.mem (((Operand.reg 4 : Operand 64).read s13) + 0) : Operand 64), ((Operand.reg 1 : Operand 64).read s13)⟩] } : Effect).Holds s13 s14 at e14
  rw [r13b4] at e14
  rw [r13b1] at e14
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at e14
  have m14 : s14.external = s14.external := rfl
  have loaded14 := e14.codeIn (pre.avoids_code 0x13d8f borrowTopBytes (by decide) (by
    intro c hc a len he
    simp only [Effect.components, List.map_cons, List.map_nil, Write.component_mem, List.append_nil, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · cases he; exact ⟨rfl, rfl⟩
    · cases he)) loaded13
  have w14 := MemWritable.of_holds e14 w13
  have r14b4 : ((Operand.reg 4 : Operand 64).read s14) = ((Operand.reg 4 : Operand 64).read s) := (e14.agrees.read (by simp <;> simp [Effect.components])).trans ((e13.agrees.read (by simp <;> simp [Effect.components])).trans ((e12.agrees.read (by simp <;> simp [Effect.components])).trans ((e11.agrees.read (by simp <;> simp [Effect.components])).trans ((e10.agrees.read (by simp <;> simp [Effect.components])).trans ((e9.agrees.read (by simp <;> simp [Effect.components])).trans ((e8.agrees.read (by simp <;> simp [Effect.components])).trans ((e7.agrees.read (by simp <;> simp [Effect.components])).trans ((e6.agrees.read (by simp <;> simp [Effect.components])).trans ((e5.agrees.read (by simp <;> simp [Effect.components])).trans ((e4.agrees.read (by simp <;> simp [Effect.components])).trans ((e3.agrees.read (by simp <;> simp [Effect.components])).trans ((e2.agrees.read (by simp <;> simp [Effect.components])).trans ((e1.agrees.read (by simp <;> simp [Effect.components])).trans (rfl))))))))))))))
  obtain ⟨s15, a15, ready15, e15⟩ :=
    (mov_r64_r64_effect_step 0x113dbf 0x48 0xe1 (by simp [RexWPrefix]) (by decide)).advances ready14 (loaded14.mono (codeRange_slice_subset 0x113d8f borrowTopBytes 48 3))
      e14.rip (next 0x13dc2 (by decide))
  change (movR64R64Effect 0x113dbf 1 4 s14).Holds s14 s15 at e15
  have mx15 : s15.external = s14.external := e15.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])
  have m15 : s15.external = s14.external := mx15.trans m14
  have loaded15 := loaded14.of_external_eq mx15
  have w15 := MemWritable.of_holds e15 w14
  have v15r1 : ((Operand.reg 1 : Operand 64).read s15) = ((Operand.reg 4 : Operand 64).read s) := by
    have h : ((Operand.reg 1 : Operand 64).read s15) = ((Operand.reg 4 : Operand 64).read s14) := e15.writes
    rw [r14b4] at h
    exact h
  have r15b4 : ((Operand.reg 4 : Operand 64).read s15) = ((Operand.reg 4 : Operand 64).read s) := (e15.agrees.read (by simp <;> simp [Effect.components])).trans ((e14.agrees.read (by simp <;> simp [Effect.components])).trans ((e13.agrees.read (by simp <;> simp [Effect.components])).trans ((e12.agrees.read (by simp <;> simp [Effect.components])).trans ((e11.agrees.read (by simp <;> simp [Effect.components])).trans ((e10.agrees.read (by simp <;> simp [Effect.components])).trans ((e9.agrees.read (by simp <;> simp [Effect.components])).trans ((e8.agrees.read (by simp <;> simp [Effect.components])).trans ((e7.agrees.read (by simp <;> simp [Effect.components])).trans ((e6.agrees.read (by simp <;> simp [Effect.components])).trans ((e5.agrees.read (by simp <;> simp [Effect.components])).trans ((e4.agrees.read (by simp <;> simp [Effect.components])).trans ((e3.agrees.read (by simp <;> simp [Effect.components])).trans ((e2.agrees.read (by simp <;> simp [Effect.components])).trans ((e1.agrees.read (by simp <;> simp [Effect.components])).trans (rfl)))))))))))))))
  have mr16 : MemReadable s15 (((Operand.reg 4 : Operand 64).read s15) + 0) 8 := by
    rw [r15b4]
    change MemReadable s15 (stackPtr s + 0#64) 8
    rw [BitVec.add_zero]
    exact w15.readable
  have mv16 : (Operand.mem (((Operand.reg 4 : Operand 64).read s15) + 0) : Operand 64).read s15 = v13 := by
    change memLoad _ _ 64 = _
    rw [r15b4]
    rw [show ((Operand.reg 4 : Operand 64).read s) + (0 : BitVec 64) = stackPtr s from BitVec.add_zero _, m15]
    exact e14.writes
  obtain ⟨s16, a16, ready16, e16⟩ :=
    (mov_r64_m64_effect_step 0x113dc2 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 .none) (by decide) rfl rfl).advances ready15 (loaded15.mono (codeRange_slice_subset 0x113d8f borrowTopBytes 51 4))
      ⟨e15.rip, mr16⟩ (next 0x13dc6 (by decide))
  change (movR64M64Effect 0x113dc2 1 (.sib 4 none 0 .none) s15).Holds s15 s16 at e16
  have mx16 : s16.external = s15.external := e16.agrees.external (by simp [Component.Covers] <;> simp [Effect.components])
  have m16 : s16.external = s14.external := mx16.trans m15
  have loaded16 := loaded15.of_external_eq mx16
  have w16 := MemWritable.of_holds e16 w15
  have v16r1 : ((Operand.reg 1 : Operand 64).read s16) = v13 := by
    have h : ((Operand.reg 1 : Operand 64).read s16) = ((Operand.mem (((Operand.reg 4 : Operand 64).read s15) + 0) : Operand 64).read s15) := e16.writes
    rw [mv16] at h
    exact h
  have r16b1 : ((Operand.reg 1 : Operand 64).read s16) = v13 := v16r1
  have r16b2 : ((Operand.reg 2 : Operand 64).read s16) = q10.1 := (e16.agrees.read (by simp <;> simp [Effect.components])).trans ((e15.agrees.read (by simp <;> simp [Effect.components])).trans ((e14.agrees.read (by simp <;> simp [Effect.components])).trans ((e13.agrees.read (by simp <;> simp [Effect.components])).trans ((e12.agrees.read (by simp <;> simp [Effect.components])).trans ((e11.agrees.read (by simp <;> simp [Effect.components])).trans (v10r2))))))
  have r16b3 : ((Operand.reg 3 : Operand 64).read s16) = ((Operand.reg 4 : Operand 64).read s) := (e16.agrees.read (by simp <;> simp [Effect.components])).trans ((e15.agrees.read (by simp <;> simp [Effect.components])).trans ((e14.agrees.read (by simp <;> simp [Effect.components])).trans ((e13.agrees.read (by simp <;> simp [Effect.components])).trans ((e12.agrees.read (by simp <;> simp [Effect.components])).trans ((e11.agrees.read (by simp <;> simp [Effect.components])).trans ((e10.agrees.read (by simp <;> simp [Effect.components])).trans ((e9.agrees.read (by simp <;> simp [Effect.components])).trans ((e8.agrees.read (by simp <;> simp [Effect.components])).trans (v7r3)))))))))
  have r16b6 : ((Operand.reg 6 : Operand 64).read s16) = q2.1 := (e16.agrees.read (by simp <;> simp [Effect.components])).trans ((e15.agrees.read (by simp <;> simp [Effect.components])).trans ((e14.agrees.read (by simp <;> simp [Effect.components])).trans ((e13.agrees.read (by simp <;> simp [Effect.components])).trans ((e12.agrees.read (by simp <;> simp [Effect.components])).trans ((e11.agrees.read (by simp <;> simp [Effect.components])).trans ((e10.agrees.read (by simp <;> simp [Effect.components])).trans ((e9.agrees.read (by simp <;> simp [Effect.components])).trans ((e8.agrees.read (by simp <;> simp [Effect.components])).trans ((e7.agrees.read (by simp <;> simp [Effect.components])).trans ((e6.agrees.read (by simp <;> simp [Effect.components])).trans ((e5.agrees.read (by simp <;> simp [Effect.components])).trans ((e4.agrees.read (by simp <;> simp [Effect.components])).trans ((e3.agrees.read (by simp <;> simp [Effect.components])).trans (v2r6))))))))))))))
  have r16b14 : ((Operand.reg 14 : Operand 64).read s16) = v9 := (e16.agrees.read (by simp <;> simp [Effect.components])).trans ((e15.agrees.read (by simp <;> simp [Effect.components])).trans ((e14.agrees.read (by simp <;> simp [Effect.components])).trans ((e13.agrees.read (by simp <;> simp [Effect.components])).trans ((e12.agrees.read (by simp <;> simp [Effect.components])).trans ((e11.agrees.read (by simp <;> simp [Effect.components])).trans ((e10.agrees.read (by simp <;> simp [Effect.components])).trans (v9r14)))))))
  have r16b15 : ((Operand.reg 15 : Operand 64).read s16) = v5 := (e16.agrees.read (by simp <;> simp [Effect.components])).trans ((e15.agrees.read (by simp <;> simp [Effect.components])).trans ((e14.agrees.read (by simp <;> simp [Effect.components])).trans ((e13.agrees.read (by simp <;> simp [Effect.components])).trans ((e12.agrees.read (by simp <;> simp [Effect.components])).trans ((e11.agrees.read (by simp <;> simp [Effect.components])).trans ((e10.agrees.read (by simp <;> simp [Effect.components])).trans ((e9.agrees.read (by simp <;> simp [Effect.components])).trans ((e8.agrees.read (by simp <;> simp [Effect.components])).trans ((e7.agrees.read (by simp <;> simp [Effect.components])).trans ((e6.agrees.read (by simp <;> simp [Effect.components])).trans (v5r15)))))))))))
  refine ⟨16, s16, (((((((((((((((a1).trans a2).trans a3).trans a4).trans a5).trans a6).trans a7).trans a8).trans a9).trans a10).trans a11).trans a12).trans a13).trans a14).trans a15).trans a16, ready16, loaded16, e16.rip, ?_, ?_, ?_⟩
  · refine ⟨r16b1, r16b2, r16b3, r16b6, r16b14, r16b15, ?_⟩
    change memLoad s16.external (stackPtr s) 64 = _
    rw [m16]
    exact e14.writes
  · exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  · apply ((((((((((((((((e1.agrees).trans e2.agrees).trans e3.agrees).trans e4.agrees).trans e5.agrees).trans e6.agrees).trans e7.agrees).trans e8.agrees).trans e9.agrees).trans e10.agrees).trans e11.agrees).trans e12.agrees).trans e13.agrees).trans e14.agrees).trans e15.agrees).trans e16.agrees).mono
    simp only [addR64R64Effect_components, notR64Effect_components, orR64R64Effect_components, shrR64Effect_components, movR64R64Effect_components, subR64M64Effect_components, sarR64Effect_components, adcR64R64Effect_components, movR64M64Effect_components]
    simp [borrowTopEffect, Effect.components, stackPtr, Operand.read_reg64]

theorem borrowTop_bytes :
    Extracted.textBytes.toListFrom 0x13d8f borrowTopBytes.length = borrowTopBytes := by
  decide +kernel

end P256.Proofs.Field.Montgomery.Reduction
