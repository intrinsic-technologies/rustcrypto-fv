import P256.Proofs.Common.Field.Montgomery.Schoolbook.CarryCompose
import P256.Proofs.Common.Instructions.ShiftLeft.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import P256.Proofs.Program.Code
import P256.Proofs.Field.Montgomery.Reduction.Slot
import P256.Proofs.Common.Field.Operations.Neg.Borrow.Or

set_option autoImplicit false

open P256.Proofs.Common.Field.FieldNeg.Instructions (orR64R64Effect orR64R64Effect_components or_r64_r64_effect_step)
open P256.Proofs.Common.Field.Instructions (subR64M64Effect subR64M64Effect_components sub_r64_m64_effect_step)
open P256.Proofs.Common.Instructions (addR64M64Effect_components mulR64Effect_components sarR64Effect sarR64Effect_components sar_r64_imm8_effect_step)
open P256.Proofs.Common.Instructions.Carry (adcR64Imm8Effect_components adcR64M64Effect_components adcR64R64Effect_components)
open P256.Proofs.Common.Instructions.Setb (SupportedOpcode setccR8Effect setccR8Effect_components setcc_r8_rex_effect_step)
open P256.Proofs.Common.Instructions.ShiftLeft (shlR64Effect_components)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Field.Montgomery.Reduction

open P256.Spec.Program.Routines
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

attribute [local simp] mulR64Effect_components adcR64R64Effect_components adcR64Imm8Effect_components
  adcR64M64Effect_components addR64M64Effect_components setccR8Effect_components shlR64Effect_components
  orR64R64Effect_components sarR64Effect_components subR64M64Effect_components

def borrowLowBytes : List UInt8 :=
  [0x49, 0x8d, 0x44, 0x24, 0x1, 0x49, 0xf7, 0xd4, 0x40, 0xf, 0x92, 0xc5, 0x49, 0x9, 0xc4, 0x49, 0xc1, 0xec, 0x3f, 0x4c, 0x89, 0x24, 0x24, 0x49, 0x89, 0xe0, 0x45, 0x31, 0xf6, 0x45, 0x31, 0xc0, 0x4c, 0x2b, 0x4, 0x24, 0x49, 0xc1, 0xf8, 0x3f]

def borrowLowEffect (s : RamState) : Effect :=
  let v1 := ((Operand.reg 12 : Operand 64).read s) + 1
  let v2 := ~~~((Operand.reg 12 : Operand 64).read s)
  let v3 := mergeGPR 8 (if (StatusFlags.ofRFLAGS s.RFLAGS).CF then 1 else 0) ((Operand.reg 5 : Operand 64).read s)
  let v4 := v2 ||| v1
  let v5 := v4 >>> 63
  let q10 := subSpec (0 : BitVec 64) v5
  let v11 := (q10.1).sshiftRight 63
  { rip := 0x113d38
    writes := [⟨(.reg 0 : Operand 64), v1⟩,
      ⟨(.reg 5 : Operand 64), v3⟩,
      ⟨(.reg 8 : Operand 64), v11⟩,
      ⟨(.reg 12 : Operand 64), v5⟩,
      ⟨(.reg 14 : Operand 64), (0 : BitVec 64)⟩,
      ⟨(.mem (stackPtr s) : Operand 64), v5⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem borrowLow_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (BorrowSlotPre 0x113d10) (codeRange 0x113d10 borrowLowBytes)
      (Effect.post borrowLowEffect) := by
  intro s ready loaded pre
  have next (offset : Nat) (h : offset < 118431) :=
    boundary_ne_program hout (inProgram_of_textOffset offset h)
  have code (offset len : Nat) := loaded.mono (codeRange_slice_subset 0x113d10 borrowLowBytes offset len)
  have loaded0 := loaded
  have w0 := pre.writable
  have m0 : s.external = s.external := rfl
  have c0 : (StatusFlags.ofRFLAGS s.RFLAGS).CF = (StatusFlags.ofRFLAGS s.RFLAGS).CF := rfl
  let v1 := ((Operand.reg 12 : Operand 64).read s) + 1
  let v2 := ~~~((Operand.reg 12 : Operand 64).read s)
  let v3 := mergeGPR 8 (if (StatusFlags.ofRFLAGS s.RFLAGS).CF then 1 else 0) ((Operand.reg 5 : Operand 64).read s)
  let v4 := v2 ||| v1
  let v5 := v4 >>> 63
  let q10 := subSpec (0 : BitVec 64) v5
  let v11 := (q10.1).sshiftRight 63
  obtain ⟨s1, a1, ready1, e1⟩ :=
    (lea_r64_effect_step 0x113d10 0x49 (by simp [RexWPrefix]) 0 (.sib 12 none 0 (.d8 1)) (by decide) rfl rfl).advances ready (loaded0.mono (codeRange_slice_subset 0x113d10 borrowLowBytes 0 5))
      pre.rip (next 0x13d15 (by decide))
  change (leaR64Effect 0x113d10 0 (.sib 12 none 0 (.d8 1)) s).Holds s s1 at e1
  have mx1 : s1.external = s.external := e1.agrees.external (by simp [Component.Covers])
  have m1 : s1.external = s.external := mx1.trans m0
  have loaded1 := loaded0.of_external_eq mx1
  have w1 := MemWritable.of_holds e1 w0
  have v1r0 : ((Operand.reg 0 : Operand 64).read s1) = v1 := by
    have h : ((Operand.reg 0 : Operand 64).read s1) = ((Operand.reg 12 : Operand 64).read s) + 1 := e1.writes
    exact h
  have r1b12 : ((Operand.reg 12 : Operand 64).read s1) = ((Operand.reg 12 : Operand 64).read s) := (e1.agrees.read (by simp <;> simp [Effect.components])).trans (rfl)
  obtain ⟨s2, a2, ready2, e2⟩ :=
    (not_r64_effect_step 0x113d15 0x49 0xd4 (by simp [RexWPrefix]) (by decide) (by decide)).advances ready1 (loaded1.mono (codeRange_slice_subset 0x113d10 borrowLowBytes 5 3))
      e1.rip (next 0x13d18 (by decide))
  change (notR64Effect 0x113d15 12 s1).Holds s1 s2 at e2
  have mx2 : s2.external = s1.external := e2.agrees.external (by simp [Component.Covers])
  have m2 : s2.external = s.external := mx2.trans m1
  have loaded2 := loaded1.of_external_eq mx2
  have w2 := MemWritable.of_holds e2 w1
  have v2r12 : ((Operand.reg 12 : Operand 64).read s2) = v2 := by
    have h : ((Operand.reg 12 : Operand 64).read s2) = ~~~((Operand.reg 12 : Operand 64).read s1) := e2.writes
    rw [r1b12] at h
    exact h
  have r2b5 : ((Operand.reg 5 : Operand 64).read s2) = ((Operand.reg 5 : Operand 64).read s) := (e2.agrees.read (by simp <;> simp [Effect.components])).trans ((e1.agrees.read (by simp <;> simp [Effect.components])).trans (rfl))
  have cf2in : (StatusFlags.ofRFLAGS s2.RFLAGS).CF = (StatusFlags.ofRFLAGS s.RFLAGS).CF := by
    rw [e2.agrees.rflags (by simp <;> simp [Effect.components]) (by simp <;> simp [Effect.components]), e1.agrees.rflags (by simp <;> simp [Effect.components]) (by simp <;> simp [Effect.components])]
    try exact c0
  obtain ⟨s3, a3, ready3, e3⟩ :=
    (setcc_r8_rex_effect_step 0x113d18 0x40 0x92 0xc5 (by simp [RexPrefix]) (by simp [SupportedOpcode]) (by decide)).advances ready2 (loaded2.mono (codeRange_slice_subset 0x113d10 borrowLowBytes 8 4))
      e2.rip (next 0x13d1c (by decide))
  change (setccR8Effect 0x113d18 4 5 2 s2).Holds s2 s3 at e3
  have mx3 : s3.external = s2.external := e3.agrees.external (by simp [Component.Covers])
  have m3 : s3.external = s.external := mx3.trans m2
  have loaded3 := loaded2.of_external_eq mx3
  have w3 := MemWritable.of_holds e3 w2
  have v3r5 : ((Operand.reg 5 : Operand 64).read s3) = v3 := by
    have h : ((Operand.reg 5 : Operand 64).read s3) = mergeGPR 8 (if (StatusFlags.ofRFLAGS s2.RFLAGS).CF then 1 else 0) ((Operand.reg 5 : Operand 64).read s2) := e3.writes
    rw [r2b5, cf2in] at h
    exact h
  have r3b0 : ((Operand.reg 0 : Operand 64).read s3) = v1 := (e3.agrees.read (by simp <;> simp [Effect.components])).trans ((e2.agrees.read (by simp <;> simp [Effect.components])).trans (v1r0))
  have r3b12 : ((Operand.reg 12 : Operand 64).read s3) = v2 := (e3.agrees.read (by simp <;> simp [Effect.components])).trans (v2r12)
  obtain ⟨s4, a4, ready4, e4⟩ :=
    (or_r64_r64_effect_step 0x113d1c 0x49 0xc4 (by simp [RexWPrefix]) (by decide)).advances ready3 (loaded3.mono (codeRange_slice_subset 0x113d10 borrowLowBytes 12 3))
      e3.rip (next 0x13d1f (by decide))
  change (orR64R64Effect 0x113d1c 12 0 s3).Holds s3 s4 at e4
  have mx4 : s4.external = s3.external := e4.agrees.external (by simp [Component.Covers])
  have m4 : s4.external = s.external := mx4.trans m3
  have loaded4 := loaded3.of_external_eq mx4
  have w4 := MemWritable.of_holds e4 w3
  have v4r12 : ((Operand.reg 12 : Operand 64).read s4) = v4 := by
    have h : ((Operand.reg 12 : Operand 64).read s4) = ((Operand.reg 12 : Operand 64).read s3) ||| ((Operand.reg 0 : Operand 64).read s3) := e4.writes
    rw [r3b0, r3b12] at h
    exact h
  have r4b12 : ((Operand.reg 12 : Operand 64).read s4) = v4 := v4r12
  obtain ⟨s5, a5, ready5, e5⟩ :=
    (shr_r64_imm8_effect_step 0x113d1f 0x49 0xec 63 (by simp [RexWPrefix]) (by decide) (by decide)).advances ready4 (loaded4.mono (codeRange_slice_subset 0x113d10 borrowLowBytes 15 4))
      e4.rip (next 0x13d23 (by decide))
  change (shrR64Effect 0x113d1f 4 12 63 s4).Holds s4 s5 at e5
  have mx5 : s5.external = s4.external := e5.agrees.external (by simp [Component.Covers])
  have m5 : s5.external = s.external := mx5.trans m4
  have loaded5 := loaded4.of_external_eq mx5
  have w5 := MemWritable.of_holds e5 w4
  have v5r12 : ((Operand.reg 12 : Operand 64).read s5) = v5 := by
    have h : ((Operand.reg 12 : Operand 64).read s5) = ((Operand.reg 12 : Operand 64).read s4) >>> 63 := e5.writes
    rw [r4b12] at h
    exact h
  have r5b12 : ((Operand.reg 12 : Operand 64).read s5) = v5 := v5r12
  have r5b4 : ((Operand.reg 4 : Operand 64).read s5) = ((Operand.reg 4 : Operand 64).read s) := (e5.agrees.read (by simp <;> simp [Effect.components])).trans ((e4.agrees.read (by simp <;> simp [Effect.components])).trans ((e3.agrees.read (by simp <;> simp [Effect.components])).trans ((e2.agrees.read (by simp <;> simp [Effect.components])).trans ((e1.agrees.read (by simp <;> simp [Effect.components])).trans (rfl)))))
  have st6 : StorePre 0x113d23 4 (fun t => ((Operand.reg 4 : Operand 64).read t) + 0) 8 s5 := by
    refine ⟨e5.rip, ?_, ?_⟩
    · rw [r5b4]
      change MemWritable s5 (stackPtr s + 0#64) 8
      rw [BitVec.add_zero]
      exact w5
    · rw [r5b4]
      change RangeApart (stackPtr s + 0#64) 8 0x113d23 4
      rw [BitVec.add_zero]
      exact pre.apart 0x13d23 4 (by decide)
  obtain ⟨s6, a6, ready6, e6⟩ :=
    (mov_m64_r64_effect_step 0x113d23 0x4c (by simp [RexWPrefix]) 4 (.sib 4 none 0 .none) (by decide) rfl rfl).advances ready5 (loaded5.mono (codeRange_slice_subset 0x113d10 borrowLowBytes 19 4))
      st6 (next 0x13d27 (by decide))
  change (movM64R64Effect 0x113d23 12 (.sib 4 none 0 .none) s5).Holds s5 s6 at e6
  change ({ rip := 0x113d27, writes := [⟨(.mem (((Operand.reg 4 : Operand 64).read s5) + 0) : Operand 64), ((Operand.reg 12 : Operand 64).read s5)⟩] } : Effect).Holds s5 s6 at e6
  rw [r5b4] at e6
  rw [r5b12] at e6
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at e6
  have m6 : s6.external = s6.external := rfl
  have loaded6 := e6.codeIn (pre.avoids_code 0x13d10 borrowLowBytes (by decide) (by
    intro c hc a len he
    simp only [Effect.components, List.map_cons, List.map_nil, Write.component_mem, List.append_nil, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · cases he; exact ⟨rfl, rfl⟩
    · cases he)) loaded5
  have w6 := MemWritable.of_holds e6 w5
  have r6b4 : ((Operand.reg 4 : Operand 64).read s6) = ((Operand.reg 4 : Operand 64).read s) := (e6.agrees.read (by simp <;> simp [Effect.components])).trans ((e5.agrees.read (by simp <;> simp [Effect.components])).trans ((e4.agrees.read (by simp <;> simp [Effect.components])).trans ((e3.agrees.read (by simp <;> simp [Effect.components])).trans ((e2.agrees.read (by simp <;> simp [Effect.components])).trans ((e1.agrees.read (by simp <;> simp [Effect.components])).trans (rfl))))))
  obtain ⟨s7, a7, ready7, e7⟩ :=
    (mov_r64_r64_effect_step 0x113d27 0x49 0xe0 (by simp [RexWPrefix]) (by decide)).advances ready6 (loaded6.mono (codeRange_slice_subset 0x113d10 borrowLowBytes 23 3))
      e6.rip (next 0x13d2a (by decide))
  change (movR64R64Effect 0x113d27 8 4 s6).Holds s6 s7 at e7
  have mx7 : s7.external = s6.external := e7.agrees.external (by simp [Component.Covers])
  have m7 : s7.external = s6.external := mx7.trans m6
  have loaded7 := loaded6.of_external_eq mx7
  have w7 := MemWritable.of_holds e7 w6
  have v7r8 : ((Operand.reg 8 : Operand 64).read s7) = ((Operand.reg 4 : Operand 64).read s) := by
    have h : ((Operand.reg 8 : Operand 64).read s7) = ((Operand.reg 4 : Operand 64).read s6) := e7.writes
    rw [r6b4] at h
    exact h
  have r7b14 : ((Operand.reg 14 : Operand 64).read s7) = ((Operand.reg 14 : Operand 64).read s) := (e7.agrees.read (by simp <;> simp [Effect.components])).trans ((e6.agrees.read (by simp <;> simp [Effect.components])).trans ((e5.agrees.read (by simp <;> simp [Effect.components])).trans ((e4.agrees.read (by simp <;> simp [Effect.components])).trans ((e3.agrees.read (by simp <;> simp [Effect.components])).trans ((e2.agrees.read (by simp <;> simp [Effect.components])).trans ((e1.agrees.read (by simp <;> simp [Effect.components])).trans (rfl)))))))
  obtain ⟨s8, a8, ready8, e8⟩ :=
    (xor_r32_r32_rex_effect_step 0x113d2a 0x45 0xf6 (by simp [RexNoWPrefix]) (by decide)).advances ready7 (loaded7.mono (codeRange_slice_subset 0x113d10 borrowLowBytes 26 3))
      e7.rip (next 0x13d2d (by decide))
  change (xorR32R32Effect 0x113d2a 3 14 14 s7).Holds s7 s8 at e8
  have mx8 : s8.external = s7.external := e8.agrees.external (by simp [Component.Covers])
  have m8 : s8.external = s6.external := mx8.trans m7
  have loaded8 := loaded7.of_external_eq mx8
  have w8 := MemWritable.of_holds e8 w7
  have v8r14 : ((Operand.reg 14 : Operand 64).read s8) = (0 : BitVec 64) := by
    have h : ((Operand.reg 14 : Operand 64).read s8) = 0 := (by simpa only [xorR32R32Effect, BitVec.xor_self, BitVec.setWidth_zero, BitVec.ofNat_eq_ofNat, Write.AllHold] using e8.writes)
    exact h
  have r8b8 : ((Operand.reg 8 : Operand 64).read s8) = ((Operand.reg 4 : Operand 64).read s) := (e8.agrees.read (by simp <;> simp [Effect.components])).trans (v7r8)
  obtain ⟨s9, a9, ready9, e9⟩ :=
    (xor_r32_r32_rex_effect_step 0x113d2d 0x45 0xc0 (by simp [RexNoWPrefix]) (by decide)).advances ready8 (loaded8.mono (codeRange_slice_subset 0x113d10 borrowLowBytes 29 3))
      e8.rip (next 0x13d30 (by decide))
  change (xorR32R32Effect 0x113d2d 3 8 8 s8).Holds s8 s9 at e9
  have mx9 : s9.external = s8.external := e9.agrees.external (by simp [Component.Covers])
  have m9 : s9.external = s6.external := mx9.trans m8
  have loaded9 := loaded8.of_external_eq mx9
  have w9 := MemWritable.of_holds e9 w8
  have v9r8 : ((Operand.reg 8 : Operand 64).read s9) = (0 : BitVec 64) := by
    have h : ((Operand.reg 8 : Operand 64).read s9) = 0 := (by simpa only [xorR32R32Effect, BitVec.xor_self, BitVec.setWidth_zero, BitVec.ofNat_eq_ofNat, Write.AllHold] using e9.writes)
    exact h
  have r9b4 : ((Operand.reg 4 : Operand 64).read s9) = ((Operand.reg 4 : Operand 64).read s) := (e9.agrees.read (by simp <;> simp [Effect.components])).trans ((e8.agrees.read (by simp <;> simp [Effect.components])).trans ((e7.agrees.read (by simp <;> simp [Effect.components])).trans ((e6.agrees.read (by simp <;> simp [Effect.components])).trans ((e5.agrees.read (by simp <;> simp [Effect.components])).trans ((e4.agrees.read (by simp <;> simp [Effect.components])).trans ((e3.agrees.read (by simp <;> simp [Effect.components])).trans ((e2.agrees.read (by simp <;> simp [Effect.components])).trans ((e1.agrees.read (by simp <;> simp [Effect.components])).trans (rfl)))))))))
  have mr10 : MemReadable s9 (((Operand.reg 4 : Operand 64).read s9) + 0) 8 := by
    rw [r9b4]
    change MemReadable s9 (stackPtr s + 0#64) 8
    rw [BitVec.add_zero]
    exact w9.readable
  have mv10 : (Operand.mem (((Operand.reg 4 : Operand 64).read s9) + 0) : Operand 64).read s9 = v5 := by
    change memLoad _ _ 64 = _
    rw [r9b4]
    rw [show ((Operand.reg 4 : Operand 64).read s) + (0 : BitVec 64) = stackPtr s from BitVec.add_zero _, m9]
    exact e6.writes
  have r9b8 : ((Operand.reg 8 : Operand 64).read s9) = (0 : BitVec 64) := v9r8
  obtain ⟨s10, a10, ready10, e10⟩ :=
    (sub_r64_m64_effect_step 0x113d30 0x4c (by simp [RexWPrefix]) 0 (.sib 4 none 0 .none) (by decide) rfl rfl).advances ready9 (loaded9.mono (codeRange_slice_subset 0x113d10 borrowLowBytes 32 4))
      ⟨e9.rip, mr10⟩ (next 0x13d34 (by decide))
  change (subR64M64Effect 0x113d30 8 (.sib 4 none 0 .none) s9).Holds s9 s10 at e10
  have mx10 : s10.external = s9.external := e10.agrees.external (by simp [Component.Covers])
  have m10 : s10.external = s6.external := mx10.trans m9
  have loaded10 := loaded9.of_external_eq mx10
  have w10 := MemWritable.of_holds e10 w9
  have v10r8 : ((Operand.reg 8 : Operand 64).read s10) = q10.1 := by
    have h : ((Operand.reg 8 : Operand 64).read s10) = (subSpec ((Operand.reg 8 : Operand 64).read s9) ((Operand.mem (((Operand.reg 4 : Operand 64).read s9) + 0) : Operand 64).read s9) ).1 := e10.writes
    rw [mv10, r9b8] at h
    exact h
  have c10 : (StatusFlags.ofRFLAGS s10.RFLAGS).CF = q10.2.CF := by
    have h : (StatusFlags.ofRFLAGS s10.RFLAGS).CF = (subSpec ((Operand.reg 8 : Operand 64).read s9) ((Operand.mem (((Operand.reg 4 : Operand 64).read s9) + 0) : Operand 64).read s9) ).2.CF := e10.flags.1
    rw [mv10, r9b8] at h
    exact h
  have r10b8 : ((Operand.reg 8 : Operand 64).read s10) = q10.1 := v10r8
  obtain ⟨s11, a11, ready11, e11⟩ :=
    (sar_r64_imm8_effect_step 0x113d34 0x49 0xf8 63 (by simp [RexWPrefix]) (by decide) (by decide)).advances ready10 (loaded10.mono (codeRange_slice_subset 0x113d10 borrowLowBytes 36 4))
      e10.rip (next 0x13d38 (by decide))
  change (sarR64Effect 0x113d34 4 8 63 s10).Holds s10 s11 at e11
  have mx11 : s11.external = s10.external := e11.agrees.external (by simp [Component.Covers])
  have m11 : s11.external = s6.external := mx11.trans m10
  have loaded11 := loaded10.of_external_eq mx11
  have w11 := MemWritable.of_holds e11 w10
  have v11r8 : ((Operand.reg 8 : Operand 64).read s11) = v11 := by
    have h : ((Operand.reg 8 : Operand 64).read s11) = ((Operand.reg 8 : Operand 64).read s10).sshiftRight 63 := e11.writes
    rw [r10b8] at h
    exact h
  have r11b0 : ((Operand.reg 0 : Operand 64).read s11) = v1 := (e11.agrees.read (by simp <;> simp [Effect.components])).trans ((e10.agrees.read (by simp <;> simp [Effect.components])).trans ((e9.agrees.read (by simp <;> simp [Effect.components])).trans ((e8.agrees.read (by simp <;> simp [Effect.components])).trans ((e7.agrees.read (by simp <;> simp [Effect.components])).trans ((e6.agrees.read (by simp <;> simp [Effect.components])).trans ((e5.agrees.read (by simp <;> simp [Effect.components])).trans ((e4.agrees.read (by simp <;> simp [Effect.components])).trans ((e3.agrees.read (by simp <;> simp [Effect.components])).trans ((e2.agrees.read (by simp <;> simp [Effect.components])).trans (v1r0))))))))))
  have r11b5 : ((Operand.reg 5 : Operand 64).read s11) = v3 := (e11.agrees.read (by simp <;> simp [Effect.components])).trans ((e10.agrees.read (by simp <;> simp [Effect.components])).trans ((e9.agrees.read (by simp <;> simp [Effect.components])).trans ((e8.agrees.read (by simp <;> simp [Effect.components])).trans ((e7.agrees.read (by simp <;> simp [Effect.components])).trans ((e6.agrees.read (by simp <;> simp [Effect.components])).trans ((e5.agrees.read (by simp <;> simp [Effect.components])).trans ((e4.agrees.read (by simp <;> simp [Effect.components])).trans (v3r5))))))))
  have r11b8 : ((Operand.reg 8 : Operand 64).read s11) = v11 := v11r8
  have r11b12 : ((Operand.reg 12 : Operand 64).read s11) = v5 := (e11.agrees.read (by simp <;> simp [Effect.components])).trans ((e10.agrees.read (by simp <;> simp [Effect.components])).trans ((e9.agrees.read (by simp <;> simp [Effect.components])).trans ((e8.agrees.read (by simp <;> simp [Effect.components])).trans ((e7.agrees.read (by simp <;> simp [Effect.components])).trans ((e6.agrees.read (by simp <;> simp [Effect.components])).trans (v5r12))))))
  have r11b14 : ((Operand.reg 14 : Operand 64).read s11) = (0 : BitVec 64) := (e11.agrees.read (by simp <;> simp [Effect.components])).trans ((e10.agrees.read (by simp <;> simp [Effect.components])).trans ((e9.agrees.read (by simp <;> simp [Effect.components])).trans (v8r14)))
  refine ⟨11, s11, ((((((((((a1).trans a2).trans a3).trans a4).trans a5).trans a6).trans a7).trans a8).trans a9).trans a10).trans a11, ready11, loaded11, e11.rip, ?_, ?_, ?_⟩
  · refine ⟨r11b0, r11b5, r11b8, r11b12, r11b14, ?_⟩
    change memLoad s11.external (stackPtr s) 64 = _
    rw [m11]
    exact e6.writes
  · exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  · apply (((((((((((e1.agrees).trans e2.agrees).trans e3.agrees).trans e4.agrees).trans e5.agrees).trans e6.agrees).trans e7.agrees).trans e8.agrees).trans e9.agrees).trans e10.agrees).trans e11.agrees).mono
    simp only [leaR64Effect_components, notR64Effect_components, setccR8Effect_components, orR64R64Effect_components, shrR64Effect_components, movR64R64Effect_components, xorR32R32Effect_components, subR64M64Effect_components, sarR64Effect_components]
    simp [borrowLowEffect, Effect.components, stackPtr, Operand.read_reg64]

theorem borrowLow_bytes :
    Extracted.textBytes.toListFrom 0x13d10 borrowLowBytes.length = borrowLowBytes := by
  decide +kernel

end P256.Proofs.Field.Montgomery.Reduction
