import Base16ct.Proofs.Base16ctUpperEncodeCorrect.Callee.Initialize.State
import Base16ct.Proofs.Base16ctUpperEncodeCorrect.Callee.Initialize.Arithmetic
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.NopMem.Triple

namespace Base16ct.Proofs.Base16ctUpperEncodeCorrect

open Base16ct.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem callee_initialize_success [Bindings] (c : CallContext) {s : RamState}
    (hs : InitializeState c s) (hip : s.RIP = 0x100668) :
    ∃ fuel t, Advances (returnBoundary c.initial) fuel s t ∧
      if c.input.length = 0 then SuccessState c t else LoopState c 0 t := by
  have hne := text_address_ne_return
    (returnBoundary_valid c.valid.stack c.valid.returnAddress).2
  have preserve {t : RamState} (hr : ReadyToStep t)
      (ha : AgreesExcept [.reg 2, .reg 8, .flags, .rip] s t)
      (hl : t.regValue .rdx = BitVec.ofNat 64 c.input.length) : InitializeState c t := by
    have hm : t.external = s.external := ha.external (by simp [Component.Covers])
    refine ⟨⟨⟨hr, hs.invariant.code.of_external_eq hm,
      (hs.invariant.agrees.trans ha).mono (by simp [encoderComponents])⟩,
      (ha.read (n := 64) (r := 4) (by simp)).trans hs.rsp,
      (ha.read (n := 64) (r := 0) (by simp)).trans hs.result, ?_,
      (ha.read (n := 64) (r := 3) (by simp)).trans hs.rbx, ?_⟩,
      (ha.read (n := 64) (r := 6) (by simp)).trans hs.src, hl,
      (ha.read (n := 64) (r := 1) (by simp)).trans hs.dst,
      (ha.read (n := 64) (r := 7) (by simp)).trans hs.resultLength⟩
    · change memLoad t.external _ 64 = _
      rw [hm]
      exact hs.returnAddress
    · change memLoad t.external _ 64 = _
      rw [hm]
      exact hs.savedRbx
  have hc1 : CodeIn (codeRange 0x100668
      [0x49, 0xb8, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x3f]) s := by
    have hb : Extracted.textBytes.toListFrom 0x668 10 =
        [0x49, 0xb8, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x3f] := by decide +kernel
    have hc := program_text_slice hs.invariant.code 0x668 10 (by decide +kernel)
    rw [hb] at hc
    exact hc
  obtain ⟨s1, run1, ready1, e1⟩ :=
    (mov_r64_imm64_effect_step 0x100668 0x49 0xb8 (by simp [RexWPrefix]) (by decide)
      0x3fffffffffffffff).advances hs.invariant.ready hc1 hip
      (hne 0x672 (by decide +kernel))
  have a1 : AgreesExcept [.reg 8, .rip] s s1 := e1.agrees
  have c1 := a1.codeIn (by simp [Component.Covers]) hs.invariant.code
  have l1 : s1.regValue .rdx = BitVec.ofNat 64 c.input.length :=
    (a1.read (n := 64) (r := 2) (by simp)).trans hs.length
  have r1 : s1.regValue .r8 = 0x3fffffffffffffff := e1.writes
  have hc2 : CodeIn (codeRange 0x100672 [0x4c, 0x21, 0xc2]) s1 := by
    have hb : Extracted.textBytes.toListFrom 0x672 3 = [0x4c, 0x21, 0xc2] := by decide +kernel
    have hc := program_text_slice c1 0x672 3 (by decide +kernel)
    rw [hb] at hc
    exact hc
  obtain ⟨s2, run2, ready2, e2⟩ :=
    (and_r64_r64_effect_step 0x100672 0x4c 0xc2 (by simp [RexWPrefix]) (by decide)).advances
      ready1 hc2 e1.rip (hne 0x675 (by decide +kernel))
  have a2 : AgreesExcept [.reg 2, .flags, .rip] s1 s2 := e2.agrees
  have c2 := a2.codeIn (by simp [Component.Covers]) c1
  have l2 : s2.regValue .rdx = BitVec.ofNat 64 c.input.length := by
    have hw : s2.regValue .rdx = s1.regValue .rdx &&& s1.regValue .r8 := e2.writes
    rw [hw, l1, r1, init_input_length_mask]
  have z2 : (StatusFlags.ofRFLAGS s2.RFLAGS).ZF = decide (c.input.length = 0) := by
    have hz : (StatusFlags.ofRFLAGS s2.RFLAGS).ZF =
        (s1.regValue .rdx &&& s1.regValue .r8 == 0) := e2.flags.2.2.2.1
    rw [hz, l1, r1, init_input_length_mask]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq, init_input_length_eq_zero]
  have hc3 : CodeIn (codeRange 0x100675 [0x74, 0x5a]) s2 := by
    have hb : Extracted.textBytes.toListFrom 0x675 2 = [0x74, 0x5a] := by decide +kernel
    have hc := program_text_slice c2 0x675 2 (by decide +kernel)
    rw [hb] at hc
    exact hc
  obtain ⟨s3, step3, ready3, e3⟩ := jcc_rel8_effect_step 0x100675 4 0x5a s2
    ready2 hc3 ⟨e2.rip, fun _ => by decide⟩
  have ip3 : s3.RIP = if c.input.length = 0 then 0x1006d1 else 0x100677 := by
    rw [e3.rip]
    simp [jccEffect, branchEffect, condHolds, z2, branchTarget]
  have run3 : Advances (returnBoundary c.initial) 1 s2 s3 := by
    apply Advances.of_step step3
    left
    rw [ip3]
    split
    · exact hne 0x6d1 (by decide +kernel)
    · exact hne 0x677 (by decide +kernel)
  have a3 : AgreesExcept [.rip] s2 s3 := e3.agrees
  have a13 : AgreesExcept [.reg 2, .reg 8, .flags, .rip] s s3 :=
    ((a1.trans a2).trans a3).mono (by simp)
  have l3 : s3.regValue .rdx = BitVec.ofNat 64 c.input.length :=
    (a3.read (n := 64) (r := 2) (by simp)).trans l2
  have h3 := preserve ready3 a13 l3
  by_cases hz : c.input.length = 0
  · refine ⟨3, s3, (run1.trans run2).trans run3, ?_⟩
    simp only [ite_eq_left hz]
    refine ⟨h3.toCalleeState, ?_, h3.dst, h3.resultLength, ?_⟩
    · simpa only [ite_eq_left hz] using ip3
    · intro i hi
      omega
  · have hc4 : CodeIn (codeRange 0x100677 [0x45, 0x31, 0xc0]) s3 := by
      have hb : Extracted.textBytes.toListFrom 0x677 3 = [0x45, 0x31, 0xc0] := by decide +kernel
      have hc := program_text_slice h3.invariant.code 0x677 3 (by decide +kernel)
      rw [hb] at hc
      exact hc
    obtain ⟨s4, run4, ready4, e4⟩ :=
      (xor_r32_r32_rex_effect_step 0x100677 0x45 0xc0 (by simp [RexNoWPrefix]) (by decide)).advances
        ready3 hc4 (by simpa only [ite_eq_right hz] using ip3) (hne 0x67a (by decide +kernel))
    have a4 : AgreesExcept [.reg 8, .flags, .rip] s3 s4 := e4.agrees
    have c4 := a4.codeIn (by simp [Component.Covers]) h3.invariant.code
    have r4 : s4.regValue .r8 = 0 := by
      have hw : s4.regValue .r8 =
          ((Operand.reg 8 : Operand 32).read s3 ^^^ (Operand.reg 8 : Operand 32).read s3).setWidth 64 :=
        e4.writes
      rw [hw, BitVec.xor_self]
      rfl
    have hc5 : CodeIn (codeRange 0x10067a [0x66, 0x0f, 0x1f, 0x44, 0x00, 0x00]) s4 := by
      have hb : Extracted.textBytes.toListFrom 0x67a 6 = [0x66, 0x0f, 0x1f, 0x44, 0x00, 0x00] := by
        decide +kernel
      have hc := program_text_slice c4 0x67a 6 (by decide +kernel)
      rw [hb] at hc
      exact hc
    obtain ⟨s5, run5, ready5, e5⟩ :=
      (nop_m_effect_step 0x10067a [0x66] (by decide) (by decide)
        (.sib 0 (some 0) 0 (.d8 0)) ⟨by decide, fun h => by cases h⟩ rfl rfl).advances
        ready4 hc5 e4.rip (hne 0x680 (by decide +kernel))
    have a5 : AgreesExcept [.rip] s4 s5 := e5.agrees
    have a35 : AgreesExcept [.reg 8, .flags, .rip] s3 s5 := (a4.trans a5).mono (by simp)
    have a15 : AgreesExcept [.reg 2, .reg 8, .flags, .rip] s s5 :=
      (a13.trans a35).mono (by simp)
    have l5 : s5.regValue .rdx = BitVec.ofNat 64 c.input.length :=
      (a35.read (n := 64) (r := 2) (by simp)).trans l3
    have h5 := preserve ready5 a15 l5
    refine ⟨5, s5, (((run1.trans run2).trans run3).trans run4).trans run5, ?_⟩
    simp only [ite_eq_right hz]
    refine ⟨h5.toCalleeState, Nat.zero_le _, ?_, h5.src, h5.length, h5.dst,
      h5.resultLength, ?_, ?_⟩
    · rw [ite_eq_left (Nat.pos_of_ne_zero hz)]
      exact e5.rip
    · exact (a5.read (n := 64) (r := 8) (by simp)).trans r4
    · intro i hi
      omega

end Base16ct.Proofs.Base16ctUpperEncodeCorrect
