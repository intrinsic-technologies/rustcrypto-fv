import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.Basic
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Test.Generated.R8Imm8.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Branch.Triple

namespace Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine

open Base16ct.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs

theorem mixed_parity_entry [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hRip : s.RIP = 0x1001c5) (hOutside : OutsideMixed boundary.rip) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.RIP = (if (s.regValue .rsi).toNat % 2 = 0 then 0x1001cf else 0x1002fa) ∧
      AgreesExcept [.flags, .rip] s t := by
  obtain ⟨b, runB, readyB, effectB⟩ :=
    (test_r8_imm8_effect_step 0x1001c5 0x40 0xc6 1
      (by unfold RexPrefix; decide) (by decide) (by decide)).advances hReady
      (program_text_slice hCode 0x1c5 4 (by decide +kernel)) hRip
      (outsideMixed_ne (pc := 0x1001c9) hOutside (by decide) (by decide))
  have frameB : AgreesExcept [.flags, .rip] s b := effectB.agrees
  have codeB := frameB.codeIn (by simp [Component.Covers]) hCode
  have hsi : (Operand.reg 6 : Operand 8).read s = (s.regValue .rsi).setWidth 8 :=
    rfl
  have hz : (StatusFlags.ofRFLAGS b.RFLAGS).ZF =
      decide ((s.regValue .rsi).toNat % 2 = 0) := by
    have hz := effectB.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS b.RFLAGS).ZF =
      (((Operand.reg 6 : Operand 8).read s &&& 1) == 0) at hz
    rw [hz, hsi]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    rw [← BitVec.toNat_inj]
    simp [BitVec.toNat_and, Nat.and_one_is_mod]
  have next : (jccEffect 0x1001c9 6 5 ((0x12b : BitVec 32).signExtend 64) b).rip =
      (if (s.regValue .rsi).toNat % 2 = 0 then 0x1001cf else 0x1002fa) := by
    by_cases h : (s.regValue .rsi).toNat % 2 = 0
    · simp [jccEffect, branchEffect, condHolds, hz, h]
    · simp [jccEffect, branchEffect, branchTarget, condHolds, hz, h]
  obtain ⟨t, runT, readyT, effectT⟩ :=
    (jcc_rel32_effect_step 0x1001c9 5 0x12b).advances (boundary := boundary)
    readyB (program_text_slice codeB 0x1c9 6 (by decide +kernel))
    ⟨effectB.rip, fun _ ↦ by decide⟩ (by
      rw [next]
      split <;> exact outsideMixed_ne hOutside (by decide) (by decide))
  have frameT : AgreesExcept [.rip] b t := effectT.agrees
  refine ⟨t, runB.trans runT, readyT,
    frameT.codeIn (by simp [Component.Covers]) codeB, effectT.rip.trans next, (frameB.trans frameT).mono (by simp)⟩

theorem mixed_capacity_entry [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hRip : s.RIP = 0x1001cf) (hOutside : OutsideMixed boundary.rip) :
    ∃ t, Advances boundary 4 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.RIP = (if (s.regValue .rsi).toNat / 2 ≤ (s.regValue .r8).toNat
        then 0x1001de else 0x1002fa) ∧
      t.regValue .r9 = s.regValue .rsi >>> 1 ∧
      AgreesExcept [.reg 9, .flags, .rip] s t := by
  obtain ⟨a, runA, readyA, effectA⟩ :=
    (mov_r64_r64_effect_step 0x1001cf 0x49 0xf1 (by unfold RexWPrefix; decide) (by decide)).advances
      hReady (program_text_slice hCode 0x1cf 3 (by decide +kernel)) hRip
      (outsideMixed_ne (pc := 0x1001d2) hOutside (by decide) (by decide))
  have frameA : AgreesExcept [.reg 9, .rip] s a := effectA.agrees
  have codeA := frameA.codeIn (by simp [Component.Covers]) hCode
  obtain ⟨b, runB, readyB, effectB⟩ :=
    (shr_r64_one_effect_step 0x1001d2 0x49 0xe9
      (by unfold RexWPrefix; decide) (by decide) (by decide)).advances
      readyA (program_text_slice codeA 0x1d2 3 (by decide +kernel)) effectA.rip
      (outsideMixed_ne (pc := 0x1001d5) hOutside (by decide) (by decide))
  have frameB : AgreesExcept [.reg 9, .flags, .rip] a b := effectB.agrees
  have codeB := frameB.codeIn (by simp [Component.Covers]) codeA
  have bx : b.regValue .r9 = s.regValue .rsi >>> 1 := by
    exact effectB.writes.trans (congrArg (fun x : BitVec 64 ↦ x >>> 1) effectA.writes)
  have bc : b.regValue .r8 = s.regValue .r8 :=
    (frameA.trans frameB).read (n := 64) (r := 8) (by simp)
  obtain ⟨c, runC, readyC, effectC⟩ :=
    (cmp_r64_r64_effect_step 0x1001d5 0x4d 0xc1 (by unfold RexWPrefix; decide) (by decide)).advances
      readyB (program_text_slice codeB 0x1d5 3 (by decide +kernel)) effectB.rip
      (outsideMixed_ne (pc := 0x1001d8) hOutside (by decide) (by decide))
  have frameC : AgreesExcept [.flags, .rip] b c := effectC.agrees
  have codeC := frameC.codeIn (by simp [Component.Covers]) codeB
  have condC : condHolds 7 (StatusFlags.ofRFLAGS c.RFLAGS) =
      decide (¬ (s.regValue .rsi).toNat / 2 ≤ (s.regValue .r8).toNat) := by
    have cf := effectC.flags.1
    have zf := effectC.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS c.RFLAGS).CF =
      decide ((b.regValue .r9).toNat < (b.regValue .r8).toNat) at cf
    change (StatusFlags.ofRFLAGS c.RFLAGS).ZF = ((b.regValue .r9 - b.regValue .r8) == 0) at zf
    change (!((StatusFlags.ofRFLAGS c.RFLAGS).CF || (StatusFlags.ofRFLAGS c.RFLAGS).ZF)) = _
    rw [cf, zf, bx, bc]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.not_eq_true', Bool.or_eq_false_iff, decide_eq_false_iff_not,
      decide_eq_true_eq, beq_eq_false_iff_ne]
    rw [ne_eq, BitVec.sub_eq_iff_eq_add]
    simp only [BitVec.ofNat_eq_ofNat, BitVec.zero_add, ← BitVec.toNat_inj,
      BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.reducePow]
    omega
  have next : (jccEffect 0x1001d8 6 7 ((0x11c : BitVec 32).signExtend 64) c).rip =
      (if (s.regValue .rsi).toNat / 2 ≤ (s.regValue .r8).toNat
        then 0x1001de else 0x1002fa) := by
    change (if condHolds 7 (StatusFlags.ofRFLAGS c.RFLAGS) then
      (0x1002fa : BitVec 64) else 0x1001de) = _
    rw [condC]
    simp only [decide_eq_true_eq, ite_not]
  obtain ⟨t, runT, readyT, effectT⟩ :=
    (jcc_rel32_effect_step 0x1001d8 7 0x11c).advances (boundary := boundary)
    readyC (program_text_slice codeC 0x1d8 6 (by decide +kernel))
    ⟨effectC.rip, fun _ ↦ by decide⟩ (by
      rw [next]
      split <;> exact outsideMixed_ne hOutside (by decide) (by decide))
  have frameT : AgreesExcept [.rip] c t := effectT.agrees
  refine ⟨t, ((runA.trans runB).trans runC).trans runT, readyT,
    frameT.codeIn (by simp [Component.Covers]) codeC, effectT.rip.trans next, ?_, ?_⟩
  · exact ((frameC.trans frameT).read (n := 64) (r := 9) (by simp)).trans bx
  · exact (((frameA.trans frameB).trans frameC).trans frameT).mono (by simp)

theorem mixed_empty_entry [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hRip : s.RIP = 0x1001de) (hOutside : OutsideMixed boundary.rip) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.RIP = (if s.regValue .rsi = 0 then 0x1002fb else 0x1001e7) ∧
      AgreesExcept [.flags, .rip] s t := by
  obtain ⟨a, runA, readyA, effectA⟩ :=
    (test_r64_r64_effect_step 0x1001de 0x48 0xf6
      (by unfold RexWPrefix; decide) (by decide)).advances
      hReady (program_text_slice hCode 0x1de 3 (by decide +kernel)) hRip
      (outsideMixed_ne (pc := 0x1001e1) hOutside (by decide) (by decide))
  have frameA : AgreesExcept [.flags, .rip] s a := effectA.agrees
  have codeA := frameA.codeIn (by simp [Component.Covers]) hCode
  have hz : (StatusFlags.ofRFLAGS a.RFLAGS).ZF = (s.regValue .rsi == 0) := by
    have hz := effectA.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS a.RFLAGS).ZF =
      ((s.regValue .rsi &&& s.regValue .rsi) == 0) at hz
    simpa only [BitVec.and_self] using hz
  have next : (jccEffect 0x1001e1 6 4 ((0x114 : BitVec 32).signExtend 64) a).rip =
      (if s.regValue .rsi = 0 then 0x1002fb else 0x1001e7) := by
    simp [jccEffect, branchEffect, branchTarget, condHolds, hz]
  obtain ⟨t, runT, readyT, effectT⟩ :=
    (jcc_rel32_effect_step 0x1001e1 4 0x114).advances (boundary := boundary)
    readyA (program_text_slice codeA 0x1e1 6 (by decide +kernel))
    ⟨effectA.rip, fun _ ↦ by decide⟩ (by
      rw [next]
      split <;> exact outsideMixed_ne hOutside (by decide) (by decide))
  have frameT : AgreesExcept [.rip] a t := effectT.agrees
  exact ⟨t, runA.trans runT, readyT, frameT.codeIn (by simp [Component.Covers]) codeA,
    effectT.rip.trans next, (frameA.trans frameT).mono (by simp)⟩

end Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine
