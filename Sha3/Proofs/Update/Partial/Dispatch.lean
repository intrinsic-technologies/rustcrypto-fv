import Sha3.Proofs.Update.Partial.Control
import Sha3.Proofs.X86.Instructions.Sub.Triple

namespace Sha3.Proofs.Update.Partial

open X86 X86.Machine X86.UserProcess X86Proofs Sha3.Spec.Program

theorem nonzero_cursor [Bindings] (v : Variant) (boundary : ReturnBoundary)
    (hb : ¬ InProgram boundary.rip) (s : RamState) (position length : Nat)
    (hposition : 0 < position) (hcursor_lt : position < v.rate) (hlength : length < 2 ^ 64)
    (hready : ReadyToStep s) (hcode : CodeIn Extracted.programImage s)
    (hip : s.RIP = partialAddress v)
    (hcursor : (Operand.reg 0 : Operand 64).read s = BitVec.ofNat 64 position)
    (hlen : (Operand.reg 1 : Operand 64).read s = BitVec.ofNat 64 length) :
    ∃ t, Advances boundary 7 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.RIP = v.updateAddress + (if v.rate - position ≤ length then 0x54#64 else 0x29#64) ∧
      (Operand.reg 2 : Operand 64).read t = BitVec.ofNat 64 (v.rate - position) ∧
      (Operand.reg 12 : Operand 64).read t =
        BitVec.ofNat 64 length - BitVec.ofNat 64 (v.rate - position) ∧
      AgreesExcept [.reg 2, .reg 12, .flags, .rip] s t := by
  have hrate := v.rate_le
  have hp64 : position < 2 ^ 64 := by omega
  obtain ⟨s1, a1, r1, c1, e1⟩ := scalar_advance (v := v)
    (effect := testR64R64Effect (v.updateAddress + 0x14#64) 0#5 0#5)
    (test_r64_r64_effect_step (v.updateAddress + 0x14#64) 0x48 0xc0
      (by unfold RexWPrefix; decide) (by decide))
    (by cases v <;> decide +kernel) hready hcode hip
    (by simp [Component.Covers])
    (by simpa only [testR64R64Effect, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.ofNat_eq_ofNat] using offset_inProgram v 0x17 (by decide)) hb
  have hz : condHolds 4#4 (StatusFlags.ofRFLAGS s1.RFLAGS) = false := by
    have h := e1.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS s1.RFLAGS).ZF =
      (((Operand.reg 0 : Operand 64).read s &&& (Operand.reg 0 : Operand 64).read s) == 0) at h
    change (StatusFlags.ofRFLAGS s1.RFLAGS).ZF = false
    rw [h, hcursor, BitVec.and_self]
    simp only [beq_eq_false_iff_ne]
    intro he
    have he' := congrArg BitVec.toNat he
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp64, BitVec.reduceToNat] at he'
    omega
  obtain ⟨s2, a2, r2, c2, e2⟩ := scalar_advance (v := v)
    (jcc_rel8_effect_step (v.updateAddress + 0x17#64) 4#4 0x2f#8)
    (by cases v <;> decide +kernel) r1 c1
    ⟨by simpa only [testR64R64Effect, BitVec.add_assoc, BitVec.reduceAdd] using e1.rip,
      fun hh ↦ by simp only [hz, Bool.false_eq_true] at hh⟩
    (by simp [jccEffect, Component.Covers])
    (by simpa only [jccEffect, branchEffect, hz, Bool.false_eq_true, ↓reduceIte, BitVec.add_assoc,
      BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using offset_inProgram v 0x19 (by decide)) hb
  have ip2 : s2.RIP = v.updateAddress + 0x19#64 := by
    simpa only [jccEffect, branchEffect, hz, Bool.false_eq_true, ↓reduceIte, BitVec.add_assoc,
      BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using e2.rip
  obtain ⟨s3, a3, r3, c3, e3⟩ := scalar_advance (v := v)
    (effect := movR32Imm32Effect (v.updateAddress + 0x19#64) 5 2#5
      (BitVec.ofNat 32 v.rate))
    (mov_r32_imm32_effect_step (v.updateAddress + 0x19#64) 0xba
      (by decide) (BitVec.ofNat 32 v.rate))
    (by cases v <;> decide +kernel) r2 c2 ip2
    (by simp [Component.Covers])
    (by simpa only [movR32Imm32Effect, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.ofNat_eq_ofNat] using offset_inProgram v 0x1e (by decide)) hb
  have hr3 : (Operand.reg 2 : Operand 64).read s3 = BitVec.ofNat 64 v.rate := by
    have h := e3.writes
    change (Operand.reg 2 : Operand 64).read s3 = (BitVec.ofNat 32 v.rate).setWidth 64 at h
    rw [h]
    cases v <;> rfl
  have hc3 : (Operand.reg 0 : Operand 64).read s3 = BitVec.ofNat 64 position := by
    rw [e3.agrees.read (by simp), e2.agrees.read (by simp [jccEffect]),
      e1.agrees.read (by simp), hcursor]
  obtain ⟨s4, a4, r4, c4, e4⟩ := scalar_advance (v := v)
    (effect := subR64R64Effect (v.updateAddress + 0x1e#64) 2#5 0#5)
    (sub_r64_r64_effect_step (v.updateAddress + 0x1e#64) 0x48 0xc2
      (by unfold RexWPrefix; decide) (by decide))
    (by cases v <;> decide +kernel) r3 c3
    (by simpa only [movR32Imm32Effect, BitVec.add_assoc, BitVec.ofNat_eq_ofNat,
      BitVec.reduceAdd] using e3.rip)
    (by simp [Component.Covers])
    (by simpa only [subR64R64Effect, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.ofNat_eq_ofNat] using offset_inProgram v 0x21 (by decide)) hb
  have hr4 : (Operand.reg 2 : Operand 64).read s4 = BitVec.ofNat 64 (v.rate - position) := by
    have h := e4.writes
    change (Operand.reg 2 : Operand 64).read s4 =
      (Operand.reg 2 : Operand 64).read s3 - (Operand.reg 0 : Operand 64).read s3 at h
    rw [h, hr3, hc3]
    exact BitVec.ofNat_sub_ofNat_of_le _ _ hp64 (by omega)
  obtain ⟨s5, a5, r5, c5, e5⟩ := scalar_advance (v := v)
    (effect := movR64R64Effect (v.updateAddress + 0x21#64) 12#5 1#5)
    (mov_r64_r64_effect_step (v.updateAddress + 0x21#64) 0x49 0xcc
      (by unfold RexWPrefix; decide) (by decide))
    (by cases v <;> decide +kernel) r4 c4
    (by simpa only [subR64R64Effect, BitVec.add_assoc, BitVec.reduceAdd] using e4.rip)
    (by simp [Component.Covers])
    (by simpa only [movR64R64Effect, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.ofNat_eq_ofNat] using offset_inProgram v 0x24 (by decide)) hb
  have hl5 : (Operand.reg 12 : Operand 64).read s5 = BitVec.ofNat 64 length := by
    have h : (Operand.reg 12 : Operand 64).read s5 = (Operand.reg 1 : Operand 64).read s4 :=
      e5.writes
    rw [h, e4.agrees.read (by simp), e3.agrees.read (by simp),
      e2.agrees.read (by simp [jccEffect]), e1.agrees.read (by simp), hlen]
  have hr5 : (Operand.reg 2 : Operand 64).read s5 = BitVec.ofNat 64 (v.rate - position) :=
    (e5.agrees.read (by simp)).trans hr4
  obtain ⟨s6, a6, r6, c6, e6⟩ := scalar_advance (v := v)
    (effect := subR64R64Effect (v.updateAddress + 0x24#64) 12#5 2#5)
    (sub_r64_r64_effect_step (v.updateAddress + 0x24#64) 0x49 0xd4
      (by unfold RexWPrefix; decide) (by decide))
    (by cases v <;> decide +kernel) r5 c5
    (by simpa only [movR64R64Effect, BitVec.add_assoc, BitVec.reduceAdd] using e5.rip)
    (by simp [Component.Covers])
    (by simpa only [subR64R64Effect, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.ofNat_eq_ofNat] using offset_inProgram v 0x27 (by decide)) hb
  have hcf : condHolds 3#4 (StatusFlags.ofRFLAGS s6.RFLAGS) =
      decide (v.rate - position ≤ length) := by
    have h := e6.flags.1
    change (StatusFlags.ofRFLAGS s6.RFLAGS).CF =
      decide (((Operand.reg 12 : Operand 64).read s5).toNat <
        ((Operand.reg 2 : Operand 64).read s5).toNat) at h
    rw [hl5, hr5] at h
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlength,
      Nat.mod_eq_of_lt (show v.rate - position < 2 ^ 64 by omega)] at h
    change (!(StatusFlags.ofRFLAGS s6.RFLAGS).CF) = _
    by_cases hl : length < v.rate - position
    · have hn : ¬v.rate - position ≤ length := by omega
      simp only [h, hl, hn, decide_true, decide_false, Bool.not_true]
    · have hn : v.rate - position ≤ length := by omega
      simp only [h, hl, hn, decide_true, decide_false, Bool.not_false]
  have htarget : branchTarget (v.updateAddress + 0x27#64) 2
      (BitVec.signExtend 64 0x2b#8) = v.updateAddress + 0x54#64 := by
    simp only [branchTarget, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSignExtend]
  obtain ⟨t, a7, r7, c7, e7⟩ := scalar_advance (v := v)
    (jcc_rel8_effect_step (v.updateAddress + 0x27#64) 3#4 0x2b#8)
    (by cases v <;> decide +kernel) r6 c6
    ⟨by simpa only [subR64R64Effect, BitVec.add_assoc, BitVec.reduceAdd] using e6.rip,
      fun _ ↦ by rw [htarget]; cases v <;> decide⟩
    (by simp [jccEffect, Component.Covers])
    (by
      simp only [jccEffect, branchEffect, htarget, BitVec.add_assoc, BitVec.reduceAdd]
      split <;> exact offset_inProgram v _ (by decide)) hb
  refine ⟨t, (((((a1.trans a2).trans a3).trans a4).trans a5).trans a6).trans a7,
    r7, c7, ?_, ?_, ?_, ?_⟩
  · have h := e7.rip
    simp only [jccEffect, branchEffect, hcf, decide_eq_true_eq, htarget,
      BitVec.add_assoc, BitVec.reduceAdd] at h
    split <;> simp_all only [↓reduceIte]
  · exact (e7.agrees.read (by simp [jccEffect])).trans
      ((e6.agrees.read (by simp)).trans hr5)
  · have h := e6.writes
    change (Operand.reg 12 : Operand 64).read s6 =
      (Operand.reg 12 : Operand 64).read s5 - (Operand.reg 2 : Operand 64).read s5 at h
    rw [e7.agrees.read (by simp [jccEffect]), h, hl5, hr5]
  · apply ((((((e1.agrees.trans e2.agrees).trans e3.agrees).trans e4.agrees).trans
      e5.agrees).trans e6.agrees).trans e7.agrees).mono
    simp only [testR64R64Effect_components, jccEffect, branchEffect_components,
      movR64R64Effect_components, movR32Imm32Effect_components, subR64R64Effect_components]
    intro c hc
    simp_all only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    rcases hc with ((((((rfl | rfl) | rfl) | rfl | rfl) | rfl | rfl | rfl) |
      rfl | rfl) | rfl | rfl | rfl) | rfl <;> simp

end Sha3.Proofs.Update.Partial
