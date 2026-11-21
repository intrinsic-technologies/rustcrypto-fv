import P256.Proofs.Sec1.SquareRoot.Exponent.Control
import P256.Proofs.Sec1.SquareRoot.Exponent.State
import X86Proofs.Instructions.Test.Generated.RR.Triple

set_option autoImplicit false

open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset programText_slice)

namespace P256.Proofs.Sec1.SquareRoot

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem ExponentLoopState.skips_squares [Bindings] {s t : RamState} {x n : Nat}
    (h : ExponentLoopState s t x n) (hn : 0 < n) (hbound : n ≤ 64) :
    exponentSkipsSquares t = decide (n = 64) := by
  have hw : (Operand.reg 5 : Operand 64).read t = BitVec.ofNat 64 ((n-1)/16) := h.word
  have hb : (Operand.reg 3 : Operand 64).read t = 3 := h.firstWord
  have hi : (Operand.reg 14 : Operand 32).read t = BitVec.ofNat 32 ((n-1)%16+1) := by
    change (t.regValue .r14).setWidth 32 = _
    rw [h.window, BitVec.setWidth_ofNat_of_le (by decide)]
  have hf : (Operand.reg 13 : Operand 32).read t = 15 := by
    change (t.regValue .r13).setWidth 32 = _
    rw [h.firstWindow]
    rfl
  apply Bool.eq_iff_iff.mpr
  simp only [exponentSkipsSquares, hw, hb, hi, hf, Bool.and_eq_true, beq_iff_eq,
    BitVec.sub_eq_iff_eq_add, decide_eq_true_eq]
  constructor
  · rintro ⟨hword, hwindow⟩
    have hword' := congrArg BitVec.toNat hword
    have hwindow' := congrArg BitVec.toNat hwindow
    change ((n - 1) / 16) % 18446744073709551616 = 3 at hword'
    change ((n - 1) % 16 + 1) % 4294967296 = 16 at hwindow'
    omega
  · intro he
    subst n
    decide +kernel

theorem exponent_window_continue [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (hready : ReadyToStep s) (hcode : CodeIn Extracted.programSections.toCodeMap s)
    (hrip : s.RIP = 0x1154c0) (houtside : ¬ InProgram boundary.rip) :
    ∃ t fuel, Advances boundary fuel s t ∧ ReadyToStep t ∧
      t.RIP = (if (Operand.reg 14 : Operand 32).read s = 0 then
        if (Operand.reg 5 : Operand 64).read s = 0 then 0x1158ff else 0x115499
        else 0x1154c5) ∧
      AgreesExcept [.flags, .rip] s t := by
  have hnext (offset : Nat) (ho : offset < 118431) :
      Extracted.textAddress + BitVec.ofNat 64 offset ≠ boundary.rip :=
    boundary_ne_program houtside (inProgram_of_textOffset offset ho)
  have hc1 : CodeIn (codeRange 0x1154c0 [0x45, 0x85, 0xf6]) s :=
    programText_slice hcode 0x154c0 _ (by decide) (by decide +kernel)
  obtain ⟨s1, hs1, hr1, he1⟩ :=
    (test_r32_r32_rex_effect_step 0x1154c0 0x45 0xf6 (by simp [RexNoWPrefix]) rfl).advances
      hready hc1 hrip (hnext 0x154c3 (by decide))
  have ha1 : AgreesExcept [.flags, .rip] s s1 := he1.agrees
  have hf1 : (StatusFlags.ofRFLAGS s1.RFLAGS).ZF =
      ((Operand.reg 14 : Operand 32).read s == 0) := by
    have hf := he1.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS s1.RFLAGS).ZF =
      (((Operand.reg 14 : Operand 32).read s &&& (Operand.reg 14 : Operand 32).read s) == 0) at hf
    simpa only [BitVec.and_self] using hf
  have hcode1 := ha1.codeIn (by simp [Component.Covers]) hcode
  have hc2 : CodeIn (codeRange 0x1154c3 [0x74, 0xcb]) s1 :=
    programText_slice hcode1 0x154c3 _ (by decide) (by decide +kernel)
  obtain ⟨s2, hs2, hr2, he2⟩ :=
    jcc_rel8_effect_step 0x1154c3 4 0xcb s1 hr1 hc2 ⟨he1.rip, fun _ => by decide⟩
  have ha2 : AgreesExcept [.rip] s1 s2 := he2.agrees
  have hip2 : s2.RIP = (if (Operand.reg 14 : Operand 32).read s = 0
      then 0x115490 else 0x1154c5) := by
    rw [he2.rip]
    change (if (StatusFlags.ofRFLAGS s1.RFLAGS).ZF then (0x115490 : BitVec 64)
      else 0x1154c5) = _
    rw [hf1]
    simp only [beq_iff_eq]
  have had2 : Advances boundary 1 s1 s2 := by
    apply Advances.of_step hs2
    left
    rw [hip2]
    split
    · exact hnext 0x15490 (by decide)
    · exact hnext 0x154c5 (by decide)
  have hag2 : AgreesExcept [.flags, .rip] s s2 :=
    (ha1.trans ha2).mono (by
      intro c hc
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
      grind only)
  by_cases hz : (Operand.reg 14 : Operand 32).read s = 0
  · have hip2' : s2.RIP = 0x115490 := by simpa only [hz, ite_true] using hip2
    have hcode2 := ha2.codeIn (by simp [Component.Covers]) hcode1
    have hc3 : CodeIn (codeRange 0x115490 [0x48, 0x85, 0xed]) s2 :=
      programText_slice hcode2 0x15490 _ (by decide) (by decide +kernel)
    obtain ⟨s3, hs3, hr3, he3⟩ :=
      (test_r64_r64_effect_step 0x115490 0x48 0xed (by constructor <;> rfl) rfl).advances
        hr2 hc3 hip2' (hnext 0x15493 (by decide))
    have ha3 : AgreesExcept [.flags, .rip] s2 s3 := he3.agrees
    have hf3 : (StatusFlags.ofRFLAGS s3.RFLAGS).ZF =
        ((Operand.reg 5 : Operand 64).read s == 0) := by
      have hf := he3.flags.2.2.2.1
      change (StatusFlags.ofRFLAGS s3.RFLAGS).ZF =
        (((Operand.reg 5 : Operand 64).read s2 &&& (Operand.reg 5 : Operand 64).read s2) == 0) at hf
      simpa only [BitVec.and_self, hag2.read (r := 5) (by simp)] using hf
    have hcode3 := ha3.codeIn (by simp [Component.Covers]) hcode2
    have hc4 : CodeIn (codeRange 0x115493 [0x0f, 0x84, 0x66, 4, 0, 0]) s3 :=
      programText_slice hcode3 0x15493 _ (by decide) (by decide +kernel)
    obtain ⟨s4, hs4, hr4, he4⟩ :=
      jcc_rel32_effect_step 0x115493 4 0x466 s3 hr3 hc4 ⟨he3.rip, fun _ => by decide⟩
    have ha4 : AgreesExcept [.rip] s3 s4 := he4.agrees
    have hip4 : s4.RIP = (if (Operand.reg 5 : Operand 64).read s = 0
        then 0x1158ff else 0x115499) := by
      rw [he4.rip]
      simp [jccEffect, branchEffect, condHolds, hf3, branchTarget]
    have had4 : Advances boundary 1 s3 s4 := by
      apply Advances.of_step hs4
      left
      rw [hip4]
      split
      · exact hnext 0x158ff (by decide)
      · exact hnext 0x15499 (by decide)
    refine ⟨s4, 4, ((hs1.trans had2).trans hs3).trans had4, hr4, ?_, ?_⟩
    · simpa only [hz, ite_true] using hip4
    · exact ((hag2.trans ha3).trans ha4).mono (by
        intro c hc
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
        grind only)
  · refine ⟨s2, 2, hs1.trans had2, hr2, ?_, hag2⟩
    simpa only [hz, ite_false] using hip2

end P256.Proofs.Sec1.SquareRoot
