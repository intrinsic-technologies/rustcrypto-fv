import P256.Proofs.Program.Code
import X86Proofs.Instructions.Dec.Generated.R.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset programText_slice)

namespace P256.Proofs.Sec1.SquareRoot

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def exponentSkipsSquares (s : RamState) : Bool :=
  (((Operand.reg 5 : Operand 64).read s - (Operand.reg 3 : Operand 64).read s) == 0) &&
    ((((Operand.reg 14 : Operand 32).read s - 1) - (Operand.reg 13 : Operand 32).read s) == 0)

theorem exponent_window_begin [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (hready : ReadyToStep s) (hcode : CodeIn Extracted.programSections.toCodeMap s)
    (hrip : s.RIP = 0x1154c5) (houtside : ¬ InProgram boundary.rip) :
    ∃ t fuel, Advances boundary fuel s t ∧ ReadyToStep t ∧
      t.RIP = (if exponentSkipsSquares s then 0x11586c else 0x1154d6) ∧
      (Operand.reg 14 : Operand 64).read t =
        ((Operand.reg 14 : Operand 32).read s - 1).setWidth 64 ∧
      AgreesExcept [.reg 14, .flags, .rip] s t := by
  have hnext (offset : Nat) (ho : offset < 118431) :
      Extracted.textAddress + BitVec.ofNat 64 offset ≠ boundary.rip :=
    boundary_ne_program houtside (inProgram_of_textOffset offset ho)
  have hc1 : CodeIn (codeRange 0x1154c5 [0x41, 0xff, 0xce]) s :=
    programText_slice hcode 0x154c5 _ (by decide) (by decide +kernel)
  obtain ⟨s1, hs1, hr1, he1⟩ :=
    (dec_r32_rex_effect_step 0x1154c5 0x41 0xce (by simp [RexNoWPrefix]) rfl rfl).advances
      hready hc1 hrip (hnext 0x154c8 (by decide))
  have ha1 : AgreesExcept [.reg 14, .flags, .rip] s s1 := he1.agrees
  have hv1 : (Operand.reg 14 : Operand 64).read s1 =
      ((Operand.reg 14 : Operand 32).read s - 1).setWidth 64 := he1.writes
  have hcode1 := ha1.codeIn (by simp [Component.Covers]) hcode
  have hc2 : CodeIn (codeRange 0x1154c8 [0x48, 0x39, 0xdd]) s1 :=
    programText_slice hcode1 0x154c8 _ (by decide) (by decide +kernel)
  obtain ⟨s2, hs2, hr2, he2⟩ :=
    (cmp_r64_r64_effect_step 0x1154c8 0x48 0xdd (by constructor <;> rfl) rfl).advances
      hr1 hc2 he1.rip (hnext 0x154cb (by decide))
  have ha2 : AgreesExcept [.flags, .rip] s1 s2 := he2.agrees
  have hf2 : (StatusFlags.ofRFLAGS s2.RFLAGS).ZF =
      (((Operand.reg 5 : Operand 64).read s - (Operand.reg 3 : Operand 64).read s) == 0) := by
    have hf := he2.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS s2.RFLAGS).ZF =
      (((Operand.reg 5 : Operand 64).read s1 - (Operand.reg 3 : Operand 64).read s1) == 0) at hf
    rwa [ha1.read (r := 5) (by simp), ha1.read (r := 3) (by simp)] at hf
  have hcode2 := ha2.codeIn (by simp [Component.Covers]) hcode1
  have hc3 : CodeIn (codeRange 0x1154cb [0x75, 9]) s2 :=
    programText_slice hcode2 0x154cb _ (by decide) (by decide +kernel)
  obtain ⟨s3, hs3, hr3, he3⟩ :=
    jcc_rel8_effect_step 0x1154cb 5 9 s2 hr2 hc3 ⟨he2.rip, fun _ => by decide⟩
  have ha3 : AgreesExcept [.rip] s2 s3 := he3.agrees
  have hip3 : s3.RIP = (if
      ((Operand.reg 5 : Operand 64).read s - (Operand.reg 3 : Operand 64).read s) == 0
      then 0x1154cd else 0x1154d6) := by
    rw [he3.rip]
    simp [jccEffect, branchEffect, condHolds, hf2, branchTarget]
  have had3 : Advances boundary 1 s2 s3 := by
    apply Advances.of_step hs3
    left
    rw [hip3]
    split
    · exact hnext 0x154cd (by decide)
    · exact hnext 0x154d6 (by decide)
  have hag3 : AgreesExcept [.reg 14, .flags, .rip] s s3 :=
    ((ha1.trans ha2).trans ha3).mono (by
      intro c hc
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
      grind only)
  have hv3 : (Operand.reg 14 : Operand 64).read s3 =
      ((Operand.reg 14 : Operand 32).read s - 1).setWidth 64 := by
    rw [ha3.read (by simp), ha2.read (by simp), hv1]
  by_cases hword : (((Operand.reg 5 : Operand 64).read s -
      (Operand.reg 3 : Operand 64).read s) == 0) = true
  · have hip3' : s3.RIP = 0x1154cd := by simpa only [hword, ite_true] using hip3
    have hcode3 := ha3.codeIn (by simp [Component.Covers]) hcode2
    have hc4 : CodeIn (codeRange 0x1154cd [0x45, 0x39, 0xee]) s3 :=
      programText_slice hcode3 0x154cd _ (by decide) (by decide +kernel)
    obtain ⟨s4, hs4, hr4, he4⟩ :=
      (cmp_r32_r32_rex_effect_step 0x1154cd 0x45 0xee (by simp [RexNoWPrefix]) rfl).advances
        hr3 hc4 hip3' (hnext 0x154d0 (by decide))
    have ha4 : AgreesExcept [.flags, .rip] s3 s4 := he4.agrees
    have hv3' : (Operand.reg 14 : Operand 32).read s3 =
        (Operand.reg 14 : Operand 32).read s - 1 := by
      have hh := congrArg (BitVec.setWidth 32) hv3
      simpa only [Operand.read_reg64, Operand.read_reg32,
        BitVec.setWidth_setWidth (by decide : ¬ (64 < 32 ∧ 64 < 32)),
        BitVec.setWidth_eq] using hh
    have hf4 : (StatusFlags.ofRFLAGS s4.RFLAGS).ZF =
        ((((Operand.reg 14 : Operand 32).read s - 1) -
          (Operand.reg 13 : Operand 32).read s) == 0) := by
      have hf := he4.flags.2.2.2.1
      change (StatusFlags.ofRFLAGS s4.RFLAGS).ZF =
        (((Operand.reg 14 : Operand 32).read s3 - (Operand.reg 13 : Operand 32).read s3) == 0) at hf
      rwa [hv3', hag3.read (r := 13) (by simp)] at hf
    have hcode4 := ha4.codeIn (by simp [Component.Covers]) hcode3
    have hc5 : CodeIn (codeRange 0x1154d0 [0x0f, 0x84, 0x96, 3, 0, 0]) s4 :=
      programText_slice hcode4 0x154d0 _ (by decide) (by decide +kernel)
    obtain ⟨s5, hs5, hr5, he5⟩ :=
      jcc_rel32_effect_step 0x1154d0 4 0x396 s4 hr4 hc5 ⟨he4.rip, fun _ => by decide⟩
    have ha5 : AgreesExcept [.rip] s4 s5 := he5.agrees
    have hip5 : s5.RIP = (if exponentSkipsSquares s then 0x11586c else 0x1154d6) := by
      simp only [exponentSkipsSquares, hword, Bool.true_and]
      rw [he5.rip]
      simp [jccEffect, branchEffect, condHolds, hf4, branchTarget]
    have had5 : Advances boundary 1 s4 s5 := by
      apply Advances.of_step hs5
      left
      rw [hip5]
      split
      · exact hnext 0x1586c (by decide)
      · exact hnext 0x154d6 (by decide)
    refine ⟨s5, 5, (((hs1.trans hs2).trans had3).trans hs4).trans had5,
      hr5, hip5, ?_, ?_⟩
    · rw [ha5.read (by simp), ha4.read (by simp), hv3]
    · exact ((hag3.trans ha4).trans ha5).mono (by
        intro c hc
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
        grind only)
  · refine ⟨s3, 3, (hs1.trans hs2).trans had3, hr3, ?_, hv3, hag3⟩
    have hwfalse := Bool.eq_false_iff.mpr hword
    simpa only [exponentSkipsSquares, hwfalse, Bool.false_and, Bool.false_eq_true, ite_false] using hip3

end P256.Proofs.Sec1.SquareRoot
