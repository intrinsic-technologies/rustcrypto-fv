import P256.Proofs.Sec1.SquareRoot.Exponent.Position
import P256.Proofs.Sec1.SquareRoot.Exponent.ReadDigit.State
import X86Proofs.Instructions.Dec.Generated.R.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Mov.Triple
import P256.Proofs.Common.Instructions.CmovMemory.Effect

set_option autoImplicit false

open P256.Proofs.Common.Instructions (cmov_r32_m32_rex_effect_step)
open P256.Proofs.Program

namespace P256.Proofs.Sec1.SquareRoot

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem exponent_next_word_prepare [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {x n : Nat} (ctx : ExponentPre s boundary x) (hp : ExponentPosition s t x n)
    (hnpos : 0 < n) (hn : n < 64) (hmod : n % 16 = 0) (hip : t.RIP = 0x115499) :
    ∃ u, Advances boundary 4 t u ∧ ReadyToStep u ∧ u.RIP = 0x1154ab ∧
      u.regValue .rbp = BitVec.ofNat 64 ((n - 1) / 16) ∧
      u.regValue .r14 = 16 ∧ AgreesExcept [.reg 5, .reg 14, .flags, .rip] t u := by
  have hnext (offset : Nat) (ho : offset < 118431) :
      Extracted.textAddress + BitVec.ofNat 64 offset ≠ boundary.rip :=
    boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset offset ho)
  have hc := programLoaded_codeIn hp.frame.loaded
  have hc1 : CodeIn (codeRange 0x115499 [0x48,0xff,0xcd]) t :=
    programText_slice hc 0x15499 _ (by decide) (by decide +kernel)
  obtain ⟨t1, ha1, hr1, he1⟩ :=
    (dec_r64_effect_step 0x115499 0x48 0xcd (by constructor <;> rfl) rfl rfl).advances
      (readyToStep hp.frame.machine hp.frame.bindingsSupported) hc1 hip (hnext 0x1549c (by decide))
  have hs1 : AgreesExcept [.reg 5, .flags, .rip] t t1 := he1.agrees
  have hv1 : (Operand.reg 5 : Operand 64).read t1 =
      BitVec.ofNat 64 (n / 16) - 1 := by
    exact he1.writes.trans (congrArg (· - 1) hp.word)
  have hb1 : (Operand.reg 3 : Operand 64).read t1 = 3 :=
    (hs1.read (by decide)).trans hp.firstWord
  have hc2 : CodeIn (codeRange 0x11549c [0x48,0x39,0xdd]) t1 :=
    programText_slice (hs1.codeIn (by simp [Component.Covers]) hc) 0x1549c _
      (by decide) (by decide +kernel)
  obtain ⟨t2, ha2, hr2, he2⟩ :=
    (cmp_r64_r64_effect_step 0x11549c 0x48 0xdd (by constructor <;> rfl) rfl).advances
      hr1 hc2 he1.rip (hnext 0x1549f (by decide))
  have hs2 : AgreesExcept [.flags, .rip] t1 t2 := he2.agrees
  have hf2 : (StatusFlags.ofRFLAGS t2.RFLAGS).ZF = false := by
    have hf := he2.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS t2.RFLAGS).ZF =
      (((Operand.reg 5 : Operand 64).read t1 - (Operand.reg 3 : Operand 64).read t1) == 0) at hf
    rw [hf, hv1, hb1]
    exact (show ∀ i : Fin 64,
      ((BitVec.ofNat 64 (i.val / 16) - 1 - 3) == 0) = false by decide +kernel) ⟨n, hn⟩
  have hag2 : AgreesExcept [.reg 5, .flags, .rip] t t2 :=
    (hs1.trans hs2).mono (by
      intro c hc
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
      grind only)
  have hc3 : CodeIn (codeRange 0x11549f [0x41,0xbe,16,0,0,0]) t2 :=
    programText_slice (hag2.codeIn (by simp [Component.Covers]) hc) 0x1549f _
      (by decide) (by decide +kernel)
  obtain ⟨t3, ha3, hr3, he3⟩ :=
    (mov_r32_imm32_rex_effect_step 0x11549f 0x41 0xbe
      (by simp [RexNoWPrefix]) (by decide) 16).advances
      hr2 hc3 he2.rip (hnext 0x154a5 (by decide))
  have hs3 : AgreesExcept [.reg 14, .rip] t2 t3 := he3.agrees
  have hag3 : AgreesExcept [.reg 5, .reg 14, .flags, .rip] t t3 :=
    (hag2.trans hs3).mono (by
      intro c hc
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
      grind only)
  have hf3 : (StatusFlags.ofRFLAGS t3.RFLAGS).ZF = false := by
    rw [hs3.rflags (by decide) (by decide), hf2]
  have hv3 : (Operand.reg 14 : Operand 64).read t3 = 16 := he3.writes
  have hl3 : (Operand.reg 14 : Operand 32).read t3 = 16 :=
    congrArg (BitVec.setWidth 32) hv3
  have hframe3 := hp.frame.of_registers hr3 hag3 (by decide) (by simp [Component.Covers])
  have haddr : (AddrMode.sib 4 none 0 (.d8 0x78)).addr t3 0x1154ab =
      exponentFrameBase s + 0x78 := by
    change t3.regValue .rsp + 0x78 = _
    rw [hframe3.rsp]
  have hread : MemReadable t3 ((AddrMode.sib 4 none 0 (.d8 0x78)).addr t3 0x1154ab) 4 := by
    rw [haddr]
    exact hframe3.stack_readable ctx (by decide)
  have hc4 : CodeIn (codeRange 0x1154a5 [0x44,0x0f,0x44,0x74,0x24,0x78]) t3 :=
    programText_slice (hag3.codeIn (by simp [Component.Covers]) hc) 0x154a5 _
      (by decide) (by decide +kernel)
  obtain ⟨t4, ha4, hr4, he4⟩ := (cmov_r32_m32_rex_effect_step 0x1154a5 0x44 0x44
      (by simp [RexNoWPrefix]) (Or.inr (Or.inl rfl)) 6
      (.sib 4 none 0 (.d8 0x78)) (by simp [AddrMode.Valid]) rfl rfl).advances
    hr3 hc4 ⟨he3.rip, hread⟩ (hnext 0x154ab (by decide))
  have hs4 : AgreesExcept [.reg 14, .rip] t3 t4 := he4.agrees
  refine ⟨t4, ((ha1.trans ha2).trans ha3).trans ha4, hr4, he4.rip, ?_, ?_, ?_⟩
  · change (Operand.reg 5 : Operand 64).read t4 = _
    rw [hs4.read (by decide), hs3.read (by decide), hs2.read (by decide), hv1]
    exact (show ∀ i : Fin 64, 0 < i.val → i.val % 16 = 0 →
      BitVec.ofNat 64 (i.val / 16) - 1 = BitVec.ofNat 64 ((i.val - 1) / 16)
      by decide +kernel) ⟨n, hn⟩ hnpos hmod
  · have hh := he4.writes
    change (Operand.reg 14 : Operand 64).read t4 =
      (if (StatusFlags.ofRFLAGS t3.RFLAGS).ZF then _
      else (Operand.reg 14 : Operand 32).read t3).setWidth 64 at hh
    simp only [hf3, Bool.false_eq_true, ite_false, hl3] at hh
    exact hh
  · exact (hag3.trans hs4).mono (by
      intro c hc
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
      grind only)

end P256.Proofs.Sec1.SquareRoot
