import P256.Proofs.Sec1.SquareRoot.Exponent.SquareFour.Frame
import P256.Proofs.Common.Instructions.LegacyLoad
import X86Proofs.Instructions.Inc.Generated.R.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

open P256.Proofs.Program
open P256.Spec.Program.Routines

namespace P256.Proofs.Sec1.SquareRoot.SquareFour

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem counter [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x k : Nat}
    (ctx : ExponentPre s boundary x) (frame : ExponentFrame s t)
    (hip : t.RIP = 0x11580d) (hk : k < 4)
    (hcounter : (Operand.mem (exponentFrameBase s + 0x7c) : Operand 32).read t = BitVec.ofNat 32 k) :
    ∃ u, Advances boundary 4 t u ∧ ReadyToStep u ∧
      u.RIP = (if k = 3 then 0x11581c else 0x115510) ∧
      (Operand.reg 0 : Operand 64).read u = BitVec.ofNat 64 (k + 1) ∧
      AgreesExcept [.reg 0, .flags, .rip] t u := by
  have hnext (offset : Nat) (ho : offset < 118431) :
      Extracted.textAddress + BitVec.ofNat 64 offset ≠ boundary.rip :=
    boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset offset ho)
  have hc := programLoaded_codeIn frame.loaded
  have haddr : (AddrMode.sib 4 none 0 (.d8 0x7c)).addr t 0x115811 =
      exponentFrameBase s + 0x7c := by
    change t.regValue .rsp + 0x7c = _
    rw [frame.rsp]
  have hread : MemReadable t ((AddrMode.sib 4 none 0 (.d8 0x7c)).addr t 0x115811) 4 := by
    rw [haddr]
    exact stack_readable ctx frame (offset := 0x7c) (len := 4) (by decide) (by decide)
  obtain ⟨t1, ha1, hr1, he1⟩ :=
    (P256.Proofs.Common.Instructions.LegacyLoad.mov_r32_m32_legacy_effect_step 0x11580d 0
      (.sib 4 none 0 (.d8 0x7c)) (by constructor <;> decide) rfl rfl).advances
      (readyToStep frame.machine frame.bindingsSupported)
      (programText_slice hc 0x1580d [0x8b,0x44,0x24,0x7c] (by decide) (by decide +kernel))
      ⟨hip, hread⟩ (hnext 0x15811 (by decide))
  have hs1 : AgreesExcept [.reg 0, .rip] t t1 := he1.agrees
  have hv1 : (Operand.reg 0 : Operand 64).read t1 = BitVec.ofNat 64 k := by
    have hh := he1.writes
    change (Operand.reg 0 : Operand 64).read t1 =
      ((Operand.mem ((AddrMode.sib 4 none 0 (.d8 0x7c)).addr t 0x115811) : Operand 32).read t).setWidth 64 at hh
    rw [hh, haddr, hcounter]
    exact BitVec.setWidth_ofNat_of_le_of_lt (by decide) (by omega)
  have hc1 := hs1.codeIn (by simp [Component.Covers]) hc
  obtain ⟨t2, ha2, hr2, he2⟩ := (inc_r32_effect_step 0x115811 0xc0 rfl rfl).advances
    hr1 (programText_slice hc1 0x15811 [0xff,0xc0] (by decide) (by decide +kernel))
    he1.rip (hnext 0x15813 (by decide))
  have hs2 : AgreesExcept [.reg 0, .flags, .rip] t1 t2 := he2.agrees
  have hv2 : (Operand.reg 0 : Operand 64).read t2 = BitVec.ofNat 64 (k + 1) := by
    have hv1low : (Operand.reg 0 : Operand 32).read t1 = BitVec.ofNat 32 k := by
      change ((Operand.reg 0 : Operand 64).read t1).setWidth 32 = _
      rw [hv1, BitVec.setWidth_ofNat_of_le (by decide)]
    have hh := he2.writes
    change (Operand.reg 0 : Operand 64).read t2 =
      ((Operand.reg 0 : Operand 32).read t1 + 1).setWidth 64 at hh
    rw [hh, hv1low]
    exact (show ∀ k : Fin 4, (BitVec.ofNat 32 k.val + 1).setWidth 64 =
      BitVec.ofNat 64 (k.val + 1) by decide +kernel) ⟨k, hk⟩
  have hc2 := hs2.codeIn (by simp [Component.Covers]) hc1
  obtain ⟨t3, ha3, hr3, he3⟩ := (cmp_r32_imm8_effect_step 0x115813 0xf8 4 rfl rfl).advances
    hr2 (programText_slice hc2 0x15813 [0x83,0xf8,4] (by decide) (by decide +kernel))
    he2.rip (hnext 0x15816 (by decide))
  have hs3 : AgreesExcept [.flags, .rip] t2 t3 := he3.agrees
  have hf3 : (StatusFlags.ofRFLAGS t3.RFLAGS).ZF = decide (k = 3) := by
    have hv2low : (Operand.reg 0 : Operand 32).read t2 = BitVec.ofNat 32 (k + 1) := by
      change ((Operand.reg 0 : Operand 64).read t2).setWidth 32 = _
      rw [hv2, BitVec.setWidth_ofNat_of_le (by decide)]
    have hh := he3.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS t3.RFLAGS).ZF =
      (((Operand.reg 0 : Operand 32).read t2 - 4#32) == 0) at hh
    rw [hh, hv2low]
    exact (show ∀ k : Fin 4, (BitVec.ofNat 32 (k.val + 1) - 4#32 == 0) =
      decide (k.val = 3) by decide +kernel) ⟨k, hk⟩
  have hc3 := hs3.codeIn (by simp [Component.Covers]) hc2
  obtain ⟨u, step, hru, heu⟩ := jcc_rel32_effect_step 0x115816 5 0xfffffcf4 t3 hr3
    (programText_slice hc3 0x15816 [0xf,0x85,0xf4,0xfc,0xff,0xff] (by decide) (by decide +kernel))
    ⟨he3.rip, fun _ => by decide⟩
  have hs4 : AgreesExcept [.rip] t3 u := heu.agrees
  have hipu : u.RIP = (if k = 3 then 0x11581c else 0x115510) := by
    rw [heu.rip]
    change (if !(StatusFlags.ofRFLAGS t3.RFLAGS).ZF then (0x115510 : BitVec 64) else 0x11581c) = _
    rw [hf3]
    by_cases he : k = 3 <;> simp [he]
  have ha4 : Advances boundary 1 t3 u := by
    apply Advances.of_step step
    left
    rw [hipu]
    split
    · exact hnext 0x1581c (by decide)
    · exact hnext 0x15510 (by decide)
  refine ⟨u, ((ha1.trans ha2).trans ha3).trans ha4, hru, hipu,
    (hs4.read (by decide)).trans ((hs3.read (by decide)).trans hv2), ?_⟩
  exact (((hs1.trans hs2).trans hs3).trans hs4).mono (by
    intro c hm
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
    grind only)

theorem inner_counter [Bindings] {t : RamState} {boundary : ReturnBoundary} {k : Nat}
    (ready : ReadyToStep t) (code : CodeIn Extracted.programSections.toCodeMap t)
    (outside : ¬ InProgram boundary.rip) (hip : t.RIP = 0x11567b) (hk : k < 4)
    (hcounter : (Operand.reg 13 : Operand 64).read t = BitVec.ofNat 64 k) :
    ∃ u, Advances boundary 4 t u ∧ ReadyToStep u ∧
      u.RIP = (if k = 3 then 0x11568e else 0x115550) ∧
      (Operand.reg 13 : Operand 64).read u = BitVec.ofNat 64 (k + 1) ∧
      (Operand.reg 14 : Operand 64).read u = 0 ∧
      AgreesExcept [.reg 13, .reg 14, .flags, .rip] t u := by
  have hnext (offset : Nat) (ho : offset < 118431) :
      Extracted.textAddress + BitVec.ofNat 64 offset ≠ boundary.rip :=
    boundary_ne_program outside (inProgram_of_textOffset offset ho)
  obtain ⟨t1, ha1, hr1, he1⟩ :=
    (inc_r64_effect_step 0x11567b 0x49 0xc5 (by simp [RexWPrefix]) rfl rfl).advances ready
      (programText_slice code 0x1567b [0x49,0xff,0xc5] (by decide) (by decide +kernel))
      hip (hnext 0x1567e (by decide))
  have hs1 : AgreesExcept [.reg 13, .flags, .rip] t t1 := he1.agrees
  have hv1 : (Operand.reg 13 : Operand 64).read t1 = BitVec.ofNat 64 (k + 1) := by
    have hh := he1.writes
    change (Operand.reg 13 : Operand 64).read t1 = (Operand.reg 13 : Operand 64).read t + 1 at hh
    rw [hh, hcounter, BitVec.ofNat_add]
    rfl
  have hc1 := hs1.codeIn (by simp [Component.Covers]) code
  obtain ⟨t2, ha2, hr2, he2⟩ := (mov_r32_imm32_rex_effect_step 0x11567e 0x41 0xbe (by simp [RexNoWPrefix]) (by decide) 0).advances
    hr1 (programText_slice hc1 0x1567e [0x41,0xbe,0,0,0,0] (by decide) (by decide +kernel))
    he1.rip (hnext 0x15684 (by decide))
  have hs2 : AgreesExcept [.reg 14, .rip] t1 t2 := he2.agrees
  have hv2 : (Operand.reg 14 : Operand 64).read t2 = 0 := he2.writes
  have hc2 := hs2.codeIn (by simp [Component.Covers]) hc1
  obtain ⟨t3, ha3, hr3, he3⟩ :=
    (cmp_r64_imm8_effect_step 0x115684 0x49 0xfd 4 (by simp [RexWPrefix]) rfl rfl).advances
      hr2 (programText_slice hc2 0x15684 [0x49,0x83,0xfd,4] (by decide) (by decide +kernel))
      he2.rip (hnext 0x15688 (by decide))
  have hs3 : AgreesExcept [.flags, .rip] t2 t3 := he3.agrees
  have hf3 : (StatusFlags.ofRFLAGS t3.RFLAGS).ZF = decide (k = 3) := by
    have hh := he3.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS t3.RFLAGS).ZF =
      (((Operand.reg 13 : Operand 64).read t2 - 4#64) == 0) at hh
    rw [hh, hs2.read (by decide), hv1]
    exact (show ∀ k : Fin 4, (BitVec.ofNat 64 (k.val + 1) - 4#64 == 0) =
      decide (k.val = 3) by decide +kernel) ⟨k, hk⟩
  have hc3 := hs3.codeIn (by simp [Component.Covers]) hc2
  obtain ⟨u, step, hru, heu⟩ := jcc_rel32_effect_step 0x115688 5 0xfffffec2 t3 hr3
    (programText_slice hc3 0x15688 [0xf,0x85,0xc2,0xfe,0xff,0xff] (by decide) (by decide +kernel))
    ⟨he3.rip, fun _ => by decide⟩
  have hs4 : AgreesExcept [.rip] t3 u := heu.agrees
  have hipu : u.RIP = (if k = 3 then 0x11568e else 0x115550) := by
    rw [heu.rip]
    change (if !(StatusFlags.ofRFLAGS t3.RFLAGS).ZF then (0x115550 : BitVec 64) else 0x11568e) = _
    rw [hf3]
    by_cases he : k = 3 <;> simp [he]
  have ha4 : Advances boundary 1 t3 u := by
    apply Advances.of_step step
    left
    rw [hipu]
    split
    · exact hnext 0x1568e (by decide)
    · exact hnext 0x15550 (by decide)
  exact ⟨u, ((ha1.trans ha2).trans ha3).trans ha4, hru, hipu,
    (hs4.read (by decide)).trans ((hs3.read (by decide)).trans ((hs2.read (by decide)).trans hv1)),
    (hs4.read (by decide)).trans ((hs3.read (by decide)).trans hv2),
    (((hs1.trans hs2).trans hs3).trans hs4).mono (by
      intro c hm
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
      grind only)⟩

end P256.Proofs.Sec1.SquareRoot.SquareFour
