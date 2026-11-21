import P256.Proofs.Sec1.Decode.Frame
import P256.Proofs.Common.Instructions.Lea32
import P256.Proofs.Common.Instructions.MovzxByte
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decode.Result

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions.Lea32 P256.Proofs.Common.Instructions.MovzxByte

theorem route [Bindings] {s : RamState} {boundary : ReturnBoundary} (tag : BitVec 8)
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (outside : ¬ InProgram boundary.rip)
    (rip : s.RIP = 0x10e632) (readable : MemReadable s (stackPtr s + 156) 1)
    (tagByte : memLoad s.external (stackPtr s + 156) 8 = tag)
    (valid : tag = 0 ∨ tag = 2 ∨ tag = 3 ∨ tag = 4 ∨ tag = 5) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ t.RIP = 0x10e649 ∧
      t.regValue .rax = tag.setWidth 64 ∧
      AgreesExcept [.reg 0, .reg 1, .reg 2, .flags, .rip] s t := by
  obtain ⟨a, aa, ra, ea⟩ :=
    (movzx_r32_m8_effect_step 0x10e632 0 (.sib 4 none 0 (.d32 156))
      (by decide) rfl rfl).advances ready
      (programText_slice (programLoaded_codeIn loaded) 0xe632 _
        (by decide) (by decide +kernel)) ⟨rip, readable⟩
      (boundary_ne_program outside (inProgram_of_textOffset 0xe63a (by decide)))
  have ga : AgreesExcept [.reg 0, .rip] s a := ea.agrees
  have ma := ga.external (by simp [Component.Covers])
  have ax : a.regValue .rax = tag.setWidth 64 := by
    change a.regValue .rax = _
    exact (show a.regValue .rax = (memLoad s.external (stackPtr s + 156) 8).setWidth 64
      from ea.writes).trans (congrArg (BitVec.setWidth 64) tagByte)
  obtain ⟨b, ab, rb, eb⟩ := (movzx_r32_r8_effect_step 0x10e63a 0xc8 rfl (by decide)).advances ra
    (programText_slice ((programLoaded_codeIn loaded).of_external_eq ma) 0xe63a _
      (by decide) (by decide +kernel)) ea.rip
    (boundary_ne_program outside (inProgram_of_textOffset 0xe63d (by decide)))
  have gb : AgreesExcept [.reg 1, .rip] a b := eb.agrees
  have mb := (ga.trans gb).external (by simp [Component.Covers])
  have cx : b.regValue .rcx = tag.setWidth 64 := by
    have h : b.regValue .rcx = ((a.regValue .rax).setWidth 8).setWidth 64 := eb.writes
    simpa only [ax, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64),
      BitVec.setWidth_eq] using h
  obtain ⟨c, ac, rc, ec⟩ :=
    (lea_r32_legacy_effect_step 0x10e63d 2 (.base 1 (.d8 0xfe))
      (by decide) rfl rfl).advances rb
      (programText_slice ((programLoaded_codeIn loaded).of_external_eq mb) 0xe63d _
        (by decide) (by decide +kernel)) eb.rip
      (boundary_ne_program outside (inProgram_of_textOffset 0xe640 (by decide)))
  have gc : AgreesExcept [.reg 2, .rip] b c := ec.agrees
  have mc := ((ga.trans gb).trans gc).external (by simp [Component.Covers])
  have dx : c.regValue .rdx = ((tag.setWidth 64 - (2#64)).setWidth 32).setWidth 64 := by
    have h : c.regValue .rdx = ((b.regValue .rcx + (0xfe#8).signExtend 64).setWidth 32).setWidth 64 := ec.writes
    simpa only [cx, show (0xfe#8).signExtend 64 = -(2#64) from rfl, BitVec.sub_eq_add_neg] using h
  obtain ⟨d, ad, rd, ed⟩ := (cmp_r32_imm8_effect_step 0x10e640 0xfa 4 rfl rfl).advances rc
    (programText_slice ((programLoaded_codeIn loaded).of_external_eq mc) 0xe640 _
      (by decide) (by decide +kernel)) ec.rip
    (boundary_ne_program outside (inProgram_of_textOffset 0xe643 (by decide)))
  have gd : AgreesExcept [.flags, .rip] c d := ed.agrees
  have md := (((ga.trans gb).trans gc).trans gd).external (by simp [Component.Covers])
  have carry : condHolds 2 (StatusFlags.ofRFLAGS d.RFLAGS) = (tag != 0) := by
    have h := ed.flags.1
    change (StatusFlags.ofRFLAGS d.RFLAGS).CF = (cmpSpec ((c.regValue .rdx).setWidth 32) 4).CF at h
    change (StatusFlags.ofRFLAGS d.RFLAGS).CF = _
    rw [h, dx]
    rcases valid with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  have next : (jccEffect 0x10e643 2 2 ((4 : BitVec 8).signExtend 64) d).rip =
      if tag = 0 then 0x10e645 else 0x10e649 := by
    simp only [jccEffect, carry]
    by_cases h : tag = 0 <;> simp [h, branchEffect, branchTarget]
  obtain ⟨e, ae, re, ee⟩ := (jcc_rel8_effect_step 0x10e643 2 4).advances rd
    (programText_slice ((programLoaded_codeIn loaded).of_external_eq md) 0xe643 _
      (by decide) (by decide +kernel)) ⟨ed.rip, by intro; decide⟩
    (by rw [next]; split
        · exact boundary_ne_program outside (inProgram_of_textOffset 0xe645 (by decide))
        · exact boundary_ne_program outside (inProgram_of_textOffset 0xe649 (by decide)))
  have ge : AgreesExcept [.rip] d e := ee.agrees
  have total := (((ga.trans gb).trans gc).trans gd).trans ge
  have after := ((gb.trans gc).trans gd).trans ge
  by_cases hz : tag = 0
  · have me := total.external (by simp [Component.Covers])
    obtain ⟨f, af, rf, ef⟩ := (test_r32_r32_effect_step 0x10e645 0xc9 rfl).advances re
      (programText_slice ((programLoaded_codeIn loaded).of_external_eq me) 0xe645 _
        (by decide) (by decide +kernel)) (by simpa only [hz, ite_true] using ee.rip.trans next)
      (boundary_ne_program outside (inProgram_of_textOffset 0xe647 (by decide)))
    have gf : AgreesExcept [.flags, .rip] e f := ef.agrees
    have mf := (total.trans gf).external (by simp [Component.Covers])
    have ecx : e.regValue .rcx = 0 := by
      have hc : e.regValue .rcx = b.regValue .rcx :=
        ((gc.trans gd).trans ge).read (n := 64) (r := 1) (by simp)
      rw [hc, cx, hz]
      rfl
    have zf : condHolds 5 (StatusFlags.ofRFLAGS f.RFLAGS) = false := by
      have h := ef.flags.2.2.2.1
      change (StatusFlags.ofRFLAGS f.RFLAGS).ZF = ((((e.regValue .rcx).setWidth 32 &&& (e.regValue .rcx).setWidth 32) == 0)) at h
      change (!(StatusFlags.ofRFLAGS f.RFLAGS).ZF) = false
      rw [h, ecx]
      decide +kernel
    obtain ⟨t, runT, rt, et⟩ := (jcc_rel8_effect_step 0x10e647 5 0x69).advances rf
      (programText_slice ((programLoaded_codeIn loaded).of_external_eq mf) 0xe647 _
        (by decide) (by decide +kernel)) ⟨ef.rip, by intro; decide⟩
      (by simpa only [jccEffect, zf, branchEffect, Bool.false_eq_true, ite_false, BitVec.reduceAdd, Extracted.textAddress] using
        boundary_ne_program outside (inProgram_of_textOffset 0xe649 (by decide)))
    have gt : AgreesExcept [.rip] f t := et.agrees
    refine ⟨7, t, (((((aa.trans ab).trans ac).trans ad).trans ae).trans af).trans runT, rt,
      ?_, ?_, ((total.trans gf).trans gt).mono (by simp)⟩
    · exact et.rip.trans (by simp only [jccEffect, zf, branchEffect, Bool.false_eq_true, ite_false]; rfl)
    · exact (((after.trans gf).trans gt).read (n := 64) (r := 0) (by simp)).trans ax
  · exact ⟨5, e, (((aa.trans ab).trans ac).trans ad).trans ae, re,
      by simpa only [hz, ite_false] using ee.rip.trans next,
      (after.read (n := 64) (r := 0) (by simp)).trans ax, total.mono (by simp)⟩

end P256.Proofs.Sec1.Decode.Result
