import P256.Proofs.Sec1.Decode.Result.Route
import P256.Proofs.Keygen.SignedNormalize.Select.Cmove
import X86Proofs.Instructions.And.Generated.R8Imm8.Triple
import X86Proofs.Instructions.Test.Generated.R8.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decode.Result

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions.MovzxByte
open P256.Proofs.Keygen.Multiply.Inverse.SafeGcd.SignedNormalize

def choice (tag valid : BitVec 8) : BitVec 8 := if tag = 0 then 0 else valid &&& 1

theorem select [Bindings] {s : RamState} {boundary : ReturnBoundary} (tag valid : BitVec 8)
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (outside : ¬ InProgram boundary.rip)
    (rip : s.RIP = 0x10e659) (readable : MemReadable s (stackPtr s + 72) 1)
    (validByte : memLoad s.external (stackPtr s + 72) 8 = valid)
    (tagRegister : s.regValue .rax = tag.setWidth 64) (zero : s.regValue .r12 = 0) :
    ∃ t, Advances boundary 5 s t ∧ ReadyToStep t ∧ t.RIP = 0x10e66a ∧
      t.regValue .rax = (choice tag valid).setWidth 64 ∧
      AgreesExcept [.reg 0, .reg 1, .flags, .rip] s t := by
  obtain ⟨a, aa, ra, ea⟩ :=
    (movzx_r32_m8_effect_step 0x10e659 1 (.sib 4 none 0 (.d8 72))
      (by decide) rfl rfl).advances ready
      (programText_slice (programLoaded_codeIn loaded) 0xe659 _
        (by decide) (by decide +kernel)) ⟨rip, readable⟩
      (boundary_ne_program outside (inProgram_of_textOffset 0xe65e (by decide)))
  have ga : AgreesExcept [.reg 1, .rip] s a := ea.agrees
  have ma := ga.external (by simp [Component.Covers])
  have cx : a.regValue .rcx = valid.setWidth 64 := by
    exact (show a.regValue .rcx = (memLoad s.external (stackPtr s + 72) 8).setWidth 64
      from ea.writes).trans (congrArg (BitVec.setWidth 64) validByte)
  obtain ⟨b, ab, rb, eb⟩ := (and_r8_imm8_effect_step 0x10e65e 0xe1 1 rfl rfl (by decide)).advances ra
    (programText_slice ((programLoaded_codeIn loaded).of_external_eq ma) 0xe65e _
      (by decide) (by decide +kernel)) ea.rip
    (boundary_ne_program outside (inProgram_of_textOffset 0xe661 (by decide)))
  have gb : AgreesExcept [.reg 1, .flags, .rip] a b := eb.agrees
  have mb := (ga.trans gb).external (by simp [Component.Covers])
  have cl : (Operand.reg 1 : Operand 8).read b = valid &&& 1 := by
    change (b.regValue .rcx).setWidth 8 = _
    rw [show b.regValue .rcx = mergeGPR 8
      (((Operand.reg 1 : Operand 8).read a) &&& 1) (a.regValue .rcx) from eb.writes, setWidth_mergeGPR8]
    change (a.regValue .rcx).setWidth 8 &&& 1 = _
    rw [cx, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64), BitVec.setWidth_eq]
  have al : (Operand.reg 0 : Operand 8).read b = tag := by
    have h := ((ga.trans gb).read (n := 64) (r := 0) (by simp)).trans tagRegister
    change b.regValue .rax = tag.setWidth 64 at h
    change (b.regValue .rax).setWidth 8 = _
    rw [h, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64), BitVec.setWidth_eq]
  obtain ⟨c, ac, rc, ec⟩ := (test_r8_r8_effect_step 0x10e661 0xc0 rfl (by decide) (by decide)).advances rb
    (programText_slice ((programLoaded_codeIn loaded).of_external_eq mb) 0xe661 _
      (by decide) (by decide +kernel)) eb.rip
    (boundary_ne_program outside (inProgram_of_textOffset 0xe663 (by decide)))
  have gc : AgreesExcept [.flags, .rip] b c := ec.agrees
  have mc := ((ga.trans gb).trans gc).external (by simp [Component.Covers])
  have zf : (StatusFlags.ofRFLAGS c.RFLAGS).ZF = (tag == 0) := by
    have h := ec.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS c.RFLAGS).ZF = ((((Operand.reg 0 : Operand 8).read b) &&& ((Operand.reg 0 : Operand 8).read b)) == 0) at h
    rw [h, al]
    simp
  obtain ⟨d, ad, rd, ed⟩ := (movzx_r32_r8_effect_step 0x10e663 0xc1 rfl (by decide)).advances rc
    (programText_slice ((programLoaded_codeIn loaded).of_external_eq mc) 0xe663 _
      (by decide) (by decide +kernel)) ec.rip
    (boundary_ne_program outside (inProgram_of_textOffset 0xe666 (by decide)))
  have gd : AgreesExcept [.reg 0, .rip] c d := ed.agrees
  have md := (((ga.trans gb).trans gc).trans gd).external (by simp [Component.Covers])
  have ax : d.regValue .rax = (valid &&& 1).setWidth 64 := by
    have h : d.regValue .rax = ((Operand.reg 1 : Operand 8).read c).setWidth 64 := ed.writes
    rw [h, gc.read (n := 8) (r := 1) (by simp), cl]
  obtain ⟨t, runT, rt, et⟩ := (cmove_r32_r32_rex_effect_step 0x10e666 0x41 0xc4
    (by simp [RexNoWPrefix]) rfl).advances rd
    (programText_slice ((programLoaded_codeIn loaded).of_external_eq md) 0xe666 _
      (by decide) (by decide +kernel)) ed.rip
    (boundary_ne_program outside (inProgram_of_textOffset 0xe66a (by decide)))
  have gt : AgreesExcept [.reg 0, .rip] d t := et.agrees
  refine ⟨t, (((aa.trans ab).trans ac).trans ad).trans runT, rt, et.rip, ?_,
    ((((ga.trans gb).trans gc).trans gd).trans gt).mono (by simp)⟩
  have z : d.regValue .r12 = 0 :=
    ((((ga.trans gb).trans gc).trans gd).read (n := 64) (r := 12) (by simp)).trans zero
  have flag : (StatusFlags.ofRFLAGS d.RFLAGS).ZF = (tag == 0) := by
    rw [gd.agree .flags (by simp) rfl, zf]
  have h : t.regValue .rax = (P256.Proofs.Common.Instructions.cmovR32R32Value 4 0 12 d).setWidth 64 := et.writes
  rw [h]
  simp only [P256.Proofs.Common.Instructions.cmovR32R32Value, condHolds, flag]
  change (if tag == 0 then (d.regValue .r12).setWidth 32 else (d.regValue .rax).setWidth 32).setWidth 64 = _
  rw [z, ax]
  change (if tag == 0#8 then (0#64).setWidth 32 else
    ((valid &&& 1#8).setWidth 64).setWidth 32).setWidth 64 =
    (if tag = 0#8 then 0#8 else valid &&& 1#8).setWidth 64
  by_cases hz : tag = 0#8
  · rw [hz]
    rfl
  · have hb : (tag == 0#8) = false := beq_eq_false_iff_ne.mpr hz
    simp only [hb, Bool.false_eq_true, hz, ite_false]
    change (((valid &&& 1#8).setWidth 64).setWidth 32).setWidth 64 = _
    rw [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64)]
    exact BitVec.setWidth_setWidth (u := 8) (v := 32) (w := 64) (by decide)

end P256.Proofs.Sec1.Decode.Result
