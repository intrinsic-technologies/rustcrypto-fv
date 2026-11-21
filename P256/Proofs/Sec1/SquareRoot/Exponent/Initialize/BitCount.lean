import P256.Proofs.Program.Code
import P256.Proofs.Common.Encoding.Serialize.Tail.Selection.Cmov
import X86Proofs.Instructions.Cmp.Generated.Imm32.Triple
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.ExponentInitialize

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions (cmov_r32_r32_effect_step)

theorem bit_count [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (outside : ¬ InProgram boundary.rip)
    (rip : s.RIP = 0x114c22) (count : (Operand.reg 1 : Operand 32).read s = 254) :
    ∃ t, Advances boundary 4 s t ∧ ReadyToStep t ∧ t.RIP = 0x114c33 ∧
      t.regValue .r14 = 254 ∧ AgreesExcept [.reg 0, .reg 14, .flags, .rip] s t := by
  have next (offset : Nat) (bound : offset < 118431) :
      Extracted.textAddress + BitVec.ofNat 64 offset ≠ boundary.rip :=
    boundary_ne_program outside (inProgram_of_textOffset offset bound)
  have code := programLoaded_codeIn loaded
  obtain ⟨a, aa, ra, ea⟩ := (cmp_r32_imm32_effect_step 0x114c22 0xf9 256 rfl rfl).advances
    ready (programText_slice code 0x14c22 _ (by decide) (by decide +kernel)) rip
    (next 0x14c28 (by decide))
  have ga : AgreesExcept [.flags, .rip] s a := ea.agrees
  have carry : (StatusFlags.ofRFLAGS a.RFLAGS).CF = true := by
    have h := ea.flags.1
    change (StatusFlags.ofRFLAGS a.RFLAGS).CF =
      (cmpSpec ((Operand.reg 1 : Operand 32).read s) (256 : BitVec 32)).CF at h
    rw [count] at h
    exact h
  obtain ⟨b, ab, rb, eb⟩ := (mov_r32_imm32_effect_step 0x114c28 0xb8 (by decide) 256).advances
    ra (programText_slice (ga.codeIn (by simp [Component.Covers]) code) 0x14c28 _
      (by decide) (by decide +kernel)) ea.rip (next 0x14c2d (by decide))
  have gb : AgreesExcept [.reg 0, .rip] a b := eb.agrees
  have carryB : (StatusFlags.ofRFLAGS b.RFLAGS).CF = true := by
    rw [gb.rflags (by decide) (by decide), carry]
  have countB : (Operand.reg 1 : Operand 32).read b = 254 :=
    ((ga.trans gb).read (by simp)).trans count
  obtain ⟨c, ac, rc, ec⟩ := (cmov_r32_r32_effect_step 0x114c2d 0x42 0xc1 (.inl rfl) rfl).advances
    rb (programText_slice ((ga.trans gb).codeIn (by simp [Component.Covers]) code) 0x14c2d _
      (by decide) (by decide +kernel)) eb.rip (next 0x14c30 (by decide))
  have gc : AgreesExcept [.reg 0, .rip] b c := ec.agrees
  have valueC : (Operand.reg 0 : Operand 32).read c = 254 := by
    have h : (Operand.reg 0 : Operand 64).read c =
        (if (StatusFlags.ofRFLAGS b.RFLAGS).CF then (Operand.reg 1 : Operand 32).read b
          else (Operand.reg 0 : Operand 32).read b).setWidth 64 := ec.writes
    rw [carryB, countB] at h
    exact congrArg (BitVec.setWidth 32) h
  obtain ⟨t, runT, rt, et⟩ := (mov_r32_r32_rex_effect_step 0x114c30 0x41 0xc6
      (by simp [RexNoWPrefix]) rfl).advances
    rc (programText_slice (((ga.trans gb).trans gc).codeIn (by simp [Component.Covers]) code)
      0x14c30 _ (by decide) (by decide +kernel)) ec.rip (next 0x14c33 (by decide))
  have gt : AgreesExcept [.reg 14, .rip] c t := et.agrees
  refine ⟨t, ((aa.trans ab).trans ac).trans runT, rt, et.rip, ?_, ?_⟩
  · have h : t.regValue .r14 = ((Operand.reg 0 : Operand 32).read c).setWidth 64 := et.writes
    rwa [valueC] at h
  · apply (((ga.trans gb).trans gc).trans gt).mono
    intro component member
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
    grind only

end P256.Proofs.Sec1.SquareRoot.ExponentInitialize
