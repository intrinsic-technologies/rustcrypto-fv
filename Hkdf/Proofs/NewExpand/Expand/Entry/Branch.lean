import Hkdf.Proofs.Common.Machine.Code
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Cmp.Generated.AccImm32.Triple
import X86Proofs.Instructions.Branch.Triple

namespace Hkdf.Proofs.NewExpand.Expand

open Hkdf.Spec.Program Hkdf.Proofs.Program Hkdf.Proofs.Common.Machine
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

private theorem length_carry (x : BitVec 64) :
    (x + 0xffffffffffffe01f).toNat < 0xffffffffffffe020 ↔
      x.toNat = 0 ∨ 8160 < x.toNat := by
  rw [BitVec.toNat_add]
  have bound := x.isLt
  change (x.toNat + 18446744073709543455) % 18446744073709551616 <
    18446744073709543456 ↔ _
  omega

theorem length_branch [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (pc : s.RIP = 0x10f281)
    (outside : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 3 s t ∧ ReadyToStep t ∧
      t.RIP = (if (s.regValue .r8).toNat = 0 ∨ 8160 < (s.regValue .r8).toNat
        then 0x10f290 else 0x10f2b1) ∧ AgreesExcept [.reg 0, .flags, .rip] s t := by
  have code := programLoaded_codeIn loaded
  obtain ⟨u, leaRun, readyU, lea⟩ := (lea_r64_effect_step 0x10f281 0x49
    (by simp [RexWPrefix]) 0 (.base 8 (.d32 0xffffe01f)) (by decide) rfl rfl).advances ready
    (programText_slice code 0xf281 [0x49,0x8d,0x80,0x1f,0xe0,0xff,0xff]
      (by decide) (by decide +kernel)) pc
    (boundary_ne_program outside (inProgram_of_textOffset 0xf288 (by decide)))
  have leaFrame : AgreesExcept [.reg 0, .rip] s u := lea.agrees
  have address : u.regValue .rax = s.regValue .r8 + 0xffffffffffffe01f := lea.writes
  have codeU := leaFrame.codeIn (by simp [Component.Covers]) code
  obtain ⟨v, cmpRun, readyV, cmp⟩ := (cmp_rax_imm32_effect_step 0x10f288 0x48
    0xffffe020 (by simp [RexWPrefix])).advances readyU
    (programText_slice codeU 0xf288 [0x48,0x3d,0x20,0xe0,0xff,0xff]
      (by decide) (by decide +kernel)) lea.rip
    (boundary_ne_program outside (inProgram_of_textOffset 0xf28e (by decide)))
  have cmpFrame : AgreesExcept [.flags, .rip] u v := cmp.agrees
  have cf : (StatusFlags.ofRFLAGS v.RFLAGS).CF =
      decide ((u.regValue .rax).toNat < 0xffffffffffffe020) := cmp.flags.1
  obtain ⟨t, step, readyT, branch⟩ := jcc_rel8_effect_step 0x10f28e 3 0x21 v readyV
    (programText_slice (cmpFrame.codeIn (by simp [Component.Covers]) codeU) 0xf28e
      [0x73,0x21] (by decide) (by decide +kernel)) ⟨cmp.rip, fun _ => by decide⟩
  have pcT : t.RIP = _ := branch.rip
  change t.RIP = (if !(StatusFlags.ofRFLAGS v.RFLAGS).CF then 0x10f2b1 else 0x10f290) at pcT
  rw [cf, address] at pcT
  simp only [length_carry, Bool.not_eq_true', decide_eq_false_iff_not, ite_not] at pcT
  have run : Advances boundary 1 v t := Advances.of_step step (.inl (by
    rw [pcT]
    split
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xf290 (by decide))
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xf2b1 (by decide))))
  have branchFrame : AgreesExcept [.rip] v t := branch.agrees
  exact ⟨t, (leaRun.trans cmpRun).trans run, readyT, pcT,
    ((leaFrame.trans cmpFrame).trans branchFrame).mono (by simp)⟩

end Hkdf.Proofs.NewExpand.Expand
