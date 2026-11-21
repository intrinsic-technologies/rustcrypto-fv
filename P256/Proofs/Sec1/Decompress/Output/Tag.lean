import P256.Proofs.Program.Code
import P256.Proofs.Common.Instructions.ByteLogic.AndReg
import P256.Proofs.Common.Instructions.MovzxByte

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decompress.Output

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs
open P256.Proofs.Program
open P256.Proofs.Common.Instructions.ByteLogic P256.Proofs.Common.Instructions.MovzxByte

theorem tag_arguments [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (outside : ¬ InProgram boundary.rip) (rip : s.RIP = 0x1100aa) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ t.RIP = 0x1100b1 ∧
      t.regValue .rdi = (((s.regValue .r15).setWidth 8) &&&
        ((s.regValue .rbp).setWidth 8)).setWidth 64 ∧
      AgreesExcept [.reg 15, .reg 7, .flags, .rip] s t := by
  obtain ⟨u, run, readyU, effect⟩ :=
    (and_r8_r8_rex_effect_step 0x1100aa 0x41 0xef (by simp [RexPrefix]) rfl).advances ready
      (programText_slice (programLoaded_codeIn loaded) 0x100aa [0x41, 0x20, 0xef]
        (by decide) (by decide +kernel)) rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x100ad (by decide)))
  change (andR8R8Effect 0x1100aa 15 5 s).Holds s u at effect
  have memory := effect.agrees.external (by simp [andR8R8Effect, Effect.components, Component.Covers])
  obtain ⟨t, runT, readyT, effectT⟩ :=
    (movzx_r32_r8_rex_effect_step 0x1100ad 0x41 0xff (by simp [RexNoWPrefix]) rfl).advances readyU
      (programText_slice ((programLoaded_codeIn loaded).of_external_eq memory)
        0x100ad [0x41, 0x0f, 0xb6, 0xff] (by decide) (by decide +kernel)) effect.rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x100b1 (by decide)))
  change (movzxR32R8Effect 0x1100ad 4 7 15 u).Holds u t at effectT
  refine ⟨t, run.trans runT, readyT, effectT.rip, ?_,
    (effect.agrees.trans effectT.agrees).mono (by simp [andR8R8Effect, movzxR32R8Effect, Effect.components])⟩
  have result : t.regValue .rdi = ((u.regValue .r15).setWidth 8).setWidth 64 := effectT.writes
  have value : u.regValue .r15 = mergeGPR 8
      (((s.regValue .r15).setWidth 8) &&& ((s.regValue .rbp).setWidth 8))
      (s.regValue .r15) := effect.writes
  rw [result, value]
  congr 1
  exact setWidth_mergeGPR8 _ _

end P256.Proofs.Sec1.Decompress.Output
