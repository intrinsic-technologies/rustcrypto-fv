import P256.Proofs.Sec1.SquareRoot.Interface
import P256.Proofs.Program.PushSequence
import X86Proofs.Instructions.Sub.Generated.Imm32.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def savedSources : List (BitVec 4) := [5, 15, 14, 12, 3]

def entryMemory (s : RamState) : Ram := pushSequenceMemory s s.external 0 savedSources

def entryComponents (s : RamState) : List Component :=
  pushSequenceFrame s 0 savedSources ++ [.reg 4, .flags, .rip]

theorem field_sqrt_entry [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) :
    ∃ t, Advances boundary 6 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = 0x11441f ∧ stackPtr t = stackPtr s - 584 ∧
      t.external = entryMemory s ∧ AgreesExcept (entryComponents s) s t := by
  obtain ⟨u, run, ready, loaded, rip, rsp, memory, agrees⟩ :=
    push_sequence (s := s) (t := s) (offset := 0) (codeOffset := 0x14410) savedSources
      pre.stack (pre.avoids _ (by simp)) pre.outerBoundary
      (readyToStep pre.machine pre.bindingsSupported) pre.loaded (fun _ h => h)
      (by simp only [BitVec.sub_zero]) pre.rip (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by intros; rfl)
      (by simp only [savedSources, PushSequenceCode]; decide +kernel)
  have ripU : u.RIP = 0x114418 := rip
  have rspU : stackPtr u = stackPtr s - 40 := rsp
  obtain ⟨t, step, readyT, effect⟩ :=
    sub_r64_imm32_effect_step 0x114418 0x48 0xec 544
      (by unfold RexWPrefix; decide +kernel) rfl rfl u ready
      (programText_slice (programLoaded_codeIn loaded) 0x14418
        [0x48, 0x81, 0xec, 0x20, 0x02, 0, 0] (by decide +kernel) (by decide +kernel)) ripU
  have ripT : t.RIP = 0x11441f := effect.rip
  have runT : Advances boundary 1 u t := Advances.of_step step (.inl (by
    rw [ripT]
    exact boundary_ne_program pre.outerBoundary
      (inProgram_of_textOffset 0x1441f (by decide +kernel))))
  have memT : t.external = u.external := effect.agrees.external
    (by simp [subR64Imm32Effect_components, Component.Covers])
  refine ⟨t, run.trans runT, readyT, ?_, ripT, ?_, memT.trans memory, ?_⟩
  · simpa only [ProgramLoaded, memT] using loaded
  · have hw : stackPtr t = stackPtr u - 544 := effect.writes
    rw [hw, rspU, BitVec.sub_sub]
    rfl
  · exact agrees.trans effect.agrees

end P256.Proofs.Sec1.SquareRoot
