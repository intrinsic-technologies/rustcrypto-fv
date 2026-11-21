import P256.Proofs.Verifying.Combination.Naf.Machine.Frame
import P256.Proofs.Verifying.Combination.Naf.Machine.Support
import P256.Proofs.Verifying.Combination.Naf.Machine.Support
import X86Proofs.Instructions.Sub.Generated.Imm8.Triple

set_option autoImplicit false

open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice)

namespace P256.Proofs.Verifying.Combination.Naf.Machine

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def prologueComponents (s : RamState) : List Component :=
  P256.Proofs.Program.saveFrame s ++ [.flags]

theorem prologue_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) :
    ∃ t, Advances boundary 7 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = 0x10f35e ∧ stackPtr t = stackPtr s - 136 ∧
      t.external = P256.Proofs.Program.saveMemory s ∧ AgreesExcept (prologueComponents s) s t := by
  have code : P256.Proofs.Program.SaveCode 0xf350 := by constructor <;> decide +kernel
  obtain ⟨u, run, ready, loaded, rip, rsp, memory, frame⟩ :=
    P256.Proofs.Program.save_registers (codeOffset := 0xf350) pre.stack (pre.avoids _ (by simp)) pre.outerBoundary
      (P256.Proofs.Program.readyToStep pre.machine pre.bindingsSupported) pre.loaded
      (by decide) pre.rip code
  obtain ⟨t, step, ready', effect⟩ :=
    (sub_r64_imm8_effect_step 0x10f35a 0x48 0xec 88
      (by constructor <;> decide) (by decide) (by decide)).advances ready
      (programText_slice (programLoaded_codeIn loaded) 0xf35a
        [0x48, 0x83, 0xec, 0x58] (by decide) (by decide +kernel)) rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf35e (by decide)))
  change (subR64Imm8Effect 0x10f35a 4 88 u).Holds u t at effect
  have external : t.external = u.external :=
    effect.agrees.external (by simp [Component.Covers])
  refine ⟨t, run.trans step, ready', ?_, effect.rip, ?_, external.trans memory, ?_⟩
  · intro a b hb
    rw [external]
    exact loaded a b hb
  · have subtract : stackPtr t = stackPtr u - 88 := effect.writes
    rw [subtract, rsp, BitVec.sub_sub]
    rfl
  · apply (frame.trans effect.agrees).mono
    simp only [P256.Proofs.Program.saveFrame, subR64Imm8Effect_components,
      prologueComponents, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    intro c hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
      (rfl | rfl | rfl) <;> simp

open P256.Proofs.Program
open P256.Proofs.Program

theorem prologue_frame [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) :
    ∃ t, Advances boundary 7 s t ∧ FrameState s t ∧ t.RIP = 0x10f35e ∧
      AgreesExcept (prologueComponents s) s t := by
  obtain ⟨t, run, ready, loaded, rip, rsp, memory, agrees⟩ := prologue_correct pre
  have writes : WritesWithin (prologueComponents s)
      #v[registerRegion s .rdi 257, Stack.region s 168] := by
    intro c hc a covered
    simp only [prologueComponents, saveFrame, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    all_goals try exact covered.elim
    all_goals exact ⟨_, by simp,
      ScalarFrame.stack_contains pre.toCalleePre (by decide) (by decide) covered⟩
  refine ⟨t, run, ⟨bindingsSupported_of_ready_agrees pre.bindingsSupported ready agrees,
    supportedMachine_of_ready_agrees pre.machine ready agrees,
    loaded, agrees.directionFlagClear (by component_not_mem) pre.directionFlag, agrees.grow,
    agrees.memoryWriteFrame writes, rsp, ?_, ?_,
    agrees.mxcsr (by component_not_mem), agrees.fcw (by component_not_mem)⟩,
    rip, agrees⟩
  · intro entry member
    change memLoad t.external _ 64 = _
    rw [memory]
    exact saveMemory_saved s entry member
  · change memLoad t.external _ 64 = _
    rw [memory]
    exact saveMemory_return s

end P256.Proofs.Verifying.Combination.Naf.Machine
