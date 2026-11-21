import P256.Proofs.ReadBe.Interface
import P256.Proofs.Program.SaveRegisters
import P256.Proofs.ReadBe.State
import X86Proofs.Instructions.Sub.Generated.Imm8.Triple

set_option autoImplicit false

open P256.Proofs.Program

namespace P256.Proofs.ReadBe.Entry

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [bindings : Bindings] {s : RamState} {boundary : ReturnBoundary}

def prologueComponents (s : RamState) : List Component :=
  P256.Proofs.Program.saveFrame s ++ [.flags]

theorem prologue_correct (pre : Pre s boundary) :
    ∃ t, Advances boundary 7 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = 0x11909e ∧ stackPtr t = frameBase s ∧
      t.external = P256.Proofs.Program.saveMemory s ∧ AgreesExcept (prologueComponents s) s t := by
  have code : P256.Proofs.Program.SaveCode 0x19090 := by constructor <;> decide +kernel
  obtain ⟨u, run, ready, loaded, rip, rsp, memory, frame⟩ :=
    P256.Proofs.Program.save_registers (codeOffset := 0x19090) pre.stack (pre.avoids _ (by simp))
      pre.outerBoundary (readyToStep pre.machine pre.bindingsSupported) pre.loaded
      (by decide +kernel) pre.rip code
  obtain ⟨t, step, ready', effect⟩ :=
    (sub_r64_imm8_effect_step 0x11909a 0x48 0xec 24
      (by constructor <;> decide +kernel) (by decide +kernel) (by decide +kernel)).advances ready
      (programText_slice (programLoaded_codeIn loaded) 0x1909a _
        (by decide +kernel) (by decide +kernel)) rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1909e (by decide +kernel)))
  have external : t.external = u.external := effect.agrees.external
    (by simp [subR64Imm8Effect_components, Component.Covers])
  refine ⟨t, run.trans step, ready', ?_, effect.rip, ?_, external.trans memory, ?_⟩
  · intro a b h
    rw [external]
    exact loaded a b h
  · have subtract : stackPtr t = stackPtr u - 24 := effect.writes
    rw [subtract, rsp, BitVec.sub_sub]
    rfl
  · apply (frame.trans effect.agrees).mono
    simp only [subR64Imm8Effect_components, prologueComponents, P256.Proofs.Program.saveFrame,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    intro c hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl) <;>
      simp [gprNumber, rexB, modrmRm]

end P256.Proofs.ReadBe.Entry
