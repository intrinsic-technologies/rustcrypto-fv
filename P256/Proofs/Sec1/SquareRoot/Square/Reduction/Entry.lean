import P256.Proofs.Sec1.SquareRoot.Square.Interface
import P256.Proofs.Program.ScalarFrame.Prologue
import X86Proofs.Instructions.Sub.Generated.Imm8.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Square.Reduction

open P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Entry [Bindings] (s t : RamState) (boundary : ReturnBoundary) : Prop where
  execution : Advances boundary 7 s t
  state : ScalarFrame.FrameState s t 32 112 112
  rip : t.RIP = 0x1133fe
  memory : t.external = saveMemory s
  agrees : AgreesExcept (saveFrame s ++ [.flags]) s t

theorem entry_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : ReductionPre s boundary) : ∃ t, Entry s t boundary := by
  have code : SaveCode 0x133f0 := by constructor <;> decide +kernel
  obtain ⟨u, run, ready, loaded, rip, rsp, memory, frame⟩ :=
    save_registers (codeOffset := 0x133f0) pre.stack (pre.avoids _ (by simp)) pre.outerBoundary
      (readyToStep pre.machine pre.bindingsSupported) pre.loaded (by decide) pre.rip code
  obtain ⟨t, run2, ready2, effect⟩ :=
    (sub_r64_imm8_effect_step 0x1133fa 0x48 0xec 64
      (by simp [RexWPrefix]) rfl rfl).advances ready
      (programText_slice (programLoaded_codeIn loaded) 0x133fa
        [0x48, 0x83, 0xec, 0x40] (by decide) (by decide +kernel)) rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x133fe (by decide)))
  change (subR64Imm8Effect 0x1133fa 4 64 u).Holds u t at effect
  have hm : t.external = u.external := effect.agrees.external (by simp [Component.Covers])
  have hsp : stackPtr t = stackPtr s - 112 := by
    have hw : stackPtr t = stackPtr u - 64 := effect.writes
    rw [hw, rsp, BitVec.sub_sub]
    rfl
  have hf : AgreesExcept (saveFrame s ++ [.flags]) s t := (frame.trans effect.agrees).mono (by
    simp only [subR64Imm8Effect_components]
    intro c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with hc | (rfl | rfl | rfl)
    · exact Or.inl hc
    · simp [saveFrame]
    · simp
    · simp [saveFrame])
  have hl : ProgramLoaded t := by simpa only [ProgramLoaded, hm] using loaded
  exact ⟨t, ⟨run.trans run2, ScalarFrame.prologue_frame pre.toCalleePre (by decide)
    ready2 hl hsp (hm.trans memory) hf, effect.rip, hm.trans memory, hf⟩⟩

end P256.Proofs.Sec1.SquareRoot.Square.Reduction
