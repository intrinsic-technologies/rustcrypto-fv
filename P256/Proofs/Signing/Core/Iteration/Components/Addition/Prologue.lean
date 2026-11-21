import P256.Proofs.Signing.Core.Iteration.Components.Addition.Entry
import X86Proofs.Instructions.Sub.Generated.Imm8.Triple
import P256.Proofs.Program.SaveRegisters

set_option autoImplicit false

open P256.Proofs.Program (CalleePre boundary_ne_program inProgram_of_textOffset
  programLoaded_codeIn programText_slice)
open P256.Proofs.Program

namespace P256.Proofs.Signing.Core.Iteration.Components.Addition

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem save_registers [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x113310 32 32 64) :
    ∃ t, Advances boundary 8 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = 0x11392a ∧ stackPtr t = stackPtr s - 48 ∧
      t.external = saveMemory s ∧ AgreesExcept (saveFrame s ++ [.reg 1]) s t ∧
      t.regValue .rcx = 0x2025e0 := by
  obtain ⟨v, runV, readyV, loadedV, ripV, frameV, rcxV⟩ := enter pre
  have values : ∀ r ∈ ([5,15,14,13,12,3] : List (BitVec 4)),
      (Operand.reg (r.setWidth 5) : Operand 64).read v =
        (Operand.reg (r.setWidth 5) : Operand 64).read s := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals exact frameV.read (by decide)
  obtain ⟨t,run,ready,loaded,rip,rsp,memory,frame⟩ := push_sequence
    (s := s) (offset := 0) (codeOffset := 0x13920) [5,15,14,13,12,3]
    pre.stack (pre.avoids _ (by simp)) pre.outerBoundary readyV loadedV frameV.grow
    (by have h : stackPtr v = stackPtr s := frameV.read (n := 64) (r := 4) (by decide)
        rw [h]
        bv_omega) ripV (by decide) (by decide)
    (by decide) values (by simp only [PushSequenceCode]; decide +kernel)
  refine ⟨t,runV.trans run,ready,loaded,rip,rsp,?_,?_,?_⟩
  · rw [memory,frameV.external (by simp [Component.Covers])]
    rfl
  · apply (frameV.trans frame).mono
    simp [pushSequenceFrame,saveFrame]
  · exact (frame.read (n := 64) (r := 1) (by simp [pushSequenceFrame])).trans rcxV

theorem prologue [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x113310 32 32 64) :
    ∃ t, Advances boundary 9 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = 0x11392e ∧ stackPtr t = stackPtr s - 64 ∧
      t.external = saveMemory s ∧ AgreesExcept (saveFrame s ++ [.reg 1, .flags]) s t ∧
      t.regValue .rcx = 0x2025e0 := by
  obtain ⟨u, run, ready, loaded, rip, rsp, memory, agrees, rcx⟩ := save_registers pre
  obtain ⟨t, step, final, effect⟩ :=
    (sub_r64_imm8_effect_step 0x11392a 0x48 0xec 16
      (by simp [RexWPrefix]) rfl rfl).advances ready
      (programText_slice (programLoaded_codeIn loaded) 0x1392a _
        (by decide +kernel) (by decide +kernel)) rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1392e (by decide)))
  change (subR64Imm8Effect 0x11392a 4 16 u).Holds u t at effect
  have ext : t.external = u.external := effect.agrees.external
    (by simp [subR64Imm8Effect_components, Component.Covers])
  refine ⟨t, run.trans step, final, ?_, effect.rip, ?_, ext.trans memory, ?_, ?_⟩
  · intro a b h
    rw [ext]
    exact loaded a b h
  · have value : stackPtr t = stackPtr u - 16 := effect.writes
    rw [value, rsp, BitVec.sub_sub]
    rfl
  · apply (agrees.trans effect.agrees).mono
    simp only [saveFrame, subR64Imm8Effect_components, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false]
    intro c hc
    rcases hc with h | (rfl | rfl | rfl)
    · rcases h with h | rfl
      · exact Or.inl h
      · simp
    · simp
    · simp
    · simp
  · exact (effect.agrees.read (n := 64) (r := 1) (by simp)).trans rcx

end P256.Proofs.Signing.Core.Iteration.Components.Addition
