import P256.Proofs.Nonce.Initialize.Reduce.Blocks.Interface
import P256.Proofs.Nonce.Initialize.Seed.Initialized

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Seed

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Nonce.Initialize.Reduce.Blocks

theorem initialize_stage [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} (pre : Nonce.InitializePre initial boundary orderAddress)
    (stage : Stage initial s boundary) (rip : s.RIP = 0x107b85) :
    ∃ t, Stage initial t boundary ∧ (initializeEffect s).Holds s t ∧
      DrbgAt t (stackPtr s + 8) ⟨⟨Array.replicate 32 0⟩, ⟨Array.replicate 32 1⟩⟩ := by
  have blockPre : InitializePre s := by
    refine ⟨rip, ?_, ?_⟩
    · intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact Prepare.stack_writable8 pre stage (offset := 8) (by decide) (by decide)
      · exact Prepare.stack_writable8 pre stage (offset := 16) (by decide) (by decide)
      · exact Prepare.stack_writable8 pre stage (offset := 24) (by decide) (by decide)
      · exact Prepare.stack_writable8 pre stage (offset := 32) (by decide) (by decide)
      · exact Prepare.stack_writable8 pre stage (offset := 40) (by decide) (by decide)
      · exact Prepare.stack_writable8 pre stage (offset := 48) (by decide) (by decide)
      · exact Prepare.stack_writable8 pre stage (offset := 56) (by decide) (by decide)
      · exact Prepare.stack_writable8 pre stage (offset := 64) (by decide) (by decide)
    · intro i hi codeOffset codeLen bound
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact (block_pre pre stage rip).apart 8 8 (by decide) codeOffset codeLen bound
      · exact (block_pre pre stage rip).apart 16 8 (by decide) codeOffset codeLen bound
      · exact (block_pre pre stage rip).apart 24 8 (by decide) codeOffset codeLen bound
      · exact (block_pre pre stage rip).apart 32 8 (by decide) codeOffset codeLen bound
      · exact (block_pre pre stage rip).apart 40 8 (by decide) codeOffset codeLen bound
      · exact (block_pre pre stage rip).apart 48 8 (by decide) codeOffset codeLen bound
      · exact (block_pre pre stage rip).apart 56 8 (by decide) codeOffset codeLen bound
      · exact (block_pre pre stage rip).apart 64 8 (by decide) codeOffset codeLen bound
  obtain ⟨fuel, t, run, ready, _, effect⟩ := initialize_run boundary pre.outerBoundary s
    (readyToStep stage.machine stage.bindingsSupported)
    (programText_slice (programLoaded_codeIn stage.loaded) 0x7b85 initializeBytes
      (by decide +kernel) (by decide +kernel)) blockPre
  have readsp : (Operand.reg 4 : Operand 64).read s = stackPtr s := Operand.read_reg64 s 4
  have stage' : Stage initial t boundary := Reduce.Blocks.Stage.of_local pre stage run ready effect.agrees (by
    intro c hc a ha
    simp only [initializeEffect, Effect.components, List.map_cons, List.map_nil, List.nil_append,
      List.append_nil, List.cons_append, Write.component_mem, Write.component_reg,
      List.mem_cons, List.not_mem_nil, or_false, readsp] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ha.elim
    · exact local_covers (offset := 8) (by decide) ha
    · exact local_covers (offset := 16) (by decide) ha
    · exact local_covers (offset := 24) (by decide) ha
    · exact local_covers (offset := 32) (by decide) ha
    · exact local_covers (offset := 40) (by decide) ha
    · exact local_covers (offset := 48) (by decide) ha
    · exact local_covers (offset := 56) (by decide) ha
    · exact local_covers (offset := 64) (by decide) ha
    · exact ha.elim) (by simp [initializeEffect, Effect.components]) (by simp [initializeEffect, Effect.components])
    (by simp [initializeEffect, Effect.components]) (by simp [initializeEffect, Effect.components])
  refine ⟨t, stage', effect, initialized_bytes effect ?_⟩
  intro i hi
  apply effect.agrees.grow
  have readable := ScalarFrame.stack_readable pre.toCalleePre stage.toFrameState (offset := 0) (len := 72) (by decide) (by decide)
  simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using readable.mem i hi

end P256.Proofs.Nonce.Initialize.Seed
