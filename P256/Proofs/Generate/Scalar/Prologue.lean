import P256.Proofs.Generate.Scalar.State
import P256.Proofs.Program.PushSequence
import X86Proofs.Instructions.Sub.Generated.Imm8.Triple

set_option autoImplicit false

namespace P256.Proofs.Generate.Scalar

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program

abbrev saveSources : List (BitVec 4) := [15, 14, 13, 12, 3]

abbrev entryMemory (s : RamState) := pushSequenceMemory s s.external 0 saveSources

abbrev entryComponents (s : RamState) :=
  pushSequenceFrame s 0 saveSources ++ [.reg 4, .flags, .rip]

theorem prologue_steps [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) :
    ∃ t, Advances boundary 6 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = 0x112edd ∧ stackPtr t = stackPtr s - 56 ∧
      t.external = entryMemory s ∧ AgreesExcept (entryComponents s) s t := by
  obtain ⟨u, run, ready, loaded, rip, rsp, memory, agrees⟩ :=
    push_sequence (s := s) (t := s) (offset := 0) (codeOffset := 0x12ed0) saveSources
      pre.stack (pre.avoids _ (by simp)) pre.outerBoundary
      (readyToStep pre.machine pre.bindingsSupported) pre.loaded (fun _ h => h)
      (by simp) pre.rip (by decide) (by decide) (by decide) (fun _ _ => rfl)
      (by simp only [PushSequenceCode]; decide +kernel)
  obtain ⟨t, step, readyT, effect⟩ :=
    sub_r64_imm8_effect_step 0x112ed9 0x48 0xec 16
      (by simp [RexWPrefix]) rfl rfl u ready
      (programText_slice (programLoaded_codeIn loaded) 0x12ed9
        [0x48,0x83,0xec,0x10] (by decide) (by decide +kernel)) rip
  have memoryT := effect.agrees.external (by simp [Component.Covers])
  refine ⟨t, run.trans (Advances.of_step step (.inl ?_)), readyT, ?_, effect.rip,
    ?_, memoryT.trans memory, agrees.trans effect.agrees⟩
  · rw [effect.rip]
    exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x12edd (by decide))
  · intro a b hb
    rw [memoryT]
    exact loaded a b hb
  · have hsp : stackPtr t = stackPtr u - 16 := effect.writes
    rw [hsp, rsp, BitVec.sub_sub]
    rfl

theorem entryMemory_saved (s : RamState) (entry : Syntax.Reg × Nat)
    (member : entry ∈ savedRegisters) :
    memLoad (entryMemory s) (stackPtr s - BitVec.ofNat 64 entry.2) 64 = s.regValue entry.1 := by
  simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [entryMemory, pushSequenceMemory, BitVec.sub_eq_add_neg]
    repeat first
      | rw [memLoad_memStore_apart _ _ _ _ _ 64
          (by unfold OffsetsApart; decide +kernel) (by decide) (by decide)]
      | exact memLoad_memStore _ _ (by decide) (by decide) _

theorem entryMemory_return (s : RamState) :
    memLoad (entryMemory s) (stackPtr s) 64 = (returnBoundary s).rip := by
  change memLoad (entryMemory s) (stackPtr s) 64 = memLoad s.external (stackPtr s) 64
  simp only [entryMemory, pushSequenceMemory, BitVec.sub_eq_add_neg]
  repeat rw [memLoad_memStore_apart_right _ (stackPtr s) _ _ 64
    (by unfold OffsetsApart; decide +kernel) (by decide) (by decide)]

theorem prologue_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) :
    ∃ t, Advances boundary 6 s t ∧ State s t ∧ t.RIP = 0x112edd ∧
      stackPtr t = stackPtr s - 56 ∧ AgreesExcept (entryComponents s) s t := by
  obtain ⟨t, run, ready, loaded, rip, rsp, memory, agrees⟩ := prologue_steps pre
  refine ⟨t, run, ?_, rip, rsp, agrees⟩
  refine ⟨bindingsSupported_of_ready_agrees pre.bindingsSupported ready agrees,
    supportedMachine_of_ready_agrees pre.machine ready agrees, loaded,
    agrees.directionFlagClear (by simp [entryComponents, pushSequenceFrame]) pre.directionFlag,
    agrees.grow, ?_, agrees.read (n := 64) (r := 5) (by simp [entryComponents, pushSequenceFrame]),
    ?_, ?_, agrees.mxcsr (by simp [entryComponents, pushSequenceFrame]),
    agrees.fcw (by simp [entryComponents, pushSequenceFrame])⟩
  · apply agrees.memoryWriteFrame
    intro c hc a ha
    simp only [entryComponents, pushSequenceFrame, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with ((rfl | rfl | rfl) | (rfl | rfl | rfl) | (rfl | rfl | rfl) |
      (rfl | rfl | rfl) | (rfl | rfl | rfl)) | rfl | rfl | rfl
    all_goals try exact ha.elim
    all_goals exact ⟨Stack.region s 72, by simp, ScalarFrame.stack_contains pre (by decide) (by decide) ha⟩
  · intro entry member
    rw [memory]
    exact entryMemory_saved s entry member
  · rw [memory]
    exact entryMemory_return s

end P256.Proofs.Generate.Scalar
