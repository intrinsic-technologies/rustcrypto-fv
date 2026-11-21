import P256.Proofs.SHA256.Entry.Save
import P256.Proofs.SHA256.Memory.Words
import P256.Proofs.SHA256.Frame

set_option autoImplicit false

namespace P256.Proofs.SHA256

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Program (saveFrame saveMemory savedRegisters)

theorem saveFrame_within_stack [Bindings] {initial : RamState} {boundary : ReturnBoundary}
    {hash : Array UInt32} {input : ByteArray} {count : Nat}
    (pre : CompressionPre initial boundary hash input count) {c : Component}
    (hc : c ∈ saveFrame initial ++ [.flags]) {a : BitVec 64} (ha : c.Covers a) :
    (Stack.region initial 336).Contains a.toNat := by
  simp only [saveFrame, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
  all_goals try exact ha.elim
  all_goals exact ScalarFrame.stack_contains pre.toCalleePre (by decide) (by decide) ha

theorem entry_saved_frame [Bindings] {initial current : RamState} {boundary : ReturnBoundary}
    {hash : Array UInt32} {input : ByteArray} {count : Nat}
    (pre : CompressionPre initial boundary hash input count)
    (ready : ReadyToStep current) (loaded : ProgramLoaded current)
    (rsp : stackPtr current = stackPtr initial - 336)
    (memory : current.external = saveMemory initial)
    (agrees : AgreesExcept (saveFrame initial ++ [.flags]) initial current) :
    ScalarFrame.FrameState initial current 32 336 336 := by
  refine ⟨bindingsSupported_of_ready_agrees pre.bindingsSupported ready agrees,
    supportedMachine_of_ready_agrees pre.machine ready agrees, loaded,
    agrees.directionFlagClear (by component_not_mem) pre.directionFlag, agrees.grow, ?_, rsp, ?_, ?_,
    agrees.mxcsr (by component_not_mem), agrees.fcw (by component_not_mem)⟩
  · apply agrees.memoryWriteFrame
    intro c hc a ha
    exact ⟨Stack.region initial 336, by simp, saveFrame_within_stack pre hc ha⟩
  · intro entry he
    change memLoad current.external _ 64 = _
    rw [memory]
    exact P256.Proofs.Program.saveMemory_saved initial entry he
  · apply P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees agrees
    intro i hi c hc ha
    simp only [saveFrame, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    all_goals try exact ha.elim
    all_goals
      obtain ⟨j, hj, he⟩ := ha
      have he' := he.symm
      simp only [BitVec.sub_eq_add_neg] at he'
    · exact OffsetsApart.ne (c₁ := -8) (len₁ := 8) (len₂ := 8) (c₂ := 0#64)
        (by unfold OffsetsApart; decide +kernel) (stackPtr initial) hj hi (by decide)
        (by simpa only [BitVec.add_zero] using he')
    · exact OffsetsApart.ne (c₁ := -16) (len₁ := 8) (len₂ := 8) (c₂ := 0#64)
        (by unfold OffsetsApart; decide +kernel) (stackPtr initial) hj hi (by decide)
        (by simpa only [BitVec.add_zero] using he')
    · exact OffsetsApart.ne (c₁ := -24) (len₁ := 8) (len₂ := 8) (c₂ := 0#64)
        (by unfold OffsetsApart; decide +kernel) (stackPtr initial) hj hi (by decide)
        (by simpa only [BitVec.add_zero] using he')
    · exact OffsetsApart.ne (c₁ := -32) (len₁ := 8) (len₂ := 8) (c₂ := 0#64)
        (by unfold OffsetsApart; decide +kernel) (stackPtr initial) hj hi (by decide)
        (by simpa only [BitVec.add_zero] using he')
    · exact OffsetsApart.ne (c₁ := -40) (len₁ := 8) (len₂ := 8) (c₂ := 0#64)
        (by unfold OffsetsApart; decide +kernel) (stackPtr initial) hj hi (by decide)
        (by simpa only [BitVec.add_zero] using he')
    · exact OffsetsApart.ne (c₁ := -48) (len₁ := 8) (len₂ := 8) (c₂ := 0#64)
        (by unfold OffsetsApart; decide +kernel) (stackPtr initial) hj hi (by decide)
        (by simpa only [BitVec.add_zero] using he')

theorem entry_saved_hashWord [Bindings] {initial current : RamState} {boundary : ReturnBoundary}
    {hash : Array UInt32} {input : ByteArray} {count i : Nat}
    (pre : CompressionPre initial boundary hash input count)
    (agrees : AgreesExcept (saveFrame initial ++ [.flags]) initial current) (hi : i < 8) :
    memLoad current.external (initial.regValue .rdi + BitVec.ofNat 64 (4 * i)) 32 =
      hash[i]!.toBitVec := by
  have he : (Operand.mem (initial.regValue .rdi + BitVec.ofNat 64 (4 * i)) : Operand 32).read current =
      (Operand.mem (initial.regValue .rdi + BitVec.ofNat 64 (4 * i)) : Operand 32).read initial := by
    apply P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees agrees
    intro j hj c hc ha
    have hs := saveFrame_within_stack pre hc ha
    apply pre.separation (1 : Fin 3) (2 : Fin 3) (by decide) _ ?_ hs
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _)
      (by change 4 * i + j < 32; omega)
  exact he.trans (pre.hashWord hi)

end P256.Proofs.SHA256
