import Sha2.Proofs.Common.SHA512.Entry.Save
import Sha2.Proofs.Common.SHA512.Words
import Sha2.Proofs.Common.SHA512.Frame

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.Encoding.Serialize (saveFrame saveMemory savedRegisters)

theorem saveFrame_within_stack [Bindings] {initial : RamState} {boundary : ReturnBoundary}
    {hash : Array UInt64} {input : ByteArray} {count : Nat}
    (pre : CompressionPre initial boundary hash input count) {c : Component}
    (hc : c ∈ saveFrame initial ++ [.flags]) {a : BitVec 64} (ha : c.Covers a) :
    (Stack.region initial 416).Contains a.toNat := by
  simp only [saveFrame, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
  all_goals try exact ha.elim
  all_goals exact stackRegion_contains_sub pre.stack.2.2.1 (by decide) (by decide) ha

theorem entry_saved_frame [Bindings] {initial current : RamState} {boundary : ReturnBoundary}
    {hash : Array UInt64} {input : ByteArray} {count : Nat}
    (pre : CompressionPre initial boundary hash input count)
    (ready : ReadyToStep current) (loaded : ProgramLoaded current)
    (rsp : stackPtr current = stackPtr initial - 416)
    (memory : current.external = saveMemory initial)
    (agrees : AgreesExcept (saveFrame initial ++ [.flags]) initial current) :
    FrameState initial current := by
  refine ⟨supportedMachine_of_ready_agrees pre.machine ready agrees, loaded,
    agrees.directionFlagClear (by simp [saveFrame]) pre.directionFlag, agrees.grow, ?_, rsp, ?_, ?_,
    agrees.mxcsr (by simp [saveFrame]), agrees.fcw (by simp [saveFrame])⟩
  · apply agrees.memoryWriteFrame
    intro c hc a ha
    exact ⟨Stack.region initial 416, by simp, saveFrame_within_stack pre hc ha⟩
  · intro entry he
    change memLoad current.external _ 64 = _
    rw [memory]
    exact Sha2.Proofs.Common.Encoding.Serialize.saveMemory_saved initial entry he
  · apply Sha2.Proofs.Common.Encoding.Serialize.read_mem_of_agrees agrees
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
    {hash : Array UInt64} {input : ByteArray} {count i : Nat}
    (pre : CompressionPre initial boundary hash input count)
    (agrees : AgreesExcept (saveFrame initial ++ [.flags]) initial current) (hi : i < 8) :
    memLoad current.external (initial.regValue .rdi + BitVec.ofNat 64 (8 * i)) 64 =
      hash[i]!.toBitVec := by
  have he : (Operand.mem (initial.regValue .rdi + BitVec.ofNat 64 (8 * i)) : Operand 64).read current =
      (Operand.mem (initial.regValue .rdi + BitVec.ofNat 64 (8 * i)) : Operand 64).read initial := by
    apply Sha2.Proofs.Common.Encoding.Serialize.read_mem_of_agrees agrees
    intro j hj c hc ha
    have hs := saveFrame_within_stack pre hc ha
    apply pre.separation (1 : Fin 3) (2 : Fin 3) (by decide) _ ?_ hs
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _)
      (by change 8 * i + j < 64; omega)
  exact he.trans (pre.hashWord hi)

end Sha2.Proofs.Common.SHA512
