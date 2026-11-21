import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.Memory
import Base16ct.Proofs.Copied.Md5.Proofs.Block.Preconditions
namespace Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine

open Base16ct.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem stack_push_contains {s : RamState} (h : Stack.Valid s base16ctMixedDecode.minStackBytes) {used i : Nat} (hused : used ≤ base16ctMixedDecode.minStackBytes) (hi : i < 8) :
    (Stack.region s base16ctMixedDecode.minStackBytes).Contains (stackPtr s - BitVec.ofNat 64 used + BitVec.ofNat 64 i).toNat := by
  obtain ⟨hs, he⟩ := Base16ct.Proofs.Copied.Md5.Proofs.Block.stack_subrange_bounds h (used := used) hused
  exact Base16ct.Proofs.Copied.Md5.Proofs.Block.contains_offset_of_subrange h.1 hs he i (by omega)

theorem validCall_stack_push_writable {s : RamState} {input : ByteArray} {capacity : Nat} {lengthWritten : Prop}
    (h : ValidCall base16ctMixedDecode s input capacity (input.size / 2) lengthWritten)
    {used : Nat} (hused : used ≤ base16ctMixedDecode.minStackBytes)
    (_halign : used % 8 = 0) :
    X86Proofs.MemWritable s (stackPtr s - BitVec.ofNat 64 used) 8 := by
  have hav := h.separation.2.1 (Stack.region s base16ctMixedDecode.minStackBytes) (by simp [base16ctMixedDecode])
  have hw : Base16ct.Proofs.Copied.Md5.Proofs.Memory.MemWritable s (stackPtr s - BitVec.ofNat 64 used) (used + 8) :=
    Base16ct.Proofs.Copied.Md5.Proofs.Block.stack_memoryWritable h.stack (used := used) hused
      (fun a hc ht ↦ hav a hc (.inr (pageTables_contains_of_md5 ht)))
  refine X86Proofs.MemWritable.of_not_reserved (by decide +kernel)
    (by have := hw.low; omega) (fun i hi ↦ hw.bytes i (by omega)) ?_
  intro i hi ht
  exact hav _ (stack_push_contains h.stack hused hi) (.inr ht)

theorem validCall_stack_push_avoids {s : RamState} {input : ByteArray} {capacity : Nat} {lengthWritten : Prop}
    (h : ValidCall base16ctMixedDecode s input capacity (input.size / 2) lengthWritten)
    {used : Nat} (hused : used ≤ base16ctMixedDecode.minStackBytes) :
    ∀ i < 8, ¬ InProgram (stackPtr s - BitVec.ofNat 64 used + BitVec.ofNat 64 i) := by
  intro i hi hp
  exact h.separation.2.1 (Stack.region s base16ctMixedDecode.minStackBytes) (by simp [base16ctMixedDecode]) _
    (stack_push_contains h.stack hused hi) (.inl hp)

end Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine
