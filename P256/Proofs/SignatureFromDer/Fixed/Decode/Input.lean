import P256.Proofs.SignatureFromDer.Fixed.Decode.CopyFrame

set_option autoImplicit false

open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)
open P256.Proofs.Program (CalleePre memoryRegion_memReadable memoryRegion_contains_add)

namespace P256.Proofs.SignatureFromDer.Fixed.Decode

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem input_readable [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x109ac0 64 72 560) (state : Frame s t)
    {offset : Nat} (bound : offset + 32 ≤ 64) :
    MemReadable t (s.regValue .rsi + BitVec.ofNat 64 offset) 32 := by
  apply P256.Proofs.Common.Memory.memReadable_sub (len := 64) _ offset 32 bound
  apply memoryRegion_memReadable pre.inputBounded _ (Nat.le_refl _) (Nat.le_refl _)
  intro a ha
  exact Option.isSome_iff_exists.mp
    (state.allocated a (Option.isSome_iff_exists.mpr (pre.inputAllocated a ha)))

theorem input_stack_apart [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x109ac0 64 72 560) (state : Frame s t)
    {offset : Nat} (bound : offset + 32 ≤ 64) :
    RangeApart (stackPtr t + 72) 32 (s.regValue .rsi + BitVec.ofNat 64 offset) 32 := by
  intro i hi j hj he
  apply pre.separation (0 : Fin 3) (2 : Fin 3) (by decide)
    (stackPtr t + 72 + BitVec.ofNat 64 i).toNat
  · rw [he, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact memoryRegion_contains_add pre.inputBounded (Nat.le_refl _) (Nat.le_refl _)
      (show offset + j < 64 by omega)
  · change (Stack.region s 560).Contains (stackPtr t + 72#64 + BitVec.ofNat 64 i).toNat
    rw [Program.ScalarFrame.scalar_stack_address (frameOffset := 184) state.rsp (by decide) (offset := 72) (by decide)]
    exact Program.ScalarFrame.stack_contains pre (offset := 112)
      (by decide) (by decide) ⟨i, hi, rfl⟩

theorem copied_extract {s t : RamState} {address destination : BitVec 64} {input : ByteArray}
    {offset : Nat} (bound : offset + 32 ≤ 64)
    (bytes : (MemoryRegion.mk address.toNat 64).HasBytes s.external input)
    (copied : ∀ i < 32, t.external[destination + BitVec.ofNat 64 i]? =
      s.external[address + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?) :
    (MemoryRegion.mk destination.toNat 32).HasBytes t.external (input.extract offset (offset + 32)) := by
  have size : input.size = 64 := bytes.1
  have extractSize : (input.extract offset (offset + 32)).size = 32 := by
    simp only [ByteArray.size_extract, size, Nat.min_eq_left bound, Nat.add_sub_cancel_left]
  refine ⟨extractSize, ?_⟩
  intro i
  have hi : i.val < 32 := by have := i.isLt; omega
  change t.external[BitVec.ofNat 64 (destination.toNat + i.val)]? = _
  rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, copied i.val hi,
    BitVec.add_assoc, ← BitVec.ofNat_add]
  have value := bytes.2 ⟨offset + i.val, by omega⟩
  change s.external[BitVec.ofNat 64 (address.toNat + (offset + i.val))]? = _ at value
  rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at value
  simpa only [ByteArray.getElem_extract] using value

end P256.Proofs.SignatureFromDer.Fixed.Decode
