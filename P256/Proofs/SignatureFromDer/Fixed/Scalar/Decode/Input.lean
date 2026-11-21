import P256.Proofs.SignatureFromDer.Fixed.Scalar.Decode.CopyFrame
import P256.Proofs.Program.ScalarFrame.Input
import P256.Proofs.Program.ScalarFrame.Copy32Bytes

set_option autoImplicit false

open P256.Proofs.Program (CalleePre memoryRegion_contains_add memoryRegion_memReadable)

namespace P256.Proofs.SignatureFromDer.Fixed.Scalar

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs


namespace Decode

theorem input_readable [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10fa20 32 40 288) (state : FrameState s t)
    {offset : Nat} (bound : offset + 32 ≤ 32) :
    MemReadable t (s.regValue .rsi + BitVec.ofNat 64 offset) 32 := by
  apply P256.Proofs.Common.Memory.memReadable_sub (len := 32) _ offset 32 bound
  apply memoryRegion_memReadable pre.inputBounded _ (Nat.le_refl _) (Nat.le_refl _)
  intro a ha
  exact Option.isSome_iff_exists.mp
    (state.allocated a (Option.isSome_iff_exists.mpr (pre.inputAllocated a ha)))

theorem input_stack_apart [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10fa20 32 40 288) (state : FrameState s t)
    {offset : Nat} (bound : offset + 32 ≤ 32) :
    RangeApart (stackPtr t + 72) 32 (s.regValue .rsi + BitVec.ofNat 64 offset) 32 := by
  intro i hi j hj he
  apply pre.separation (0 : Fin 3) (2 : Fin 3) (by decide)
    (stackPtr t + 72 + BitVec.ofNat 64 i).toNat
  · rw [he, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact memoryRegion_contains_add pre.inputBounded (Nat.le_refl _) (Nat.le_refl _)
      (show offset + j < 32 by omega)
  · change (Stack.region s 288).Contains (stackPtr t + 72#64 + BitVec.ofNat 64 i).toNat
    rw [Program.ScalarFrame.scalar_stack_address (frameOffset := 152) state.rsp (by decide) (offset := 72) (by decide)]
    exact Program.ScalarFrame.stack_contains pre (offset := 80)
      (by decide) (by decide) ⟨i, hi, rfl⟩

end Decode
end P256.Proofs.SignatureFromDer.Fixed.Scalar
