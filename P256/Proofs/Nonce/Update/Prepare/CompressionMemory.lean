import P256.Proofs.Nonce.Update.Prepare.CompressionCall

set_option autoImplicit false

namespace P256.Proofs.Nonce

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

set_option maxRecDepth 2048 in
theorem CompressionCallResult.stack_byte [Bindings] {initial s t : RamState}
    {boundary : ReturnBoundary} {entry ret : BitVec 64} {state : State}
    {reserve depth outputOffset offset len : Nat} {hash : Array UInt32} {input : ByteArray}
    (pre : DrbgCalleePre initial boundary entry reserve state)
    (result : CompressionCallResult initial s t boundary reserve depth outputOffset ret hash input)
    (capacity : depth + 344 ≤ reserve) (outputBound : outputOffset ≤ reserve)
    (bound : offset ≤ depth) (span : len ≤ offset + 8)
    (apart : outputOffset + len ≤ offset ∨ offset + 32 ≤ outputOffset)
    {i : Nat} (hi : i < len) :
    t.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      s.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  have bounds := stack_bounds pre.stack
  have sub := stack_sub_toNat pre.stack (show offset ≤ reserve by omega)
  have outputSub := stack_sub_toNat pre.stack outputBound
  have address : (stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat =
      (stackPtr initial).toNat - offset + i := by
    rw [toNat_add_ofNat _ _ (by rw [sub]; omega), sub]
  apply result.writes
  intro region member inside
  have cases : region = MemoryRegion.mk (stackPtr initial - BitVec.ofNat 64 outputOffset).toNat 32 ∨
      region = MemoryRegion.mk ((stackPtr initial).toNat - (depth+344)) 344 := by
    simpa using member
  rcases cases with rfl | rfl
  · change (stackPtr initial - BitVec.ofNat 64 outputOffset).toNat ≤ _ ∧
      _ < (stackPtr initial - BitVec.ofNat 64 outputOffset).toNat + 32 at inside
    rw [outputSub, address] at inside
    omega
  · change (stackPtr initial).toNat - (depth+344) ≤ _ ∧
      _ < (stackPtr initial).toNat - (depth+344) + 344 at inside
    rw [address] at inside
    omega

end P256.Proofs.Nonce
