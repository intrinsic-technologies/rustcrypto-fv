import P256.Proofs.Nonce.Update.Finish.Hash

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem HmacCallResult.stack_byte [Bindings] {initial s t : RamState}
    {boundary : ReturnBoundary} {entry ret : BitVec 64} {state : State}
    {reserve depth stateOffset outputOffset offset len : Nat} {key : ByteArray} {input : ByteArray}
    (pre : DrbgCalleePre initial boundary entry reserve state)
    (result : HmacCallResult initial s t boundary reserve depth stateOffset outputOffset ret key input)
    (capacity : depth + 680 ≤ reserve) (stateBound : stateOffset ≤ reserve) (outputBound : outputOffset ≤ reserve)
    (bound : offset ≤ depth) (span : len ≤ offset + 8)
    (stateApart : stateOffset + len ≤ offset ∨ offset + 168 ≤ stateOffset)
    (apart : outputOffset + len ≤ offset ∨ offset + 32 ≤ outputOffset)
    {i : Nat} (hi : i < len) :
    t.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      s.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  have bounds := stack_bounds pre.stack
  have sub := stack_sub_toNat pre.stack (show offset ≤ reserve by omega)
  have stateSub := stack_sub_toNat pre.stack stateBound
  have outputSub := stack_sub_toNat pre.stack outputBound
  have address : (stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat =
      (stackPtr initial).toNat - offset + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 2^64),
      Nat.mod_eq_of_lt (by rw [sub]; omega), sub]
  apply result.writes
  intro region member inside
  have cases : region = MemoryRegion.mk (stackPtr initial - BitVec.ofNat 64 stateOffset).toNat 168 ∨
      region = MemoryRegion.mk (stackPtr initial - BitVec.ofNat 64 outputOffset).toNat 32 ∨
      region = MemoryRegion.mk ((stackPtr initial).toNat - (depth+680)) 680 := by
    simpa using member
  rcases cases with rfl | rfl | rfl
  · change (stackPtr initial - BitVec.ofNat 64 stateOffset).toNat ≤ _ ∧
      _ < (stackPtr initial - BitVec.ofNat 64 stateOffset).toNat + 168 at inside
    rw [stateSub, address] at inside
    omega
  · change (stackPtr initial - BitVec.ofNat 64 outputOffset).toNat ≤ _ ∧
      _ < (stackPtr initial - BitVec.ofNat 64 outputOffset).toNat + 32 at inside
    rw [outputSub, address] at inside
    omega
  · change (stackPtr initial).toNat - (depth+680) ≤ _ ∧
      _ < (stackPtr initial).toNat - (depth+680) + 680 at inside
    rw [address] at inside
    omega

end P256.Proofs.Nonce.Update.Finish
