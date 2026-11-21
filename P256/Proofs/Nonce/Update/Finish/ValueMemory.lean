import P256.Proofs.Nonce.Update.Finish.Value

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Finish

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem ValueCallResult.stack_byte [Bindings] {initial s t : RamState}
    {boundary : ReturnBoundary} {entry ret : BitVec 64} {original state : State}
    {reserve depth offset len : Nat}
    (pre : DrbgCalleePre initial boundary entry reserve original)
    (result : ValueCallResult initial s t boundary reserve depth ret state)
    (capacity : depth + 1176 ≤ reserve) (bound : offset ≤ depth) (span : len ≤ offset + 8)
    {i : Nat} (hi : i < len) :
    t.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      s.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  have bounds := stack_bounds pre.stack
  have sub := stack_sub_toNat pre.stack (show offset ≤ reserve by omega)
  have address : (stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat =
      (stackPtr initial).toNat - offset + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 2^64),
      Nat.mod_eq_of_lt (by rw [sub]; omega), sub]
  apply result.writes
  intro region member inside
  have cases : region = registerRegion initial .rdi 64 ∨
      region = MemoryRegion.mk ((stackPtr initial).toNat - (depth+1176)) 1176 := by
    simpa using member
  rcases cases with rfl | rfl
  · exact pre.separation _ inside (ScalarFrame.stack_contains pre.callee (by omega) span ⟨i, hi, rfl⟩)
  · change (stackPtr initial).toNat - (depth+1176) ≤ _ ∧
      _ < (stackPtr initial).toNat - (depth+1176) + 1176 at inside
    rw [address] at inside
    omega

end P256.Proofs.Nonce.Update.Finish
