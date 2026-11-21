import P256.Proofs.Signing.Wrapper.Hash.Finalize.Pad.Fill.Pre

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Hash.Finalize.Pad.Fill

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem result_frame [Bindings] {initial start s t : RamState} {secret message : ByteArray}
    (pre : HashEntry initial start secret message)
    (rsp : stackPtr s = stackPtr initial - 528#64)
    (destination : s.regValue .rdi = stackPtr initial - 456#64 + BitVec.ofNat 64 (message.size % 64 + 1))
    (result : CalleeResult s t (returnBoundary initial) (63 - message.size % 64) 0) :
    MemoryWriteFrame s t #v[workRegion initial] := by
  have bounds := stack_bounds (stack pre.context)
  have rem : message.size % 64 < 64 := Nat.mod_lt _ (by decide)
  have sp : (stackPtr s).toNat = (stackPtr initial).toNat - 528 := by
    rw [rsp]
    exact stack_sub_toNat (stack pre.context) (by decide)
  have dst : (s.regValue .rdi).toNat = (stackPtr initial).toNat - 456 + (message.size % 64 + 1) := by
    rw [destination, toNat_add_ofNat _ _ (by rw [stack_sub_toNat (stack pre.context) (by decide : 456 ≤ 5112)]; omega),
      stack_sub_toNat (stack pre.context) (by decide : 456 ≤ 5112)]
  intro a ha
  apply result.frame a
  intro region member hin
  have cases : region = registerRegion s .rdi (63 - message.size % 64) ∨ region = Stack.region s 0 := by
    simpa using member
  apply ha (workRegion initial) (by simp)
  change (stackPtr initial).toNat - 5112 ≤ a.toNat ∧
    a.toNat < (stackPtr initial).toNat - 5112 + (5112 - 240)
  rcases cases with rfl | rfl
  · change (s.regValue .rdi).toNat ≤ a.toNat ∧ a.toNat < (s.regValue .rdi).toNat + (63 - message.size % 64) at hin
    rw [dst] at hin
    constructor <;> omega
  · change (stackPtr s).toNat - 0 ≤ a.toNat ∧
      a.toNat < (Stack.region s 0).start + (Stack.region s 0).size at hin
    rw [stack_region_end, sp] at hin
    constructor <;> omega

theorem result_byte [Bindings] {initial start s t : RamState} {secret message : ByteArray}
    (pre : HashEntry initial start secret message)
    (rsp : stackPtr s = stackPtr initial - 528#64)
    (destination : s.regValue .rdi = stackPtr initial - 456#64 + BitVec.ofNat 64 (message.size % 64 + 1))
    (result : CalleeResult s t (returnBoundary initial) (63 - message.size % 64) 0)
    {i : Nat} (bound : i < 288) (outside : i ≤ message.size % 64 ∨ 64 ≤ i) :
    t.external[stackPtr initial - 456#64 + BitVec.ofNat 64 i]? =
      s.external[stackPtr initial - 456#64 + BitVec.ofNat 64 i]? := by
  have bounds := stack_bounds (stack pre.context)
  have rem : message.size % 64 < 64 := Nat.mod_lt _ (by decide)
  have address (j : Nat) (hj : j ≤ 288) :
      (stackPtr initial - 456#64 + BitVec.ofNat 64 j).toNat = (stackPtr initial).toNat - 456 + j := by
    rw [toNat_add_ofNat _ _ (by rw [stack_sub_toNat (stack pre.context) (by decide : 456 ≤ 5112)]; omega),
      stack_sub_toNat (stack pre.context) (by decide : 456 ≤ 5112)]
  apply result.frame
  intro region member hin
  have cases : region = registerRegion s .rdi (63 - message.size % 64) ∨ region = Stack.region s 0 := by
    simpa using member
  rcases cases with rfl | rfl
  · change (s.regValue .rdi).toNat ≤ _ ∧
      (stackPtr initial - 456#64 + BitVec.ofNat 64 i).toNat <
        (s.regValue .rdi).toNat + (63 - message.size % 64) at hin
    rw [destination, address _ (by omega), address _ (by omega)] at hin
    omega
  · change (stackPtr s).toNat - 0 ≤ _ ∧
      (stackPtr initial - 456#64 + BitVec.ofNat 64 i).toNat <
        (Stack.region s 0).start + (Stack.region s 0).size at hin
    have sp : (stackPtr s).toNat = (stackPtr initial).toNat - 528 := by
      rw [rsp]
      exact stack_sub_toNat (stack pre.context) (by decide)
    rw [stack_region_end, sp, address _ (by omega)] at hin
    omega

end P256.Proofs.Signing.Wrapper.Hash.Finalize.Pad.Fill
