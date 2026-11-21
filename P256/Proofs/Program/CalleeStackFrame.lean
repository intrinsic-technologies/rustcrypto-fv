import P256.Proofs.Program.ScalarFrame.Work

set_option autoImplicit false

namespace P256.Proofs.Program

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem CalleeResult.stack_frame [Bindings] {initial s t : RamState}
    {boundary : ReturnBoundary} {outerReserve savedBytes outputBytes reserve : Nat}
    {stackOffset outputOffset : Nat} {outputRegister : Syntax.Reg}
    (stack : Stack.Valid initial outerReserve)
    (result : CalleeResult s t boundary outputBytes reserve outputRegister)
    (rsp : stackPtr s = stackPtr initial - BitVec.ofNat 64 stackOffset)
    (output : s.regValue outputRegister = stackPtr initial - BitVec.ofNat 64 outputOffset)
    (capacity : stackOffset + reserve ≤ outerReserve)
    (stackBelow : savedBytes + 8 ≤ stackOffset)
    (outputBound : outputOffset ≤ outerReserve)
    (outputBelow : outputBytes + savedBytes ≤ outputOffset) :
    MemoryWriteFrame s t #v[ScalarFrame.Work.region initial outerReserve savedBytes] := by
  have bounds := stack_bounds stack
  have sp : (stackPtr s).toNat = (stackPtr initial).toNat - stackOffset := by
    rw [rsp]
    exact stack_sub_toNat stack (by omega)
  have dst : (s.regValue outputRegister).toNat = (stackPtr initial).toNat - outputOffset := by
    rw [output]
    exact stack_sub_toNat stack outputBound
  intro a ha
  apply result.frame a
  intro region hr hin
  apply ha (ScalarFrame.Work.region initial outerReserve savedBytes) (by simp)
  have cases : region = registerRegion s outputRegister outputBytes ∨
      region = Stack.region s reserve := by simpa using hr
  change (stackPtr initial).toNat - outerReserve ≤ a.toNat ∧
    a.toNat < (stackPtr initial).toNat - outerReserve + (outerReserve - savedBytes)
  rcases cases with rfl | rfl
  · change (s.regValue outputRegister).toNat ≤ a.toNat ∧
      a.toNat < (s.regValue outputRegister).toNat + outputBytes at hin
    rw [dst] at hin
    constructor <;> omega
  · change (stackPtr s).toNat - reserve ≤ a.toNat ∧
      a.toNat < (Stack.region s reserve).start + (Stack.region s reserve).size at hin
    rw [stack_region_end, sp] at hin
    constructor <;> omega

theorem CalleeResult.stack_byte [Bindings] {s entry t : RamState} {boundary : ReturnBoundary}
    {outerReserve frameOffset outputOffset outputBytes reserve offset len : Nat}
    (stack : Stack.Valid s outerReserve)
    (rsp : stackPtr entry = stackPtr s - BitVec.ofNat 64 (frameOffset + 8))
    (result : CalleeResult entry t boundary outputBytes reserve)
    (destination : entry.regValue .rdi = stackPtr s - BitVec.ofNat 64 outputOffset)
    (hframe : frameOffset + 8 ≤ outerReserve)
    (hout : outputOffset ≤ outerReserve) (ho : offset ≤ frameOffset) (hlen : len ≤ offset + 8)
    (hapart : offset + outputBytes ≤ outputOffset ∨ outputOffset + len ≤ offset)
    {i : Nat} (hi : i < len) :
    t.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      entry.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  have hb := stack_bounds stack
  have hs := stack_sub_toNat stack (offset := offset) (by omega)
  have hsn : (stackPtr entry).toNat = (stackPtr s).toNat - (frameOffset + 8) := by
    rw [rsp]
    exact stack_sub_toNat stack (offset := frameOffset + 8) (by omega)
  have hdn : (entry.regValue .rdi).toNat = (stackPtr s).toNat - outputOffset := by
    rw [destination]
    exact stack_sub_toNat stack hout
  have ha : (stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat =
      (stackPtr s).toNat - offset + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 2^64),
      Nat.mod_eq_of_lt (by rw [hs]; omega), hs]
  apply result.frame
  intro r hr hin
  have hr' : r = registerRegion entry .rdi outputBytes ∨ r = Stack.region entry reserve := by
    simpa using hr
  rcases hr' with rfl | rfl
  · change (entry.regValue .rdi).toNat ≤ _ ∧
      (stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat <
        (entry.regValue .rdi).toNat + outputBytes at hin
    rw [hdn, ha] at hin
    omega
  · change (stackPtr entry).toNat - reserve ≤ _ ∧
      (stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat <
        (Stack.region entry reserve).start + (Stack.region entry reserve).size at hin
    rw [stack_region_end, hsn, ha] at hin
    omega

end P256.Proofs.Program
