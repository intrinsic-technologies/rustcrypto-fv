import P256.Proofs.Nonce.Update.Zero.State
import P256.Proofs.Program.ScalarFrame.Memory

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Zero

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame

variable [Bindings] {initial s t : RamState} {boundary : ReturnBoundary} {state : State}

theorem work_contains_scratch (pre : DrbgCalleePre initial boundary 0x109f30 1856 state)
    {offset len : Nat} {a : BitVec 64} (span : offset + len ≤ 632)
    (covered : (Component.mem (scratch initial + BitVec.ofNat 64 offset) len).Covers a) :
    (ScalarFrame.workRegion initial 1856).Contains a.toNat := by
  have address : scratch initial + BitVec.ofNat 64 offset =
      stackPtr initial - BitVec.ofNat 64 (680 - offset) := by
    have bound : offset ≤ 680 := by omega
    change stackPtr initial - BitVec.ofNat 64 680 + BitVec.ofNat 64 offset = _
    conv => lhs; rw [show 680 = (680 - offset) + offset by omega]
    rw [BitVec.ofNat_add, ← BitVec.sub_sub, BitVec.sub_add_cancel]
  rw [address] at covered
  exact ScalarFrame.work_contains pre.callee (by omega) (by omega) covered

theorem work_substack (pre : DrbgCalleePre initial boundary 0x109f30 1856 state) {a : Nat}
    (inside : (workRegion initial 1856).Contains a) : (Stack.region initial 1856).Contains a := by
  change (stackPtr initial).toNat - 1856 ≤ a ∧
    a < (stackPtr initial).toNat - 1856 + 1808 at inside
  have bounds := stack_bounds pre.stack
  change (stackPtr initial).toNat - 1856 ≤ a ∧
    a < (Stack.region initial 1856).start + (Stack.region initial 1856).size
  rw [stack_region_end]
  constructor <;> omega

theorem result_stack_byte {outputBytes reserve stackOffset outputOffset offset len : Nat}
    (pre : DrbgCalleePre initial boundary 0x109f30 1856 state)
    (result : CalleeResult s t boundary outputBytes reserve)
    (rsp : stackPtr s = stackPtr initial - BitVec.ofNat 64 stackOffset)
    (output : s.regValue .rdi = stackPtr initial - BitVec.ofNat 64 outputOffset)
    (stackBound : stackOffset ≤ 1856) (outputBound : outputOffset ≤ 1856)
    (bound : offset ≤ 1856) (above : offset + 8 ≤ stackOffset)
    (apart : outputOffset + len ≤ offset ∨ offset + outputBytes ≤ outputOffset)
    {i : Nat} (hi : i < len) (span : len ≤ offset + 8) :
    t.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      s.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  have bounds := stack_bounds pre.stack
  have addr : (stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat =
      (stackPtr initial).toNat - offset + i := by
    rw [BitVec.toNat_add, stack_sub_toNat pre.stack bound, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : i < 2^64), Nat.mod_eq_of_lt (by omega)]
  have sp : (stackPtr s).toNat = (stackPtr initial).toNat - stackOffset := by
    rw [rsp, stack_sub_toNat pre.stack stackBound]
  have out : (s.regValue .rdi).toNat = (stackPtr initial).toNat - outputOffset := by
    rw [output, stack_sub_toNat pre.stack outputBound]
  apply result.frame
  intro region hr hin
  have cases : region = registerRegion s .rdi outputBytes ∨ region = Stack.region s reserve := by
    simpa using hr
  rcases cases with rfl | rfl
  · change (s.regValue .rdi).toNat ≤ _ ∧ _ < (s.regValue .rdi).toNat + outputBytes at hin
    rw [out, addr] at hin
    omega
  · change (stackPtr s).toNat - reserve ≤ _ ∧
      _ < (Stack.region s reserve).start + (Stack.region s reserve).size at hin
    rw [stack_region_end, sp, addr] at hin
    omega

theorem stack_writable8 (pre : DrbgCalleePre initial boundary 0x109f30 1856 state)
    (frame : FrameState initial s) {offset : Nat}
    (bound : offset ≤ 680) (aligned : (680-offset) % 8 = 0) :
    MemWritable s (stackPtr s + BitVec.ofNat 64 offset) 8 := by
  rw [ScalarFrame.scalar_stack_address (frameOffset := 680) frame.rsp (by decide) bound]
  exact writable_of_grow (stack_sub_writable8 (offset := 680-offset) pre.stack
    (fun a ha hp => pre.avoids _ (by simp) a ha (.inr hp)) (by omega) aligned) frame.allocated

end P256.Proofs.Nonce.Update.Zero
