import P256.Proofs.Nonce.Update.Frame
import P256.Proofs.Program.ScalarFrame.Call
import P256.Proofs.Program.CalleeStack
import P256.Proofs.HMAC.State

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem hash_pre [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {outerEntry : BitVec 64} {reserve : Nat} {state : State}
    (pre : DrbgCalleePre initial boundary outerEntry reserve state)
    (layout : StackCallLayout reserve 32 168 672)
    (frame : ScalarFrame.FrameState initial s 64 reserve (BitVec.ofNat 64 layout.stackOffset))
    (rip : s.RIP = 0x100f10)
    (source : s.regValue .rsi = stackPtr initial - BitVec.ofNat 64 layout.inputOffset)
    (destination : s.regValue .rdi = stackPtr initial - BitVec.ofNat 64 layout.outputOffset)
    (ret : InProgram (returnBoundary s).rip) :
    HMAC.HashCalleePre s boundary 0x100f10 168 672 := by
  refine ⟨CalleePre.of_stack pre.callee layout frame.bindingsSupported frame.machine
    frame.directionFlag frame.loaded frame.allocated rip frame.rsp source destination ret, ?_⟩
  intro a ha hp
  apply pre.avoids (Stack.region initial reserve) (by simp) a ?_ hp
  have bounds := stack_bounds pre.stack
  have capacity := layout.capacity
  have above := layout.inputAbove
  have inputEnd := layout.inputEnd
  change (s.regValue .rsi).toNat ≤ a.toNat ∧ a.toNat < (s.regValue .rsi).toNat + 32 at ha
  rw [source, stack_sub_toNat pre.stack (by omega)] at ha
  change (stackPtr initial).toNat - reserve ≤ a.toNat ∧
    a.toNat < (Stack.region initial reserve).start + (Stack.region initial reserve).size
  rw [stack_region_end]
  constructor <;> omega

end P256.Proofs.Nonce.Update.Finish
