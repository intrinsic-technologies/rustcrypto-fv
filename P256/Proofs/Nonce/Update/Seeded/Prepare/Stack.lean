import P256.Proofs.Nonce.Update.State
import P256.Proofs.Program.ScalarFrame.Memory

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Seeded.Prepare

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

variable [Bindings] {initial s : RamState} {boundary : ReturnBoundary} {state : State}

theorem stack_address (frame : FrameState initial s) {offset : Nat} (bound : offset ≤ 680) :
    stackPtr s + BitVec.ofNat 64 offset = stackPtr initial - BitVec.ofNat 64 (680 - offset) :=
  ScalarFrame.scalar_stack_address frame.rsp (by decide) bound

theorem stack_readable (frame : FrameState initial s)
    (pre : DrbgCalleePre initial boundary 0x109f30 1856 state)
    {offset len : Nat} (_large : 680 ≤ 1856) (bound : offset ≤ 680)
    (span : offset + len ≤ 688) :
    MemReadable s (stackPtr s + BitVec.ofNat 64 offset) len := by
  rw [stack_address frame bound]
  exact readable_of_grow (stack_sub_readable pre.stack (by omega) (by omega)) frame.allocated

theorem stack_writable (frame : FrameState initial s)
    (pre : DrbgCalleePre initial boundary 0x109f30 1856 state)
    {offset len : Nat} (_large : 680 ≤ 1856) (_bound : offset ≤ 680)
    (span : offset + len ≤ 680) (positive : 0 < len) :
    P256.Proofs.Common.Instructions.CrossPageStore.Writable s
      (stackPtr s + BitVec.ofNat 64 offset) len :=
  ScalarFrame.stack_writable pre.callee frame (by decide) span positive

theorem stack_writable8 (frame : FrameState initial s)
    (pre : DrbgCalleePre initial boundary 0x109f30 1856 state)
    {offset : Nat} (_large : 680 ≤ 1856) (bound : offset ≤ 680)
    (aligned : (680 - offset) % 8 = 0) :
    MemWritable s (stackPtr s + BitVec.ofNat 64 offset) 8 := by
  rw [stack_address frame bound]
  exact writable_of_grow (stack_sub_writable8 pre.stack
    (fun a ha hp => pre.avoids _ (by simp) a ha (.inr hp)) (by omega) aligned) frame.allocated

theorem stack_codeApart (frame : FrameState initial s)
    (pre : DrbgCalleePre initial boundary 0x109f30 1856 state)
    {offset len pc codeLen : Nat} (_large : 680 ≤ 1856) (_bound : offset ≤ 680)
    (span : offset + len ≤ 680) (codeBound : pc + codeLen ≤ 118431) :
    RangeApart (stackPtr s + BitVec.ofNat 64 offset) len
      (Extracted.textAddress + BitVec.ofNat 64 pc) codeLen :=
  ScalarFrame.stack_code pre.callee frame (by decide) span codeBound

end P256.Proofs.Nonce.Update.Seeded.Prepare
