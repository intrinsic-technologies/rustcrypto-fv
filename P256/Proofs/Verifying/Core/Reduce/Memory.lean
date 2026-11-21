import P256.Proofs.Verifying.Core.Reduce.Interface
import P256.Proofs.Program.ScalarFrame.Memory
import P256.Proofs.Program.ScalarFrame.Input

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Reduce

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program

abbrev FrameState [Bindings] (s t : RamState) := ScalarFrame.FrameState s t 32 104 88
abbrev workRegion (s : RamState) := ScalarFrame.workRegion s 104

export ScalarFrame (work_contains)

theorem scalar_stack_address {s t : RamState} (hsp : stackPtr t = stackPtr s - 88)
    {offset : Nat} (h : offset ≤ 88) :
    stackPtr t + BitVec.ofNat 64 offset = stackPtr s - BitVec.ofNat 64 (88 - offset) :=
  ScalarFrame.scalar_stack_address (frameOffset := 88) hsp (by decide) h

theorem stack_readable [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x113120 32 32 104) (state : FrameState s t)
    {offset len : Nat} (bound : offset + len ≤ 88) :
    MemReadable t (stackPtr t + BitVec.ofNat 64 offset) len :=
  ScalarFrame.stack_readable (frameOffset := 88) pre state (by decide) bound

theorem stack_code [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x113120 32 32 104) (state : FrameState s t)
    {offset len codeOffset codeLen : Nat} (bound : offset + len ≤ 88)
    (codeBound : codeOffset + codeLen ≤ 118431) :
    RangeApart (stackPtr t + BitVec.ofNat 64 offset) len
      (Extracted.textAddress + BitVec.ofNat 64 codeOffset) codeLen :=
  ScalarFrame.stack_code (frameOffset := 88) pre state (by decide) bound codeBound

end P256.Proofs.Verifying.Core.Reduce
