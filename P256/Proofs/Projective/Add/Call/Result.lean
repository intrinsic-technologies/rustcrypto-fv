import P256.Proofs.Program.FieldCall.Result
import P256.Proofs.Field.Stack
import P256.Proofs.Program.ScalarFrame.Call
import X86Proofs.Instructions.Movs.RepTriple

set_option autoImplicit false

namespace P256.Proofs.Projective.Add.Call

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame
open X86 X86.Machine X86.UserProcess X86Proofs

theorem field_call_work_frame [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {target : RamState → BitVec 64} {ret : BitVec 64}
    (pre : CalleePre s boundary 0x1051f0 96 96 920) (state : FrameState s t 96 920 632)
    (effect : (callEffect target ret t).Holds t u) :
    MemoryWriteFrame t u #v[workRegion s 920] := by
  exact Program.FieldCall.field_call_work_frame pre state (by decide) (by decide) effect

theorem stack_result_work_frame [Bindings] {s entry t : RamState} {boundary : ReturnBoundary}
    {outputOffset outputBytes reserve : Nat}
    (pre : CalleePre s boundary 0x1051f0 96 96 920) (state : FrameState s entry 96 920 640)
    (result : CalleeResult entry t boundary outputBytes reserve)
    (destination : entry.regValue .rdi = stackPtr s - BitVec.ofNat 64 outputOffset)
    (hout : outputOffset ≤ 920) (hsaved : outputBytes + 48 ≤ outputOffset)
    (hreserve : reserve + 640 ≤ 920) :
    MemoryWriteFrame entry t #v[workRegion s 920] := by
  exact Program.FieldCall.stack_result_work_frame pre state result destination hout hsaved hreserve (by decide)

theorem after_result [Bindings] {s entry t : RamState} {boundary : ReturnBoundary}
    {outputBytes reserve : Nat}
    (pre : CalleePre s boundary 0x1051f0 96 96 920) (state : FrameState s entry 96 920 640)
    (result : CalleeResult entry t boundary outputBytes reserve)
    (hf : MemoryWriteFrame entry t #v[workRegion s 920]) : FrameState s t 96 920 632 := by
  exact Program.FieldCall.after_result pre state result (by decide) hf

end P256.Proofs.Projective.Add.Call
