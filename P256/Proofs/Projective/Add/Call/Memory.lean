import P256.Proofs.Program.FieldCall.Memory
import P256.Proofs.Projective.Add.Call.Result

set_option autoImplicit false

namespace P256.Proofs.Projective.Add.Call

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame
open X86 X86.Machine X86.UserProcess X86Proofs

theorem stack_result_byte [Bindings] {s entry t : RamState} {boundary : ReturnBoundary}
    {outputOffset outputBytes reserve offset len : Nat}
    (pre : CalleePre s boundary 0x1051f0 96 96 920) (state : FrameState s entry 96 920 640)
    (result : CalleeResult entry t boundary outputBytes reserve)
    (destination : entry.regValue .rdi = stackPtr s - BitVec.ofNat 64 outputOffset)
    (hout : outputOffset ≤ 920) (ho : offset ≤ 632) (hlen : len ≤ offset + 8)
    (hapart : offset + outputBytes ≤ outputOffset ∨ outputOffset + len ≤ offset)
    {i : Nat} (hi : i < len) :
    t.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      entry.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  exact Program.FieldCall.stack_result_byte pre state result destination (by decide) hout ho hlen hapart hi

end P256.Proofs.Projective.Add.Call
