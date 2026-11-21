import P256.Proofs.Program.CalleeStackFrame
import P256.Proofs.Program.FieldCall.Result

set_option autoImplicit false

namespace P256.Proofs.Program.FieldCall

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame
open X86 X86.Machine X86.UserProcess X86Proofs

variable {outerEntry : BitVec 64} {outerInput outerOutput outerReserve frameOffset : Nat}

variable {inputRegister : Syntax.Reg}

theorem stack_result_byte [Bindings] {s entry t : RamState} {boundary : ReturnBoundary}
    {outputOffset outputBytes reserve offset len : Nat}
    (pre : CalleePre s boundary outerEntry outerInput outerOutput outerReserve inputRegister) (state : FrameState s entry outerOutput outerReserve (BitVec.ofNat 64 (frameOffset + 8)))
    (result : CalleeResult entry t boundary outputBytes reserve)
    (destination : entry.regValue .rdi = stackPtr s - BitVec.ofNat 64 outputOffset)
    (hframe : frameOffset + 8 ≤ outerReserve)
    (hout : outputOffset ≤ outerReserve) (ho : offset ≤ frameOffset) (hlen : len ≤ offset + 8)
    (hapart : offset + outputBytes ≤ outputOffset ∨ outputOffset + len ≤ offset)
    {i : Nat} (hi : i < len) :
    t.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      entry.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? :=
  result.stack_byte pre.stack state.rsp destination hframe hout ho hlen hapart hi

end P256.Proofs.Program.FieldCall
