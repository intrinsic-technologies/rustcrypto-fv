import Hkdf.Proofs.Common.StreamPadding.Layout
import Hkdf.Proofs.Common.State
import Hkdf.Proofs.Common.SHA256.Interfaces

set_option autoImplicit false

namespace Hkdf.Proofs.Common.StreamPadding

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Spec.Program
open Hkdf.Proofs.Common.SHA256

structure Result [Bindings] (v : Variant) (initial s t : RamState)
    (boundary : ReturnBoundary) (message : ByteArray) : Prop where
  execution : ∃ fuel, Advances boundary fuel s t
  ready : ReadyToStep t
  running : CallFrame.Running initial boundary (regions v initial) t
  rip : t.RIP = v.pc .exit
  rsp : stackPtr t = stackPtr s
  rbx : t.regValue .rbx = s.regValue .rbx
  rbp : t.regValue v.stableReg = s.regValue v.stableReg
  mxcsr : t.MXCSR = s.MXCSR
  fcw : t.FP87_Control = s.FP87_Control
  frame : MemoryWriteFrame s t (writes v (stackPtr s))
  hashWords : HashStateAt t (stackPtr s + BitVec.ofNat 64 v.hash)
    (compressBlocks Hkdf.Proofs.NIST.SHA256.initialHash (bytePadding message))

end Hkdf.Proofs.Common.StreamPadding
