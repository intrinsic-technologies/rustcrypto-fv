import Hkdf.Proofs.Key.State
import Hkdf.Proofs.Common.SHA256.Interfaces

set_option autoImplicit false

namespace Hkdf.Proofs.Key.Hash

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Spec.Program

structure Working [Bindings] (initial : RamState) (boundary : ReturnBoundary)
    (s : RamState) : Prop extends Key.State initial boundary s where
  rsp : stackPtr s = blockAddress initial
  outputPointer : s.regValue .rbx = initial.regValue .rdi
  zeroBlock : (⟨(blockAddress initial).toNat, 64⟩ : MemoryRegion).HasBytes s.external
    ⟨Array.replicate 64 0⟩

theorem Prepared.working [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    (prepared : Prepared initial boundary s) : Working initial boundary s :=
  ⟨prepared.toState, prepared.rsp, prepared.outputPointer, prepared.zeroBlock⟩

theorem Working.of_observations [Bindings] {initial s t : RamState}
    {boundary : ReturnBoundary} (state : Working initial boundary s)
    (running : Hkdf.Proofs.Common.CallFrame.Running initial boundary (writeRegions initial) t)
    (saved : (Component.mem (stackPtr initial - 40) 48).Agrees s t)
    (rsp : stackPtr t = stackPtr s)
    (rbx : t.regValue .rbx = s.regValue .rbx)
    (rbp : t.regValue .rbp = s.regValue .rbp)
    (mxcsr : t.MXCSR = s.MXCSR) (fcw : t.FP87_Control = s.FP87_Control)
    (zero : (⟨(blockAddress initial).toNat, 64⟩ : MemoryRegion).HasBytes t.external
      ⟨Array.replicate 64 0⟩) : Working initial boundary t :=
  ⟨state.toState.of_observations running saved rbp mxcsr fcw,
    rsp.trans state.rsp, rbx.trans state.outputPointer, zero⟩

end Hkdf.Proofs.Key.Hash
