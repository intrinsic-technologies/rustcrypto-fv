import Hkdf.Proofs.NewExpand.Calls
import Hkdf.Proofs.Common.CallFrame
import Hkdf.Proofs.Common.Encoding.Serialize.State

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Extract

open Hkdf.Spec Hkdf.Spec.Program Hkdf.Proofs.Common
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def base (initial : RamState) : BitVec 64 := stackPtr initial - 456

structure Saved (initial s : RamState) : Prop where
  registers : ∀ slot ∈ Encoding.Serialize.savedRegisters,
    memLoad s.external (stackPtr initial - BitVec.ofNat 64 slot.2) 64 = initial.regValue slot.1
  returnAddress : stackTop initial = memLoad s.external (stackPtr initial) 64
  mxcsr : s.MXCSR = initial.MXCSR
  fcw : s.FP87_Control = initial.FP87_Control

structure Frame [Bindings] (initial s : RamState) (boundary : ReturnBoundary) : Prop extends
    CallFrame.Running initial boundary #v[Stack.region initial 2264] s, Saved initial s where
  rsp : stackPtr s = base initial
  outputPtr : memLoad s.external (base initial + 80) 64 = initial.regValue .rdi

structure Normalized [Bindings] (initial s : RamState) (boundary : ReturnBoundary)
    (salt : Option ByteArray) : Prop extends Frame initial s boundary where
  rip : s.RIP = 0x10fadf
  ikmPtr : s.regValue .r15 = initial.regValue .rcx
  ikmLen : s.regValue .r14 = initial.regValue .r8
  block : (⟨(base initial + 120).toNat, 64⟩ : MemoryRegion).HasBytes s.external
    (HMAC.keyBlock (salt.getD (RFC5869.defaultSalt .sha256)))

structure Initialized [Bindings] (initial s : RamState) (boundary : ReturnBoundary)
    (salt : Option ByteArray) : Prop extends Frame initial s boundary where
  rip : s.RIP = 0x10fc63
  ikmPtr : s.regValue .r15 = initial.regValue .rcx
  ikmLen : s.regValue .r14 = initial.regValue .r8
  hashPtr : s.regValue .rax = base initial + 184
  hmac : HmacAt s (base initial + 120) (salt.getD (RFC5869.defaultSalt .sha256)) ByteArray.empty

structure Updated [Bindings] (initial s : RamState) (boundary : ReturnBoundary)
    (salt : Option ByteArray) (ikm : ByteArray) : Prop extends Frame initial s boundary where
  rip : s.RIP = 0x10fccb
  hmac : HmacAt s (base initial + 120) (salt.getD (RFC5869.defaultSalt .sha256)) ikm

end Hkdf.Proofs.NewExpand.Extract
