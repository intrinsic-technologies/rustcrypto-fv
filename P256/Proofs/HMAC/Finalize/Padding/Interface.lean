import P256.Proofs.HMAC.Interface
import P256.Proofs.HMAC.Finalize.Interface
import P256.Proofs.SHA256.Mathematics.Padding.Finalize

open P256.Proofs.Program
open P256.Proofs.Program.ScalarFrame (workRegion)

set_option autoImplicit false

namespace P256.Proofs.HMAC.Finalize.Padding

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def lengthStart (outer : Bool) : BitVec 64 := if outer then 0x10133c else 0x10109e

def compressionStart (outer : Bool) : BitVec 64 := if outer then 0x1013aa else 0x10110c

def positionRegister (outer : Bool) : Syntax.Reg := if outer then .r12 else .r13

def countRegister (outer : Bool) : Syntax.Reg := if outer then .r13 else .rbp

def hashRegister (outer : Bool) : Syntax.Reg := if outer then .r14 else .r15

structure Padded [Bindings] (initial s : RamState) (message : ByteArray) (outer : Bool) : Prop
    extends ScalarFrame.FrameState initial s 0 672 328 where
  outputPointer : s.regValue .rbx = initial.regValue .rsi
  position : s.regValue (positionRegister outer) = BitVec.ofNat 64 (message.size % 64)
  count : s.regValue (countRegister outer) = BitVec.ofNat 64 (message.size / 64)
  hashPointer : s.regValue (hashRegister outer) = stackPtr initial - 192#64
  buffer : (MemoryRegion.mk (stackPtr initial - 256#64).toNat 64).HasBytes
    s.external (SHA256.paddedBuffer message)
  hash : SHA256.HashStateAt s (stackPtr initial - 192#64)
    (SHA256.compressBlocks P256.Proofs.SHA256.initialHash message)

structure BlockReady [Bindings] (initial s : RamState) (message : ByteArray) : Prop
    extends ScalarFrame.FrameState initial s 0 672 328 where
  outputPointer : s.regValue .rbx = initial.regValue .rsi
  inputPointer : s.regValue .rsi = stackPtr initial - 320#64
  hashPointer : s.regValue .rdi = stackPtr initial - 192#64
  count : s.regValue .rdx = 1
  buffer : (MemoryRegion.mk (stackPtr initial - 320#64).toNat 64).HasBytes
    s.external (SHA256.tailFirst message)
  hash : SHA256.HashStateAt s (stackPtr initial - 192#64)
    (SHA256.compressBlocks P256.Proofs.SHA256.initialHash message)

end P256.Proofs.HMAC.Finalize.Padding
