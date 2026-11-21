import P256.Proofs.HMAC.Interface
import P256.Proofs.HMAC.Finalize.FrameSupport
import P256.Proofs.HMAC.State
import P256.Proofs.HMAC.Finalize.Memory

open P256.Proofs.Program
open P256.Proofs.Program.ScalarFrame (workRegion)

set_option autoImplicit false

namespace P256.Proofs.HMAC.Finalize

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def paddingStart (outer : Bool) : BitVec 64 := if outer then 0x101255 else 0x100fb7

def paddingEnd (outer : Bool) : BitVec 64 := if outer then 0x1013af else 0x101111

def scratchRegion (initial : RamState) : MemoryRegion :=
  ⟨(stackPtr initial).toNat - 672, 520⟩

structure Buffered [Bindings] (initial s : RamState) (message : ByteArray) : Prop
    extends ScalarFrame.FrameState initial s 0 672 328 where
  outputPointer : s.regValue .rbx = initial.regValue .rsi
  state : Sha256StateAt s (stackPtr initial - 256#64) message

structure Prepared [Bindings] (initial s : RamState) (key input : ByteArray) : Prop
    extends Buffered initial s (keyPad key 0x36 ++ input) where
  outer : Sha256StateAt s (stackPtr initial - 152#64) (keyPad key 0x5c)

structure Compressed [Bindings] (initial s : RamState) (message : ByteArray) : Prop
    extends ScalarFrame.FrameState initial s 0 672 328 where
  outputPointer : s.regValue .rbx = initial.regValue .rsi
  hash : SHA256.HashStateAt s (stackPtr initial - 192#64)
    (P256.Proofs.SHA256.Reference.compress (SHA256.compressBlocks P256.Proofs.SHA256.initialHash message)
      (Standards.NIST.SHA2.bytesToBits (SHA256.tailFirst message)))

end P256.Proofs.HMAC.Finalize
