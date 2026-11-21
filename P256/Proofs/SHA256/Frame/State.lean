import P256.Proofs.SHA256.State
import P256.Proofs.Program.ScalarFrame.Memory
import P256.Proofs.Common.Encoding.Serialize.Convert.SavePointer

set_option autoImplicit false

namespace P256.Proofs.SHA256

open Prelude X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program

structure LoopState [Bindings] (initial current : RamState) (hash : Array UInt32)
    (index count : Nat) : Prop extends ScalarFrame.FrameState initial current 32 336 336 where
  registers : RegistersAt current hash
  inputPointer : current.regValue .rsi = initial.regValue .rsi + BitVec.ofNat 64 (64 * index)
  statePointer : memLoad current.external (stackPtr current + 0xc0) 64 = initial.regValue .rdi
  endPointer : memLoad current.external (stackPtr current + 0xc8) 64 =
    initial.regValue .rsi + BitVec.ofNat 64 (64 * count)

end P256.Proofs.SHA256
