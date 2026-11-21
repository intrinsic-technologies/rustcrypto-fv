import P256.Proofs.Nonce.Update.Interface
import P256.Proofs.Nonce.UpdateValue.Pre
import P256.Proofs.Nonce.UpdateValue.Bytes
import P256.Proofs.Program.ScalarFrame.State

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

abbrev FrameState [Bindings] (initial s : RamState) : Prop :=
  ScalarFrame.FrameState initial s 64 1856 680

def scratch (s : RamState) : BitVec 64 := stackPtr s - 680

structure Saved [Bindings] (initial s : RamState) (state : State) : Prop extends
    FrameState initial s where
  rip : s.RIP = 0x109f41
  statePointer : s.regValue .rdi = initial.regValue .rdi
  descriptors : s.regValue .rsi = initial.regValue .rsi
  inputCount : s.regValue .rdx = initial.regValue .rdx
  drbg : DrbgAt s (initial.regValue .rdi) state

end P256.Proofs.Nonce.Update
