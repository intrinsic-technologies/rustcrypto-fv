import P256.Proofs.Sec1.SquareRoot.State

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program

structure ExponentCallState [Bindings] (s t : RamState) (x : Nat) : Prop where
  frame : FrameState s t
  rip : t.RIP = 0x11448a
  r14 : t.regValue .r14 = stackPtr s - 248
  rsi : t.regValue .rsi = stackPtr s - 392
  rdi : t.regValue .rdi = stackPtr s - 248
  rdx : t.regValue .rdx = 0x202fb8
  rcx : t.regValue .rcx = 254
  r8 : t.regValue .r8 = stackPtr s - 360
  input : ResidueAt t (stackPtr s - 392) x

end P256.Proofs.Sec1.SquareRoot
