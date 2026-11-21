import P256.Proofs.Signing.Core.Iteration.Components.Callees
import P256.Proofs.Program.ScalarFrame.Call
import P256.Proofs.Program.ScalarFrame.Work

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Components.Constructor

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar

structure Frame [bindings : Bindings] (s t : RamState) : Prop where
  bindingsSupported : MachineRamUnitStrideDecodable bindings t
  machine : SupportedIntegerMachineState bindings.processor t
  loaded : ProgramLoaded t
  directionFlag : Prelude.RFLAGS.DirectionFlagClear t.RFLAGS
  allocated : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome
  frame : MemoryWriteFrame s t #v[registerRegion s .rdi 72, Stack.region s 512]
  rsp : stackPtr t = stackPtr s - 216
  savedRbx : (Operand.mem (stackPtr s - 24) : Operand 64).read t = s.regValue .rbx
  savedR14 : (Operand.mem (stackPtr s - 16) : Operand 64).read t = s.regValue .r14
  savedR15 : (Operand.mem (stackPtr s - 8) : Operand 64).read t = s.regValue .r15
  rbp : t.regValue .rbp = s.regValue .rbp
  r12 : t.regValue .r12 = s.regValue .r12
  r13 : t.regValue .r13 = s.regValue .r13
  returnAddress : (Operand.mem (stackPtr s) : Operand 64).read t =
    (Operand.mem (stackPtr s) : Operand 64).read s
  mxcsr : t.MXCSR = s.MXCSR
  fp87 : t.FP87_Control = s.FP87_Control

structure Stage [Bindings] (s t : RamState) (boundary : ReturnBoundary) : Prop
    extends Frame s t where
  execution : ∃ fuel, Advances boundary fuel s t
  output : t.regValue .rbx = s.regValue .rdi

structure Decoded [Bindings] (s t : RamState) (boundary : ReturnBoundary)
    (r scalarS : Nat) : Prop extends Stage s t boundary where
  rip : t.RIP = 0x10997d
  first : Nat256At t (stackPtr t + 64) r
  second : Nat256At t (stackPtr t + 96) scalarS

end P256.Proofs.Signing.Core.Iteration.Components.Constructor
