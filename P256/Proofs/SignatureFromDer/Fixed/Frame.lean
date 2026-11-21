import P256.Proofs.SignatureFromDer.Fixed.Interface
import P256.Proofs.Program.ScalarFrame.Memory

set_option autoImplicit false

namespace P256.Proofs.SignatureFromDer.Fixed

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)

structure Frame [bindings : Bindings] (s t : RamState) : Prop where
  bindingsSupported : MachineRamUnitStrideDecodable bindings t
  machine : SupportedIntegerMachineState bindings.processor t
  loaded : ProgramLoaded t
  directionFlag : Prelude.RFLAGS.DirectionFlagClear t.RFLAGS
  allocated : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome
  frame : MemoryWriteFrame s t #v[registerRegion s .rdi 72, Stack.region s 560]
  rsp : stackPtr t = stackPtr s - 184
  savedRbx : (Operand.mem (stackPtr s - 16) : Operand 64).read t = s.regValue .rbx
  savedR14 : (Operand.mem (stackPtr s - 8) : Operand 64).read t = s.regValue .r14
  rbp : t.regValue .rbp = s.regValue .rbp
  r12 : t.regValue .r12 = s.regValue .r12
  r13 : t.regValue .r13 = s.regValue .r13
  r15 : t.regValue .r15 = s.regValue .r15
  returnAddress : (Operand.mem (stackPtr s) : Operand 64).read t =
    (Operand.mem (stackPtr s) : Operand 64).read s
  mxcsr : t.MXCSR = s.MXCSR
  fp87 : t.FP87_Control = s.FP87_Control

structure Stage [Bindings] (s t : RamState) (boundary : ReturnBoundary) : Prop
    extends Frame s t where
  execution : ∃ fuel, X86Proofs.Advances boundary fuel s t
  output : t.regValue .rbx = s.regValue .rdi

structure DecodedState [Bindings] (s t : RamState) (boundary : ReturnBoundary)
    (input : ByteArray) : Prop extends Stage s t boundary where
  rip : t.RIP = 0x109bbe
  first : Nat256At t (stackPtr t + 104) (Arith.uint (input.extract 0 32))
  second : Nat256At t (stackPtr t + 136) (Arith.uint (input.extract 32 64))
  firstRange : Arith.uint (input.extract 0 32) < Operations.domain.n
  secondRange : Arith.uint (input.extract 32 64) < Operations.domain.n

end P256.Proofs.SignatureFromDer.Fixed
