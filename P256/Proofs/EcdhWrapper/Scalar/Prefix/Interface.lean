import P256.Proofs.EcdhWrapper.Scalar.Selected
import P256.Proofs.EcdhWrapper.Nonzero

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Scalar

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open SecretKeyFromBytes.Scalar (Nat256At)

structure CheckedPrefix [bindings : Bindings] (initial t : RamState) (secret : ByteArray) : Prop where
  execution : ∃ fuel, Advances (returnBoundary initial) fuel initial t
  rip : t.RIP = 0x106923
  rsp : stackPtr t = stackPtr initial-504
  nonzero : (t.regValue .rax).setWidth 8 = 1
  valid : (t.regValue .rbp).setWidth 8 = 1
  pointers : t.regValue .r12 = initial.regValue .rdi
  count : t.regValue .r13 = 2
  lengths : t.regValue .r15 = initial.regValue .rdx
  scalar : Nat256At t (stackPtr initial-264) (Arith.uint secret)
  frame : MemoryWriteFrame initial t (wrapperRegions ecdhDiffieHellman initial)
  bindingsSupported : MachineRamUnitStrideDecodable bindings t
  machine : SupportedIntegerMachineState bindings.processor t
  directionFlag : DirectionFlagUnset t
  loaded : ProgramLoaded t
  allocated : ∀ a : BitVec 64, (initial.external[a]?).isSome → (t.external[a]?).isSome
  saved : ∀ reg ∈ savedRegisters,
    memLoad t.external (stackPtr initial-BitVec.ofNat 64 reg.2) 64 = initial.regValue reg.1
  returnAddress : memLoad t.external (stackPtr initial) 64 = (returnBoundary initial).rip
  output : memLoad t.external (stackPtr initial-472) 64 = initial.regValue .rcx
  capacity : memLoad t.external (stackPtr initial-464) 64 = initial.regValue .r8
  mxcsr : t.MXCSR = initial.MXCSR
  fp87 : t.FP87_Control = initial.FP87_Control

end P256.Proofs.EcdhWrapper.Scalar
