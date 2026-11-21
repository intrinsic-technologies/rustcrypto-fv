import P256.Proofs.Program.WrapperMemory
import P256.Proofs.Generate.Sampler.Interface

set_option autoImplicit false

namespace P256.Proofs.Generate.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program

def stateRegions (initial : RamState) : Option MemoryRegion → (n : Nat) × Vector MemoryRegion n
  | none => ⟨3,wrapperRegions signingKeyGenerateFromRng initial⟩
  | some region => ⟨4,#v[region,allocatorStateRegion,randomSourceRegion,
      callStack signingKeyGenerateFromRng initial]⟩

structure State [bindings : Bindings] (initial t : RamState) (offset : Nat) (written : Option MemoryRegion := none) : Prop where
  execution : ∃ fuel, Advances (returnBoundary initial) fuel initial t
  bindingsSupported : MachineRamUnitStrideDecodable bindings t
  machine : SupportedIntegerMachineState bindings.processor t
  loaded : ProgramLoaded t
  directionFlag : DirectionFlagUnset t
  rsp : stackPtr t = stackPtr initial - BitVec.ofNat 64 offset
  output : t.regValue .r14 = initial.regValue .rcx
  capacity : t.regValue .rbx = initial.regValue .r8
  savedRbx : memLoad t.external (stackPtr initial - 24) 64 = initial.regValue .rbx
  savedR14 : memLoad t.external (stackPtr initial - 16) 64 = initial.regValue .r14
  savedR15 : memLoad t.external (stackPtr initial - 8) 64 = initial.regValue .r15
  returnAddress : memLoad t.external (stackPtr initial) 64 = (returnBoundary initial).rip
  otherRegisters : ∀ r ∈ [Syntax.Reg.rbp, .r12, .r13], t.regValue r = initial.regValue r
  allocated : ∀ a : BitVec 64, (initial.external[a]?).isSome → (t.external[a]?).isSome
  frame : MemoryWriteFrame initial t (stateRegions initial written).2


structure SamplerEntry [Bindings] (initial s : RamState) (input : ByteArray) : Prop extends
    State initial s 272 where
  pre : Sampler.Pre s (returnBoundary initial) input
  destination : s.regValue .rdi = stackPtr initial - 184
  descriptor : s.regValue .rsi = stackPtr initial - 256
  samplerReturn : (returnBoundary s).rip = 0x106dad
  buffer : s.regValue .r15 = stackPtr initial - 184

end P256.Proofs.Generate.Wrapper
