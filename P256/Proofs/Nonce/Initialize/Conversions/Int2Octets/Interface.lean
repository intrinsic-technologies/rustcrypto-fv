import P256.Proofs.Program.Interface
import P256.Proofs.Field.Representation

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Conversions.Int2Octets

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Field P256.Proofs.SecretKeyFromBytes.Scalar

structure Pre [bindings : Bindings] (s : RamState)
    (boundary : ReturnBoundary) : Prop where
  bindingsSupported : MachineRamUnitStrideDecodable bindings s
  machine : SupportedIntegerMachineState bindings.processor s
  directionFlag : Prelude.RFLAGS.DirectionFlagClear s.RFLAGS
  loaded : ProgramLoaded s
  rip : s.RIP = 0x106f40
  length : s.regValue .rcx = 32
  inputBounded : (registerRegion s .rdi 32).Bounded
  inputAllocated : (registerRegion s .rdi 32).Allocated s.external
  orderBounded : (registerRegion s .rsi 32).Bounded
  orderAllocated : (registerRegion s .rsi 32).Allocated s.external
  outputBounded : (registerRegion s .rdx 32).Bounded
  outputAllocated : (registerRegion s .rdx 32).Allocated s.external
  stack : Stack.Valid s 128
  separation : MemoryRegion.PairwiseDisjoint
    #v[registerRegion s .rdi 32, registerRegion s .rdx 32, Stack.region s 128]
  orderOutput : (registerRegion s .rsi 32).Disjoint (registerRegion s .rdx 32)
  orderStack : (registerRegion s .rsi 32).Disjoint (Stack.region s 128)
  avoids : ∀ region ∈ [registerRegion s .rdx 32, Stack.region s 128],
    region.Avoids (fun a => InProgram a ∨ InPageTables a)
  outerBoundary : ¬ InProgram boundary.rip
  returnInProgram : InProgram (returnBoundary s).rip
  order : Nat256At s (s.regValue .rsi) P256.Spec.Operations.domain.n

structure Result [bindings : Bindings] (s t : RamState)
    (boundary : ReturnBoundary) (value : Nat) : Prop extends CalleeResult s t boundary 32 128 .rdx where
  output : (registerRegion s .rdx 32).HasBytes t.external
    (Standards.RFC.DeterministicSigning.Nonce.intToOctets P256.Spec.Operations.domain.n value)

end P256.Proofs.Nonce.Initialize.Conversions.Int2Octets
