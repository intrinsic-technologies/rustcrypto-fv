import P256.Proofs.Nonce.Interface

set_option autoImplicit false

namespace P256.Proofs.Nonce

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

structure DrbgCalleePre [bindings : Bindings] (s : RamState) (boundary : ReturnBoundary)
    (entry : BitVec 64) (reserve : Nat) (state : State) : Prop where
  bindingsSupported : MachineRamUnitStrideDecodable bindings s
  machine : SupportedIntegerMachineState bindings.processor s
  directionFlag : Prelude.RFLAGS.DirectionFlagClear s.RFLAGS
  loaded : ProgramLoaded s
  rip : s.RIP = entry
  stateBounded : (registerRegion s .rdi 64).Bounded
  stateAllocated : (registerRegion s .rdi 64).Allocated s.external
  stack : Stack.Valid s reserve
  separation : MemoryRegion.Disjoint (registerRegion s .rdi 64) (Stack.region s reserve)
  avoids : ∀ region ∈ [registerRegion s .rdi 64, Stack.region s reserve],
    region.Avoids (fun a => InProgram a ∨ InPageTables a)
  outerBoundary : ¬ InProgram boundary.rip
  returnInProgram : InProgram (X86Proofs.returnBoundary s).rip
  stateBytes : DrbgAt s (s.regValue .rdi) state

structure DrbgCalleeResult [Bindings] (s t : RamState)
    (boundary : ReturnBoundary) (reserve : Nat) (state : State) : Prop
    extends CalleeResult s t boundary 64 reserve where
  stateBytes : DrbgAt t (s.regValue .rdi) state

abbrev UpdateValuePre [Bindings] (s : RamState) (boundary : ReturnBoundary)
    (state : State) : Prop := DrbgCalleePre s boundary 0x10a900 1168 state

end P256.Proofs.Nonce
