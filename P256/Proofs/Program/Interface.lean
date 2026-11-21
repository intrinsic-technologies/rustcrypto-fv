import P256.Spec.Program
import X86Proofs.Program.Execution

set_option autoImplicit false

namespace P256.Proofs.Program

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure CalleePre [bindings : Bindings] (s : RamState) (boundary : ReturnBoundary)
    (entry : BitVec 64) (inputBytes outputBytes : Nat) (stackReserve : Nat) (inputRegister : Syntax.Reg := .rsi) : Prop where
  bindingsSupported : MachineRamUnitStrideDecodable bindings s
  machine : SupportedIntegerMachineState bindings.processor s
  directionFlag : Prelude.RFLAGS.DirectionFlagClear s.RFLAGS
  loaded : ProgramLoaded s
  rip : s.RIP = entry
  inputBounded : (registerRegion s inputRegister inputBytes).Bounded
  inputAllocated : (registerRegion s inputRegister inputBytes).Allocated s.external
  outputBounded : (registerRegion s .rdi outputBytes).Bounded
  outputAllocated : (registerRegion s .rdi outputBytes).Allocated s.external
  stack : Stack.Valid s stackReserve
  separation : MemoryRegion.PairwiseDisjoint
    #v[registerRegion s inputRegister inputBytes, registerRegion s .rdi outputBytes, Stack.region s stackReserve]
  avoids : ∀ region ∈ [registerRegion s .rdi outputBytes, Stack.region s stackReserve],
    region.Avoids (fun a => InProgram a ∨ InPageTables a)
  outerBoundary : ¬ InProgram boundary.rip
  returnInProgram : InProgram (X86Proofs.returnBoundary s).rip

structure CalleeResult [bindings : Bindings] (s t : RamState)
    (boundary : ReturnBoundary) (outputBytes : Nat) (stackReserve : Nat)
    (outputRegister : Syntax.Reg := .rdi) : Prop where
  execution : ∃ fuel, X86Proofs.Advances boundary fuel s t
  rip : t.RIP = (X86Proofs.returnBoundary s).rip
  rsp : t.regValue .rsp = (X86Proofs.returnBoundary s).rsp
  bindingsSupported : MachineRamUnitStrideDecodable bindings t
  machine : SupportedIntegerMachineState bindings.processor t
  calleeSaved : CalleeSavedRegistersUnchanged s t
  directionFlag : DirectionFlagUnset t
  mxcsr : t.MXCSR = s.MXCSR
  fp87 : t.FP87_Control = s.FP87_Control
  frame : MemoryWriteFrame s t
    #v[registerRegion s outputRegister outputBytes, Stack.region s stackReserve]
  loaded : ProgramLoaded t
  allocated : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome

end P256.Proofs.Program
