import P256.Spec
import X86Proofs.Program.Execution

set_option autoImplicit false

namespace P256.Proofs.ReadBe

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Pre [bindings : Bindings] (s : RamState) (boundary : ReturnBoundary) : Prop where
  bindingsSupported : MachineRamUnitStrideDecodable bindings s
  machine : SupportedIntegerMachineState bindings.processor s
  directionFlag : DirectionFlagUnset s
  loaded : ProgramLoaded s
  rip : s.RIP = 0x119090
  count : s.regValue .rsi = 32
  limbs : s.regValue .rcx = 4
  bits : s.regValue .r8 = 256
  inputBounded : (registerRegion s .rdi 32).Bounded
  inputAllocated : (registerRegion s .rdi 32).Allocated s.external
  outputBounded : (registerRegion s .rdx 32).Bounded
  outputAllocated : (registerRegion s .rdx 32).Allocated s.external
  stack : Stack.Valid s 128
  separation : MemoryRegion.PairwiseDisjoint
    #v[registerRegion s .rdi 32, registerRegion s .rdx 32, Stack.region s 128]
  avoids : ∀ region ∈ [registerRegion s .rdx 32, Stack.region s 128],
    region.Avoids (fun a => InProgram a ∨ InPageTables a)
  outerBoundary : ¬ InProgram boundary.rip
  returnInProgram : InProgram (returnBoundary s).rip

structure Result [bindings : Bindings] (s t : RamState) (boundary : ReturnBoundary)
    (input : ByteArray) : Prop where
  execution : ∃ fuel, Advances boundary fuel s t
  rip : t.RIP = (returnBoundary s).rip
  rsp : t.regValue .rsp = (returnBoundary s).rsp
  bindingsSupported : MachineRamUnitStrideDecodable bindings t
  machine : SupportedIntegerMachineState bindings.processor t
  calleeSaved : CalleeSavedRegistersUnchanged s t
  directionFlag : DirectionFlagUnset t
  mxcsr : t.MXCSR = s.MXCSR
  fp87 : t.FP87_Control = s.FP87_Control
  frame : MemoryWriteFrame s t #v[registerRegion s .rdx 32, Stack.region s 128]
  loaded : ProgramLoaded t
  allocated : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome
  status : (Operand.reg 0 : Operand 8).read t = 255
  value : ∀ j < 4, memLoad t.external (s.regValue .rdx + BitVec.ofNat 64 (8 * j)) 64 =
    BitVec.ofNat 64 (Arith.uint input / 2 ^ (64 * j))

end P256.Proofs.ReadBe
