import P256.Proofs.Nonce.Interface
import P256.Proofs.Signing.Search
import P256.Proofs.Program.SaveRegisters

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)

structure Pre [Bindings] (s : RamState) (boundary : ReturnBoundary)
    (orderAddress : BitVec 64) (state : State) : Prop extends
    CalleePre s boundary 0x107330 32 72 2096 where
  outputLength : s.regValue .rdx = 32
  outputAvoids : (registerRegion s .rsi 32).Avoids (fun a => InProgram a ∨ InPageTables a)
  orderBounded : (MemoryRegion.mk orderAddress.toNat 32).Bounded
  orderAllocated : (MemoryRegion.mk orderAddress.toNat 32).Allocated s.external
  orderDisjoint : ∀ region ∈ [registerRegion s .rsi 32, registerRegion s .rdi 72,
    Stack.region s 2096], (MemoryRegion.mk orderAddress.toNat 32).Disjoint region
  generator : GeneratorAt s (s.regValue .rdi) orderAddress state

def frameBase (s : RamState) : BitVec 64 := stackPtr s - 232

def regions (s : RamState) : Vector MemoryRegion 3 :=
  #v[registerRegion s .rdi 72, registerRegion s .rsi 32, Stack.region s 2096]

structure Frame [bindings : Bindings] (initial s : RamState) : Prop where
  bindingsSupported : MachineRamUnitStrideDecodable bindings s
  machine : SupportedIntegerMachineState bindings.processor s
  loaded : ProgramLoaded s
  directionFlag : DirectionFlagUnset s
  allocated : ∀ a : BitVec 64, (initial.external[a]?).isSome → (s.external[a]?).isSome
  frame : MemoryWriteFrame initial s (regions initial)
  rsp : stackPtr s = frameBase initial
  saved : ∀ item ∈ savedRegisters,
    memLoad s.external (stackPtr initial - BitVec.ofNat 64 item.2) 64 = initial.regValue item.1
  returnAddress : memLoad s.external (stackPtr initial) 64 = (returnBoundary initial).rip
  mxcsr : s.MXCSR = initial.MXCSR
  fp87 : s.FP87_Control = initial.FP87_Control

structure Slots (initial s : RamState) : Prop where
  outputSlot : memLoad s.external (frameBase initial + 40) 64 = initial.regValue .rsi
  lengthSlot : memLoad s.external (frameBase initial + 48) 64 = 32
  bitsSlot : memLoad s.external (frameBase initial + 56) 32 = 256
  statePointerSlot : memLoad s.external (frameBase initial + 64) 64 = initial.regValue .rdi + 8
  valuePointerSlot : memLoad s.external (frameBase initial + 136) 64 = initial.regValue .rdi + 40
  generatorPointerSlot : memLoad s.external (frameBase initial + 144) 64 = initial.regValue .rdi

structure Loop [Bindings] (initial s : RamState) (orderAddress : BitVec 64)
    (state : State) : Prop extends Frame initial s, Slots initial s where
  rip : s.RIP = 0x1073a0
  rdi : s.regValue .rdi = initial.regValue .rdi + 8
  r12 : s.regValue .r12 = initial.regValue .rdi + 40
  rbx : s.regValue .rbx = 0x11c930
  generator : GeneratorAt s (initial.regValue .rdi) orderAddress state

structure Generated [Bindings] (initial s : RamState) (orderAddress : BitVec 64)
    (state : State) : Prop extends Frame initial s, Slots initial s where
  rip : s.RIP = 0x1073df
  rdi : s.regValue .rdi = initial.regValue .rdi + 8
  generator : GeneratorAt s (initial.regValue .rdi) orderAddress (updateValue state)
  output : (registerRegion initial .rsi 32).HasBytes s.external (updateValue state).value

structure Updated [Bindings] (initial s : RamState) (orderAddress : BitVec 64)
    (state : State) : Prop extends Frame initial s, Slots initial s where
  rip : s.RIP = 0x1073eb
  generator : GeneratorAt s (initial.regValue .rdi) orderAddress (Signing.Search.nextState state)
  output : (registerRegion initial .rsi 32).HasBytes s.external (updateValue state).value

structure ReturnState [bindings : Bindings] (initial s : RamState)
    (orderAddress : BitVec 64) (nonce : Nat) (state : State) : Prop where
  rip : s.RIP = (returnBoundary initial).rip
  rsp : s.regValue .rsp = (returnBoundary initial).rsp
  bindingsSupported : MachineRamUnitStrideDecodable bindings s
  machine : SupportedIntegerMachineState bindings.processor s
  calleeSaved : CalleeSavedRegistersUnchanged initial s
  directionFlag : DirectionFlagUnset s
  mxcsr : s.MXCSR = initial.MXCSR
  fp87 : s.FP87_Control = initial.FP87_Control
  frame : MemoryWriteFrame initial s (regions initial)
  loaded : ProgramLoaded s
  allocated : ∀ a : BitVec 64, (initial.external[a]?).isSome → (s.external[a]?).isSome
  output : (registerRegion initial .rsi 32).HasBytes s.external
    (Standards.SECG.ECC.Encoding.natToOctets 32 nonce)
  generator : GeneratorAt s (initial.regValue .rdi) orderAddress state

structure Result [Bindings] (initial s : RamState) (boundary : ReturnBoundary)
    (orderAddress : BitVec 64) (nonce : Nat) (state : State) : Prop extends
    ReturnState initial s orderAddress nonce state where
  execution : ∃ fuel, Advances boundary fuel initial s

end P256.Proofs.Nonce.Fill
