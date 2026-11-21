import Sha2.Proofs.Common.SHA256.Absorb.Contract

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Absorb.Table

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field Sha2.Proofs.Common.Machine

structure WellFormed (l : Layout) (reserve : Nat) : Prop where
  chunk : Absorb.WellFormed l.chunk reserve
  storedFits : l.storedOffset + 104 ≤ l.chunk.frameBytes
  copyApart : l.storedOffset = l.chunk.bufferOffset ∨
    l.storedOffset + 104 ≤ l.chunk.bufferOffset ∨ l.chunk.bufferOffset + 104 ≤ l.storedOffset
  pointerFits : l.pointerSlot + 8 ≤ l.chunk.frameBytes
  lengthFits : l.lengthSlot + 8 ≤ l.chunk.frameBytes
  pointerActive : OffsetsApart l.pointerSlot 8 l.chunk.bufferOffset 104
  pointerStored : OffsetsApart l.pointerSlot 8 l.storedOffset 104
  lengthActive : OffsetsApart l.lengthSlot 8 l.chunk.bufferOffset 104
  lengthStored : OffsetsApart l.lengthSlot 8 l.storedOffset 104
  chunkClobbers : ∀ r ∈ l.chunk.clobbered, r ∈ l.clobbered
  indexClobber : l.index.setWidth 5 ∈ l.clobbered
  indexPreserved : l.index.setWidth 5 ∉ l.chunk.clobbered
  bufferSourceClobbers : ∀ r ∈ l.chunk.bufferSource, r.setWidth 5 ∈ l.clobbered
  bufferSourceIndex : ∀ r ∈ l.chunk.bufferSource, r ≠ l.index
  bufferSourceCopies : ∀ r ∈ l.chunk.bufferSource,
    ∀ call ∈ [l.chunk.smallCall, l.chunk.fillCall, l.chunk.tailCall], ∀ copyRegister,
      call.encoding = .register copyRegister → r ≠ copyRegister
  countRegister : ∀ r, l.count = .reg r → r.setWidth 5 ∉ l.chunk.clobbered ∧ r ≠ l.index
  countFits : ∀ offset, l.count = .stack offset → offset + 8 ≤ l.chunk.frameBytes
  countActive : ∀ offset, l.count = .stack offset → OffsetsApart offset 8 l.chunk.bufferOffset 104
  countStored : ∀ offset, l.count = .stack offset → OffsetsApart offset 8 l.storedOffset 104

structure InputData (l : Layout) (sp : BitVec 64) (inputs : Array Input)
    (s : RamState) : Prop where
  sizeBound : inputs.size < 2^61
  messageBound : (message inputs).size < 2^61
  pointersReadable : MemReadable s (memLoad s.external (sp + BitVec.ofNat 64 l.pointerSlot) 64)
    (8 * inputs.size)
  lengthsReadable : MemReadable s (memLoad s.external (sp + BitVec.ofNat 64 l.lengthSlot) 64)
    (8 * inputs.size)
  pointers : ∀ i : Fin inputs.size, memLoad s.external
    (memLoad s.external (sp + BitVec.ofNat 64 l.pointerSlot) 64 + BitVec.ofNat 64 (8 * i.val)) 64 =
      inputs[i].address
  lengths : ∀ i : Fin inputs.size, memLoad s.external
    (memLoad s.external (sp + BitVec.ofNat 64 l.lengthSlot) 64 + BitVec.ofNat 64 (8 * i.val)) 64 =
      BitVec.ofNat 64 inputs[i].bytes.size
  bytes : ∀ i : Fin inputs.size, inputs[i].region.HasBytes s.external inputs[i].bytes
  bounded : ∀ i : Fin inputs.size, inputs[i].region.Bounded

structure LoadPre (l : Layout) (sp : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = l.head
  rsp : stackPtr s = sp
  pointerSlot : MemReadable s (sp + BitVec.ofNat 64 l.pointerSlot) 8
  lengthSlot : MemReadable s (sp + BitVec.ofNat 64 l.lengthSlot) 8
  pointer : MemReadable s (memLoad s.external (sp + BitVec.ofNat 64 l.pointerSlot) 64 +
    (Blocks.readReg s l.index <<< 3)) 8
  length : MemReadable s (memLoad s.external (sp + BitVec.ofNat 64 l.lengthSlot) 64 +
    (Blocks.readReg s l.index <<< 3)) 8
  stored : MemReadable s (l.stored sp) 104
  active : Common.Instructions.CrossPageStore.Writable s (l.chunk.buffer sp) 104
  bufferRegister : l.cloneIn = [] → ∀ r ∈ l.chunk.bufferSource, Blocks.readReg s r = l.chunk.buffer sp
  workingPointer : ∀ r ∈ l.chunk.bufferRestore, Blocks.readReg s r = l.chunk.buffer sp
  storedPointer : l.cloneIn ≠ [] → s.regValue .rdx = l.stored sp
  direction : DirectionFlagUnset s
  separate : l.stored sp = l.chunk.buffer sp ∨
    RangeApart (l.stored sp) 104 (l.chunk.buffer sp) 104
  codeApart : ∀ site ∈ l.load ++ l.cloneIn,
    RangeApart (l.chunk.buffer sp) 104 site.pc (Blocks.bytes site.block).length

structure LoadPost (l : Layout) (sp : BitVec 64) (s t : RamState) : Prop where
  rip : t.RIP = l.chunk.entry
  rsp : stackPtr t = sp
  source : Blocks.readReg t l.chunk.registers.source = memLoad s.external
    (memLoad s.external (sp + BitVec.ofNat 64 l.pointerSlot) 64 + (Blocks.readReg s l.index <<< 3)) 64
  length : Blocks.readReg t l.chunk.registers.length = memLoad s.external
    (memLoad s.external (sp + BitVec.ofNat 64 l.lengthSlot) 64 + (Blocks.readReg s l.index <<< 3)) 64
  position : Blocks.readReg t l.chunk.registers.tail =
    (memLoad s.external (l.stored sp + 63) 8).setWidth 64
  copied : ∀ i < 104, t.external[l.chunk.buffer sp + BitVec.ofNat 64 i]? =
    s.external[l.stored sp + BitVec.ofNat 64 i]?
  bufferRegister : ∀ r ∈ l.chunk.bufferSource, Blocks.readReg t r = l.chunk.buffer sp
  count : l.count.read sp t = l.count.read sp s
  index : Blocks.readReg t l.index = Blocks.readReg s l.index
  agrees : AgreesExcept (l.chunk.clobbered.map Component.reg ++
    (l.chunk.bufferSource.toList.map fun r => Component.reg (r.setWidth 5)) ++
    [.mem (l.chunk.buffer sp) 104, .flags, .rip]) s t
  memory : MemoryWriteFrame s t #v[⟨(l.chunk.buffer sp).toNat, 104⟩]
  registers : ∀ r : BitVec 5, r ∉ l.chunk.clobbered →
    (∀ source ∈ l.chunk.bufferSource, r ≠ source.setWidth 5) →
    (.reg r : Operand 64).read t = (.reg r : Operand 64).read s

structure NextPre (l : Layout) (sp : BitVec 64) (large : Bool) (s : RamState) : Prop where
  rip : s.RIP = if large then l.chunk.largeExit else l.chunk.smallExit
  rsp : stackPtr s = sp
  countBound : (l.count.read sp s).toNat < 2^61
  countRead : ∀ offset, l.count = .stack offset → MemReadable s (sp + BitVec.ofNat 64 offset) 8
  workingPointer : large = true →
    ∀ r ∈ l.chunk.bufferRestore, Blocks.readReg s r = l.chunk.buffer sp
  remaining : (Blocks.readReg s l.index).toNat < (l.count.read sp s).toNat
  active : MemReadable s (l.chunk.buffer sp) 104
  stored : Common.Instructions.CrossPageStore.Writable s (l.stored sp) 104
  direction : DirectionFlagUnset s
  bufferRegister : ∀ r ∈ l.chunk.bufferSource, Blocks.readReg s r = l.chunk.buffer sp
  separate : l.stored sp = l.chunk.buffer sp ∨
    RangeApart (l.stored sp) 104 (l.chunk.buffer sp) 104
  codeApart : ∀ site ∈ (if large then l.nextLarge else l.nextSmall) ++ l.cloneOut,
    RangeApart (l.stored sp) 104 site.pc (Blocks.bytes site.block).length

structure NextPost (l : Layout) (sp : BitVec 64) (s t : RamState) : Prop where
  rip : t.RIP = if Blocks.readReg s l.index + 1 = l.count.read sp s then l.exit else l.head
  rsp : stackPtr t = sp
  index : Blocks.readReg t l.index = Blocks.readReg s l.index + 1
  count : l.count.read sp t = l.count.read sp s
  copied : ∀ i < 104, t.external[l.stored sp + BitVec.ofNat 64 i]? =
    s.external[l.chunk.buffer sp + BitVec.ofNat 64 i]?
  workingPointer : ∀ r ∈ l.chunk.bufferRestore, Blocks.readReg t r = l.chunk.buffer sp
  storedPointer : l.cloneIn ≠ [] → t.regValue .rdx = l.stored sp
  agrees : AgreesExcept (l.chunk.clobbered.map Component.reg ++
    [.reg (l.index.setWidth 5), .mem (l.stored sp) 104, .flags, .rip]) s t
  memory : MemoryWriteFrame s t #v[⟨(l.stored sp).toNat, 104⟩]
  registers : ∀ r : BitVec 5, r ∉ l.chunk.clobbered → r ≠ l.index.setWidth 5 →
    (.reg r : Operand 64).read t = (.reg r : Operand 64).read s

structure CountAt (l : Layout) (sp : BitVec 64) (s : RamState) : Prop where
  readable : ∀ offset, l.count = .stack offset → MemReadable s (sp + BitVec.ofNat 64 offset) 8

structure BlockContracts [Bindings] (l : Layout) (boundary : ReturnBoundary) : Prop where
  load : ∀ sp, AdvanceTriple boundary (LoadPre l sp)
    ((l.load ++ l.cloneIn).flatMap Blocks.Site.code) (LoadPost l sp)
  advance : ∀ sp large, AdvanceTriple boundary (NextPre l sp large)
    (((if large then l.nextLarge else l.nextSmall) ++ l.cloneOut).flatMap Blocks.Site.code)
    (NextPost l sp)

structure CodeFacts (l : Layout) : Prop where
  loaded : ∀ site ∈ l.load ++ l.cloneIn ++ l.cloneOut ++ l.nextSmall ++ l.nextLarge,
    ∀ s, ProgramLoaded s → CodeIn site.code s
  inside : InProgram l.head ∧ InProgram l.exit

structure Separation (l : Layout) (initial s : RamState) (reserve : Nat)
    (inputs : Array Input) : Prop where
  inputApart : ∀ i : Fin inputs.size, inputs[i].region.Disjoint (Stack.region initial reserve)
  pointers : (⟨(memLoad s.external (l.chunk.sp initial + BitVec.ofNat 64 l.pointerSlot) 64).toNat,
    8 * inputs.size⟩ : MemoryRegion).Disjoint (Stack.region initial reserve)
  lengths : (⟨(memLoad s.external (l.chunk.sp initial + BitVec.ofNat 64 l.lengthSlot) 64).toNat,
    8 * inputs.size⟩ : MemoryRegion).Disjoint (Stack.region initial reserve)

def Contract [bindings : Bindings] (l : Layout) : Prop :=
  ∀ {initial s : RamState} {n reserve : Nat} {regions : Vector MemoryRegion n}
    {inputs : Array Input},
    WellFormed l reserve → Absorb.Flow l.chunk → Absorb.CodeFacts l.chunk →
    Absorb.CallTargets l.chunk → Absorb.BlockContracts l.chunk (returnBoundary initial) →
    Absorb.Contract l.chunk → CodeFacts l → BlockContracts l (returnBoundary initial) →
    UnitStringStride bindings → SupportedMachine bindings initial → Stack.Valid initial reserve →
    (Stack.region initial reserve).Avoids (fun a => InProgram a ∨ InPageTables a) →
    ValidReturnAddress initial → ExecutionState initial s regions →
    LoopState l (l.chunk.sp initial) inputs 0 s → CountAt l (l.chunk.sp initial) s → InputData l (l.chunk.sp initial) inputs s →
    Separation l initial s reserve inputs →
    (∀ region ∈ footprint l (l.chunk.sp initial), ∀ a, region.Contains a →
      ∃ outer ∈ regions, outer.Contains a) →
    ∃ t, Finished l initial s t regions inputs

end Sha2.Proofs.Common.SHA256.Absorb.Table
