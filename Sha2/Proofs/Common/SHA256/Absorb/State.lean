import Sha2.Proofs.Common.SHA256.Absorb.Blocks
import Sha2.Proofs.Common.SHA256.Hasher
import Sha2.Proofs.Common.Machine.ExecutionState
import Sha2.Proofs.Wrapper.Absorb.Blocks.Mathematics
import X86Proofs.Instructions.Call.Encode

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Absorb

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

inductive CallEncoding where
  | relative (displacement : BitVec 32)
  | memory (address : AddrMode)
  | register (register : BitVec 4)

def CallEncoding.bytes : CallEncoding → List UInt8
  | .relative disp => encodeCallRel32 disp
  | .memory am => encodeCallM64 am
  | .register r => encodeCallR64 r

structure CallSite where
  pc : BitVec 64
  encoding : CallEncoding

inductive Stage where
  | prepare | smallBranch | emptyTest | emptyBranch
  | smallSetup | smallCall | smallLength | smallStore
  | fillSetup | fillCall | increment | fillCompressSetup | fillCompressCall
  | clearTail | restoreSource | count | countBranch
  | addBlocks | bulkSetup | bulkCall | bulkRestore
  | splitTail | tailStore | tailSetup | tailCall | emptySetup
  deriving DecidableEq

structure Layout where
  initialHash : Array UInt32 := NIST.SHA256.initialHash
  frameBytes : Nat
  bufferOffset : Nat
  registers : Blocks.Registers
  alignedSource : BitVec 4
  savedSource : BitVec 4
  bulkSave : Option (BitVec 4)
  bufferRestore : Option (BitVec 4)
  bufferSource : Option (BitVec 4)
  clobbered : List (BitVec 5)
  entry : BitVec 64
  smallExit : BitVec 64
  largeExit : BitVec 64
  pc : Stage → BitVec 64
  blocks : Stage → List Blocks.Site
  smallCall : CallSite
  fillCall : CallSite
  fillCompressCall : CallSite
  bulkCall : CallSite
  tailCall : CallSite

def Layout.sp (l : Layout) (initial : RamState) : BitVec 64 :=
  stackPtr initial - BitVec.ofNat 64 l.frameBytes

def Layout.buffer (l : Layout) (sp : BitVec 64) : BitVec 64 :=
  sp + BitVec.ofNat 64 l.bufferOffset

def footprint (l : Layout) (sp : BitVec 64) : Vector MemoryRegion 2 :=
  #v[⟨(l.buffer sp).toNat, 104⟩, ⟨(sp - 344).toNat, 344⟩]

structure WellFormed (l : Layout) (reserve : Nat) : Prop where
  capacity : l.frameBytes + 344 ≤ reserve
  aligned : (l.frameBytes + 8) % 16 = 0
  bufferFits : l.bufferOffset + 104 ≤ l.frameBytes
  hashAligned : (l.bufferOffset + 64) % 4 = 0
  preservesStack : (4 : BitVec 5) ∉ l.clobbered

structure Prepared (l : Layout) (sp : BitVec 64) (prior : ByteArray)
    (input : Input) (s : RamState) : Prop where
  rip : s.RIP = l.entry
  rsp : stackPtr s = sp
  hasher : HasherAt s (l.buffer sp) prior l.initialHash
  source : Blocks.readReg s l.registers.source = input.address
  length : Blocks.readReg s l.registers.length = BitVec.ofNat 64 input.bytes.size
  position : Blocks.readReg s l.registers.tail = BitVec.ofNat 64 (prior.size % 64)
  bytes : input.region.HasBytes s.external input.bytes
  bounded : input.region.Bounded
  messageBound : prior.size + input.bytes.size < 2^61
  bufferRegister : ∀ r ∈ l.bufferSource, Blocks.readReg s r = l.buffer sp
  copyRegister : ∀ call ∈ [l.smallCall, l.fillCall, l.tailCall], ∀ r,
    call.encoding = .register r → Blocks.readReg s r = 0x10dd60

structure PhaseFrame (l : Layout) (sp : BitVec 64) (before after : RamState) : Prop where
  memory : MemoryWriteFrame before after (footprint l sp)
  registers : ∀ r : BitVec 5, r.toNat < 16 → r ∉ l.clobbered →
    (.reg r : Operand 64).read after = (.reg r : Operand 64).read before

structure Preserved [Bindings] (l : Layout) (initial before current : RamState)
    {n : Nat} (regions : Vector MemoryRegion n) : Prop where
  state : ExecutionState initial current regions
  rsp : stackPtr current = l.sp initial
  frame : PhaseFrame l (l.sp initial) before current

structure Aligned (l : Layout) (sp : BitVec 64) (prior : ByteArray) (input : Input)
    (consumed : Nat) (s : RamState) : Prop where
  rsp : stackPtr s = sp
  consumedBound : consumed ≤ input.bytes.size
  aligned : (prior ++ input.bytes.extract 0 consumed).size % 64 = 0
  hashWords : HashStateAt s (l.buffer sp + 64)
    (compressBlocks l.initialHash (prior ++ input.bytes.extract 0 consumed))
  blocks : memLoad s.external (l.buffer sp + 96) 64 =
    BitVec.ofNat 64 ((prior ++ input.bytes.extract 0 consumed).size / 64)
  source : Blocks.readReg s l.alignedSource = input.address + BitVec.ofNat 64 consumed
  length : Blocks.readReg s l.registers.remaining = BitVec.ofNat 64 (input.bytes.size - consumed)

structure Finished [Bindings] (l : Layout) (initial before current : RamState)
    {n : Nat} (regions : Vector MemoryRegion n) (prior : ByteArray) (input : Input) : Prop
    extends Preserved l initial before current regions where
  rip : current.RIP = if input.bytes.size < 64 - prior.size % 64 then l.smallExit else l.largeExit
  hasher : HasherAt current (l.buffer (l.sp initial)) (prior ++ input.bytes) l.initialHash
  bufferRestored : 64 - prior.size % 64 ≤ input.bytes.size →
    ∀ r ∈ l.bufferRestore, Blocks.readReg current r = l.buffer (l.sp initial)

namespace Table

inductive Count where
  | reg (register : BitVec 4)
  | stack (offset : Nat)

def Count.read (count : Count) (sp : BitVec 64) (s : RamState) : BitVec 64 :=
  match count with
  | .reg r => Blocks.readReg s r
  | .stack offset => memLoad s.external (sp + BitVec.ofNat 64 offset) 64

structure Layout where
  chunk : Absorb.Layout
  clobbered : List (BitVec 5)
  index : BitVec 4
  count : Count
  pointerSlot : Nat
  lengthSlot : Nat
  storedOffset : Nat
  head : BitVec 64
  exit : BitVec 64
  load : List Blocks.Site
  cloneIn : List Blocks.Site
  cloneOut : List Blocks.Site
  nextSmall : List Blocks.Site
  nextLarge : List Blocks.Site

def Layout.stored (l : Layout) (sp : BitVec 64) : BitVec 64 :=
  sp + BitVec.ofNat 64 l.storedOffset

def footprint (l : Layout) (sp : BitVec 64) : Vector MemoryRegion 3 :=
  #v[⟨(l.chunk.buffer sp).toNat, 104⟩, ⟨(l.stored sp).toNat, 104⟩,
    ⟨(sp - 344).toNat, 344⟩]

structure LoopState (l : Layout) (sp : BitVec 64) (inputs : Array Input)
    (index : Nat) (s : RamState) : Prop where
  rip : s.RIP = l.head
  rsp : stackPtr s = sp
  hasher : HasherAt s (l.stored sp) (Sha2.Proofs.Wrapper.prefixMessage inputs index) l.chunk.initialHash
  indexRegister : Blocks.readReg s l.index = BitVec.ofNat 64 index
  count : l.count.read sp s = BitVec.ofNat 64 inputs.size
  remaining : index < inputs.size
  bufferRegister : l.cloneIn = [] → ∀ r ∈ l.chunk.bufferSource, Blocks.readReg s r = l.chunk.buffer sp
  workingPointer : ∀ r ∈ l.chunk.bufferRestore, Blocks.readReg s r = l.chunk.buffer sp
  storedPointer : l.cloneIn ≠ [] → s.regValue .rdx = l.stored sp
  copyRegister : ∀ call ∈ [l.chunk.smallCall, l.chunk.fillCall, l.chunk.tailCall], ∀ r,
    call.encoding = .register r → Blocks.readReg s r = 0x10dd60

structure Finished [Bindings] (l : Layout) (initial before current : RamState)
    {n : Nat} (regions : Vector MemoryRegion n) (inputs : Array Input) : Prop where
  state : ExecutionState initial current regions
  rip : current.RIP = l.exit
  rsp : stackPtr current = l.chunk.sp initial
  hasher : HasherAt current (l.stored (l.chunk.sp initial)) (message inputs) l.chunk.initialHash
  count : l.count.read (l.chunk.sp initial) current = BitVec.ofNat 64 inputs.size
  memory : MemoryWriteFrame before current (footprint l (l.chunk.sp initial))
  registers : ∀ r : BitVec 5, r.toNat < 16 → r ∉ l.clobbered →
    (.reg r : Operand 64).read current = (.reg r : Operand 64).read before

end Table

end Sha2.Proofs.Common.SHA256.Absorb
