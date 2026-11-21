import Sha3.Proofs.Finalize.Layout
import Sha3.Proofs.Incremental.State
import Sha3.Proofs.Permutation.Precondition
import X86Proofs.Program.ReadWrite.Bytes

namespace Sha3.Proofs.Finalize

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

def frameBase (s : RamState) : BitVec 64 := s.regValue .rsp - 296

def writeRegions (v : Variant) (s : RamState) (fullState : Bool := false) : Vector MemoryRegion 3 :=
  #v[Stack.region s frameBytes, ⟨(s.regValue .rdi).toNat, 201⟩,
    ⟨(s.regValue .rsi).toNat, (v.digestBytes fullState)⟩]

def digest (v : Variant) (state : Incremental.State)
    (keccak : Bool := false) (fullState : Bool := false) : Standards.NIST.SHA3.Digest (v.digestBytes fullState) :=
  Absorption.digestLanes (Incremental.finalize Keccak.keccakLanes v.rate state (Variant.suffix keccak))
    (v.digestBytes fullState) (v.digestBytes_le_state fullState)

structure CallPre (boundary : ReturnBoundary) (v : Variant) (reset : Bool)
    (state : Incremental.State) (s : RamState)
    (keccak : Bool := false) (fullState : Bool := false) : Prop where
  rip : s.RIP = entryAddress v reset keccak fullState
  stack : Stack.Valid s frameBytes
  stackAvoid : (Stack.region s frameBytes).Avoids fun address ↦
    InProgram address ∨ InPageTables address
  stateRead : MemReadable s (s.regValue .rdi) 201
  outputRead : MemReadable s (s.regValue .rsi) (v.digestBytes fullState)
  stateAvoid : ∀ i < 201, ¬ (InProgram (s.regValue .rdi + BitVec.ofNat 64 i) ∨
    InPageTables (s.regValue .rdi + BitVec.ofNat 64 i))
  outputAvoid : ∀ i < (v.digestBytes fullState), ¬ (InProgram (s.regValue .rsi + BitVec.ofNat 64 i) ∨
    InPageTables (s.regValue .rsi + BitVec.ofNat 64 i))
  stateStack : RangeApart (s.regValue .rdi) 201 (frameBase s) 304
  outputStack : RangeApart (s.regValue .rsi) (v.digestBytes fullState) (frameBase s) 304
  outputState : RangeApart (s.regValue .rsi) (v.digestBytes fullState) (s.regValue .rdi) 201
  aligned : (s.regValue .rdi).toNat % 8 = 0
  direction : DirectionFlagUnset s
  cursor : state.cursor < v.rate
  metadata : (Operand.mem (s.regValue .rdi + 200) : Operand 8).read s =
    BitVec.ofNat 8 state.cursor
  lanes : Permutation.memoryLanes (s.regValue .rdi) s = state.lanes
  target : InProgram (stackTop s)
  resetBoundary : reset = true → s.regValue .rsp ≠ boundary.rsp
  boundary : s.regValue .rsp - 24 ≠ boundary.rsp
  valid : fullState = true → v = .sha256 ∧ keccak = true

structure CallResult (v : Variant) (reset : Bool) (state : Incremental.State)
    (initial final : RamState) (keccak : Bool := false)
    (fullState : Bool := false) : Prop where
  rip : final.RIP = stackTop initial
  stack : final.regValue .rsp = initial.regValue .rsp + 8
  saved : CalleeSavedRegistersUnchanged initial final
  memory : MemoryWriteFrame initial final (writeRegions v initial fullState)
  grows : ∀ address : BitVec 64, (initial.external[address]?).isSome →
    (final.external[address]?).isSome
  rest : scalarFrame final = scalarFrame initial
  output : ∀ i : Fin (v.digestBytes fullState),
    final.external[initial.regValue .rsi + BitVec.ofNat 64 i.val]? = some (digest v state keccak fullState)[i]
  zero : reset = true → Bytes final.external (initial.regValue .rdi) 201 (fun _ ↦ 0)

structure SavedFrame (v : Variant) (initial s : RamState) (fullState : Bool := false) : Prop where
  saved : ∀ r ∈ [Syntax.Reg.rbp, .r12, .r13, .r15], s.regValue r = initial.regValue r
  rbx : (Operand.mem (initial.regValue .rsp - 16) : Operand 64).read s =
    initial.regValue .rbx
  r14 : (Operand.mem (initial.regValue .rsp - 8) : Operand 64).read s =
    initial.regValue .r14
  returnSlot : (Operand.mem (initial.regValue .rsp) : Operand 64).read s = stackTop initial
  memory : MemoryWriteFrame initial s (writeRegions v initial fullState)
  grows : ∀ address : BitVec 64, (initial.external[address]?).isSome →
    (s.external[address]?).isSome
  rest : scalarFrame s = scalarFrame initial

structure BodyFrame (v : Variant) (initial s : RamState) (fullState : Bool := false)
    extends SavedFrame v initial s fullState where
  stack : s.regValue .rsp = initial.regValue .rsp - 24
  stateSaved : s.regValue .rbx = initial.regValue .rdi
  output : s.regValue .r14 = initial.regValue .rsi

structure Padded (v : Variant) (reset : Bool) (state : Incremental.State)
    (initial s : RamState) (keccak : Bool := false) (fullState : Bool := false)
    extends BodyFrame v initial s fullState where
  rip : s.RIP = callAddress v reset keccak fullState
  pointer : s.regValue .rdi = initial.regValue .rdi
  lanes : Permutation.memoryLanes (initial.regValue .rdi) s = fun lane ↦
    (state.lanes lane ^^^ Incremental.byteLanes state.cursor (Variant.suffix keccak) lane) ^^^
      Incremental.byteLanes (v.rate - 1) 0x80 lane

structure Permuted (v : Variant) (reset : Bool) (state : Incremental.State)
    (initial s : RamState) (keccak : Bool := false) (fullState : Bool := false)
    extends BodyFrame v initial s fullState where
  rip : s.RIP = outputAddress v reset keccak fullState
  lanes : Permutation.memoryLanes (initial.regValue .rdi) s =
    Incremental.finalize Keccak.keccakLanes v.rate state (Variant.suffix keccak)

end Sha3.Proofs.Finalize
