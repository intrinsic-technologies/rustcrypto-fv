import Sha3.Proofs.Variant
import Sha3.Proofs.Incremental.State
import Sha3.Proofs.Memory
import Sha3.Proofs.Outcome
import Sha3.Proofs.Run
import Sha3.Proofs.Permutation.Layout
import X86Proofs.Program.ReadWrite.Bytes
import X86Proofs.Instructions.Call.Form

namespace Sha3.Proofs.Update

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

def frameBytes : Nat := 56

def stackBytes : Nat := 328

def frameBase (initial : RamState) : BitVec 64 := initial.regValue .rsp - 56

def stackBase (initial : RamState) : BitVec 64 := initial.regValue .rsp - 328

def stateRegion (initial : RamState) : MemoryRegion :=
  ⟨(initial.regValue .rsi).toNat, 201⟩

def writeRegions (initial : RamState) : Vector MemoryRegion 2 :=
  #v[⟨(stackBase initial).toNat, stackBytes⟩, stateRegion initial]

def savedRegisters : Vector Syntax.Reg 6 := #v[.rbx, .r12, .r13, .r14, .r15, .rbp]

def cursor (pointer : BitVec 64) (s : RamState) : Nat :=
  ((Operand.mem (pointer + 200) : Operand 8).read s).toNat

structure StateAt (pointer : BitVec 64) (state : Incremental.State) (s : RamState) : Prop where
  lanes : Permutation.memoryLanes pointer s = state.lanes
  cursor : cursor pointer s = state.cursor

structure SavedFrame (initial s : RamState) : Prop where
  saved : ∀ i : Fin 6,
    (Operand.mem (frameBase initial + BitVec.ofNat 64 (8 + 8 * i.val)) : Operand 64).read s =
      initial.regValue savedRegisters[i]
  returnSlot : (Operand.mem (initial.regValue .rsp) : Operand 64).read s =
    (Operand.mem (initial.regValue .rsp) : Operand 64).read initial

structure CallContext [Bindings] (v : Variant) (initial : RamState)
    (bytes : ByteArray) (state : Incremental.State) : Prop where
  rip : initial.RIP = v.updateAddress
  ready : ReadyToStep initial
  loaded : ProgramLoaded initial
  stack : Stack.Valid initial stackBytes
  stateRead : MemReadable initial (initial.regValue .rsi) 201
  inputRead : MemReadable initial (initial.regValue .rdx) bytes.size
  inputBytes : Bytes initial.external (initial.regValue .rdx) bytes.size
    (fun i ↦ (bytes.data[i]?).getD 0)
  length : initial.regValue .rcx = BitVec.ofNat 64 bytes.size
  cursorPointer : initial.regValue .rdi = initial.regValue .rsi + 200
  cursor_lt : state.cursor < v.rate
  state : StateAt (initial.regValue .rsi) state initial
  stateStack : RangeApart (initial.regValue .rsi) 201 (stackBase initial) 336
  inputApart : ∀ region ∈ writeRegions initial,
    (⟨(initial.regValue .rdx).toNat, bytes.size⟩ : MemoryRegion).Disjoint region
  avoids : ∀ region ∈ writeRegions initial,
    region.Avoids (fun address ↦ InProgram address ∨ InPageTables address)
  target : InProgram (stackTop initial)

structure BodyInvariant [Bindings] (initial s : RamState) : Prop where
  ready : ReadyToStep s
  loaded : ProgramLoaded s
  stack : s.regValue .rsp = frameBase initial
  saved : SavedFrame initial s
  memory : MemoryWriteFrame initial s (writeRegions initial)
  grows : ∀ address : BitVec 64, (initial.external[address]?).isSome →
    (s.external[address]?).isSome
  rest : scalarFrame s = scalarFrame initial

structure CallResult (initial final : RamState) (state : Incremental.State) : Prop where
  rip : final.RIP = stackTop initial
  stack : final.regValue .rsp = initial.regValue .rsp + 8
  state : StateAt (initial.regValue .rsi) state final
  saved : CalleeSavedRegistersUnchanged initial final
  memory : MemoryWriteFrame initial final (writeRegions initial)
  grows : ∀ address : BitVec 64, (initial.external[address]?).isSome →
    (final.external[address]?).isSome
  rest : scalarFrame final = scalarFrame initial

def partialAddress (v : Variant) : BitVec 64 := v.updateAddress + 0x14

def divisionAddress (v : Variant) : BitVec 64 := v.updateAddress + 0xec

def fullBlockAddress : Variant → BitVec 64
  | .sha224 => 0x1009c0 | .sha256 => 0x1006b0
  | .sha384 => 0x1003d0 | .sha512 => 0x100120

def tailAddress : Variant → BitVec 64
  | .sha224 => 0x100a7d | .sha256 => 0x10075f
  | .sha384 => 0x10044c | .sha512 => 0x10017c

def cursorWriteAddress : Variant → BitVec 64
  | .sha224 => 0x100ba3 | .sha256 => 0x100883
  | .sha384 => 0x100563 | .sha512 => 0x100293

end Sha3.Proofs.Update
