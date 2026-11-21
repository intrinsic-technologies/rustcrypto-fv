import Sha3.Proofs.Keccak
import Sha3.Proofs.Frame
import X86Proofs.Program.Agrees

namespace Sha3.Proofs.Permutation

open X86 X86.Machine X86Proofs Prelude Sha3.Spec.Program Keccak

inductive Copy where
  | absorb
  | finalize
  deriving DecidableEq

def entryAddress : Copy → BitVec 64
  | .absorb => 0x100bc0
  | .finalize => 0x105c30

def roundAddress (copy : Copy) : BitVec 64 := entryAddress copy + 0xf0

def storeAddress (copy : Copy) : BitVec 64 := entryAddress copy + 0x50b

def returnAddress (copy : Copy) : BitVec 64 := entryAddress copy + 0x5f2

def constantBase : Copy → BitVec 64
  | .absorb => 0x200000
  | .finalize => 0x2000c0

def frameBytes : Nat := 264

def frameBase (initial : RamState) : BitVec 64 := initial.regValue .rsp - 264

def laneOperands (sp : BitVec 64) : Vector (Operand 64) 25 :=
  #v[.mem (sp + 0x18), .mem (sp + 0x80), .mem (sp + 0x88), .mem (sp + 0x78),
    .mem (sp + 0x70), .mem (sp + 0x20), .reg 9, .mem (sp + 0x30), .reg 11,
    .mem (sp + 0x10), .reg 0, .mem (sp + 0x28), .reg 12, .mem (sp + 0x38),
    .reg 13, .reg 5, .reg 1, .reg 15, .reg 14, .reg 3, .mem (sp + 0x50),
    .mem (sp + 0x60), .mem (sp + 0x58), .mem (sp + 0x68), .mem sp]

def readLanes (sp : BitVec 64) (s : RamState) : Lanes :=
  fun i ↦ (laneOperands sp)[i].read s

def memoryLanes (pointer : BitVec 64) (s : RamState) : Lanes :=
  fun i ↦ (Operand.mem (pointer + BitVec.ofNat 64 (8 * i.val)) : Operand 64).read s

def savedRegisters : Vector Syntax.Reg 6 := #v[.rbx, .r12, .r13, .r14, .r15, .rbp]

def writeRegions (initial : RamState) : Vector MemoryRegion 2 :=
  #v[⟨(frameBase initial).toNat, frameBytes⟩, ⟨(initial.regValue .rdi).toNat, 200⟩]

structure CallFrame (initial s : RamState) : Prop where
  stack : s.regValue .rsp = frameBase initial
  pointer : (Operand.mem (frameBase initial + 0xa0) : Operand 64).read s =
    initial.regValue .rdi
  saved : ∀ i : Fin 6,
    (Operand.mem (frameBase initial + BitVec.ofNat 64 (216 + 8 * i.val)) : Operand 64).read s =
      initial.regValue savedRegisters[i]
  returnSlot : (Operand.mem (initial.regValue .rsp) : Operand 64).read s =
    (Operand.mem (initial.regValue .rsp) : Operand 64).read initial
  memory : MemoryWriteFrame initial s (writeRegions initial)
  grows : ∀ address : BitVec 64, (initial.external[address]?).isSome → (s.external[address]?).isSome
  rest : scalarFrame s = scalarFrame initial

def roundPC (copy : Copy) (round : Nat) : BitVec 64 :=
  if round < 24 then roundAddress copy else storeAddress copy

structure RoundInvariant (copy : Copy) (initial : RamState) (round : Nat) (a : Lanes)
    (s : RamState) : Prop where
  frame : CallFrame initial s
  rip : s.RIP = roundPC copy round
  counter : s.regValue .rdx = BitVec.ofNat 64 (8 * round)
  lanes : readLanes (frameBase initial) s = a

structure CallResult (initial final : RamState) (a : Lanes) : Prop where
  rip : final.RIP = (Operand.mem (initial.regValue .rsp) : Operand 64).read initial
  stack : final.regValue .rsp = initial.regValue .rsp + 8
  lanes : memoryLanes (initial.regValue .rdi) final = a
  saved : CalleeSavedRegistersUnchanged initial final
  memory : MemoryWriteFrame initial final (writeRegions initial)
  grows : ∀ address : BitVec 64, (initial.external[address]?).isSome → (final.external[address]?).isSome
  rest : scalarFrame final = scalarFrame initial

theorem roundPC_lt (copy : Copy) {round : Nat} (h : round < 24) : roundPC copy round = roundAddress copy := by
  simp [roundPC, h]

theorem roundPC_24 (copy : Copy) : roundPC copy 24 = storeAddress copy := by rfl

theorem frameBase_add_frameBytes (initial : RamState) :
    frameBase initial + BitVec.ofNat 64 frameBytes = initial.regValue .rsp := by
  exact BitVec.sub_add_cancel _ _

theorem laneOperands_no_counter (sp : BitVec 64) (i : Fin 25) :
    (laneOperands sp)[i] ≠ .reg 2 := by
  finite_cases i <;>
    dsimp [laneOperands] <;> intro h <;> cases h

end Sha3.Proofs.Permutation
