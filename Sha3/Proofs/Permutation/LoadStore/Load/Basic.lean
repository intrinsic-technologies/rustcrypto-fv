import Sha3.Proofs.Permutation.LoadStore.Entry
import Sha3.Proofs.Permutation.LoadStore.Memory

namespace Sha3.Proofs.Permutation.Load

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

structure Pre (copy : Copy) (initial : RamState) : Prop where
  entry : EntryStackPre copy initial
  input : MemReadable initial (initial.regValue .rdi) 200
  apart : RangeApart (frameBase initial) frameBytes (initial.regValue .rdi) 200

structure Values where
  registers : BitVec 5 → BitVec 64
  slots : Fin 27 → Option (BitVec 64)

def Values.initial (initial : RamState) : Values :=
  ⟨fun r ↦ (Operand.reg r : Operand 64).read initial, fun _ ↦ none⟩

def Values.setReg (v : Values) (r : BitVec 5) (value : BitVec 64) : Values :=
  { v with registers := fun q ↦ if q = r then value else v.registers q }

def Values.setSlot (v : Values) (i : Fin 27) (value : BitVec 64) : Values :=
  { v with slots := fun j ↦ if j = i then some value else v.slots j }

def slotAddress (initial : RamState) (i : Nat) : BitVec 64 :=
  frameBase initial + BitVec.ofNat 64 (8 * i)

structure Progress (initial : RamState) (v : Values) (p : BitVec 64)
    (s : RamState) : Prop where
  rip : s.RIP = p
  stack : stackPtr s = frameBase initial
  registers : ∀ r : BitVec 5, r ≠ 4 →
    (Operand.reg r : Operand 64).read s = v.registers r
  slots : ∀ i : Fin 27, ∀ value, v.slots i = some value →
    (Operand.mem (slotAddress initial i.val) : Operand 64).read s = value
  saved : ∀ i : Fin 6,
    (Operand.mem (frameBase initial + BitVec.ofNat 64 (216 + 8 * i.val)) : Operand 64).read s =
      initial.regValue savedRegisters[i]
  returnSlot : (Operand.mem (initial.regValue .rsp) : Operand 64).read s =
    (Operand.mem (initial.regValue .rsp) : Operand 64).read initial
  memory : MemoryWriteFrame initial s #v[⟨(frameBase initial).toNat, frameBytes⟩]
  grow : ∀ address : BitVec 64, (initial.external[address]?).isSome →
    (s.external[address]?).isSome
  rest : scalarFrame s = scalarFrame initial

end Sha3.Proofs.Permutation.Load
