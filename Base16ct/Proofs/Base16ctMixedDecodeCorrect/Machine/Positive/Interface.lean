import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.Memory
import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Decoder.List
import Base16ct.Proofs.Copied.Md5.Proofs.Buffered.Stores.Program
import X86Proofs.Instructions.Call.Form

namespace Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine

open Base16ct.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs

structure MixedInternalCall (initial : RamState) (input : List UInt8) (capacity : Nat)
    (boundary : ReturnBoundary) : Prop where
  rip : initial.RIP = 0x1001c0
  length : (initial.regValue .rsi).toNat = input.length
  capacityArgument : (initial.regValue .r8).toNat = capacity
  inputBound : input.length < 2 ^ 64
  source : MemReadable initial (initial.regValue .rdi) input.length
  bytes : ∀ j (hj : j < input.length),
    initial.external[initial.regValue .rdi + BitVec.ofNat 64 j]? = some input[j]
  output : Base16ct.Proofs.Copied.Md5.Proofs.Memory.MemWritable initial (initial.regValue .rcx) capacity
  outputNonzero : initial.regValue .rcx ≠ 0
  stackAligned : (stackPtr initial).toNat % 8 = 0
  result : input.length / 2 ≤ capacity →
    (∃ output, mixedDecodeList input = some output) →
    Base16ct.Proofs.Copied.Md5.Proofs.Memory.MemWritable initial (initial.regValue .rdx) 8
  stack : Base16ct.Proofs.Copied.Md5.Proofs.Memory.MemWritable initial (stackPtr initial - 24) 24
  outputAvoids : ∀ j < capacity, ¬ InProgram (initial.regValue .rcx + BitVec.ofNat 64 j)
  resultAvoids : input.length / 2 ≤ capacity →
    (∃ output, mixedDecodeList input = some output) →
    ∀ j < 8, ¬ InProgram (initial.regValue .rdx + BitVec.ofNat 64 j)
  resultReserved : input.length / 2 ≤ capacity →
    (∃ output, mixedDecodeList input = some output) →
    ∀ j < 8, ¬ PageTableReserved (initial.regValue .rdx + BitVec.ofNat 64 j)
  stackReserved : ∀ j < 24, ¬ PageTableReserved (stackPtr initial - 24 + BitVec.ofNat 64 j)
  stackAvoids : ∀ j < 24, ¬ InProgram (stackPtr initial - 24 + BitVec.ofNat 64 j)
  sourceOutput : RangeApart (initial.regValue .rdi) input.length (initial.regValue .rcx) capacity
  sourceStack : RangeApart (initial.regValue .rdi) input.length (stackPtr initial - 24) 24
  outputStack : RangeApart (initial.regValue .rcx) capacity (stackPtr initial - 24) 24
  resultOutput : input.length / 2 ≤ capacity →
    (∃ output, mixedDecodeList input = some output) →
    RangeApart (initial.regValue .rdx) 8 (initial.regValue .rcx) (input.length / 2)
  resultStack : input.length / 2 ≤ capacity →
    (∃ output, mixedDecodeList input = some output) →
    RangeApart (initial.regValue .rdx) 8 (stackPtr initial - 24) 24
  returnRead : MemReadable initial (stackPtr initial) 8
  returnValue : stackTop initial = boundary.rip
  returnStack : boundary.rsp = stackPtr initial + 8
  returnLow : boundary.rip.toNat < 2 ^ 32
  returnOutside : OutsideMixed boundary.rip
  returnOutput : RangeApart (stackPtr initial) 8 (initial.regValue .rcx) capacity
  returnResult : input.length / 2 ≤ capacity →
    (∃ output, mixedDecodeList input = some output) →
    RangeApart (stackPtr initial) 8 (initial.regValue .rdx) 8
  returnStackApart : RangeApart (stackPtr initial) 8 (stackPtr initial - 24) 24


theorem MixedInternalCall.stack_word {initial : RamState} {input : List UInt8}
    {capacity : Nat} {boundary : ReturnBoundary}
    (h : MixedInternalCall initial input capacity boundary)
    (offset : Nat) (hOffset : offset + 8 ≤ 24) (hAlign : offset % 8 = 0) :
    X86Proofs.MemWritable initial (stackPtr initial - 24 + BitVec.ofNat 64 offset) 8 := by
  have hb := h.stack.low
  have hbase : (stackPtr initial).toNat = (stackPtr initial - 24).toNat + 24 := by
    have he := congrArg BitVec.toNat (BitVec.sub_add_cancel (stackPtr initial) 24)
    rw [BitVec.toNat_add] at he
    change ((stackPtr initial - 24).toNat + 24) % 2 ^ 64 = (stackPtr initial).toNat at he
    rw [Nat.mod_eq_of_lt (by omega)] at he
    exact he.symm
  apply writable_word_of_aligned
    (Base16ct.Proofs.Copied.Md5.Proofs.Buffered.Stores.writable_sub h.stack offset 8 hOffset)
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show offset < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show (stackPtr initial - 24).toNat + offset < 2 ^ 64 by omega)]
    have ha := h.stackAligned
    rw [hbase] at ha
    omega
  · intro j hj
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact h.stackReserved (offset + j) (by omega)

end Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine
