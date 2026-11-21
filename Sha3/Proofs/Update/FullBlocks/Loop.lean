import Sha3.Proofs.Update.FullBlocks.Context

namespace Sha3.Proofs.Update.FullBlocks

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program
open Keccak Permutation

def absorbedPrefix (a : Lanes) (rate : Nat) (bytes : ByteArray) (offset count : Nat) : Lanes :=
  (Array.ofFn fun i : Fin count ↦ Absorption.blockLanes bytes (offset + i.val * rate) rate).foldl
    (fun a block ↦ keccakLanes (fun lane ↦ a lane ^^^ block lane)) a

theorem absorbedPrefix_zero (a : Lanes) (rate : Nat) (bytes : ByteArray) (offset : Nat) :
    absorbedPrefix a rate bytes offset 0 = a := by
  simp [absorbedPrefix]

theorem absorbedPrefix_succ (a : Lanes) (rate : Nat) (bytes : ByteArray) (offset count : Nat) :
    absorbedPrefix a rate bytes offset (count + 1) =
      keccakLanes (fun lane ↦ absorbedPrefix a rate bytes offset count lane ^^^
        Absorption.blockLanes bytes (offset + count * rate) rate lane) := by
  simp only [absorbedPrefix, Array.ofFn_succ, Array.foldl_push, Fin.val_castSucc]

def loopPC (v : Variant) (count index : Nat) : BitVec 64 :=
  if index < count then start v else tailAddress v

def keptRegisters : List (BitVec 5) := [13, 3, 12]

structure LoopInvariant [Bindings] (initial origin : RamState) (bytes : ByteArray)
    (v : Variant) (offset count index : Nat) (s : RamState) : Prop where
  machine : BodyInvariant initial s
  slot : (Operand.mem (frameBase initial) : Operand 64).read s =
    (Operand.mem (frameBase initial) : Operand 64).read origin
  pointer : s.regValue .r15 = initial.regValue .rsi
  input : (Operand.reg 14 : Operand 64).read s =
    initial.regValue .rdx + .ofNat 64 (offset + index * v.rate)
  counter : (Operand.reg 5 : Operand 64).read s = .ofNat 64 (v.rate * (count - index))
  kept : ∀ r ∈ keptRegisters,
    (Operand.reg r : Operand 64).read s = (Operand.reg r : Operand 64).read origin
  lanes : memoryLanes (initial.regValue .rsi) s =
    absorbedPrefix (memoryLanes (initial.regValue .rsi) origin) v.rate bytes offset index
  cursor : Update.cursor (initial.regValue .rsi) s = Update.cursor (initial.regValue .rsi) origin
  rip : s.RIP = loopPC v count index

theorem count_sub_rate (rate total index : Nat) (hi : index < total) :
    BitVec.ofNat 64 (rate * (total - index)) - BitVec.ofNat 64 rate =
      BitVec.ofNat 64 (rate * (total - (index + 1))) := by
  have he : total - index = total - (index + 1) + 1 := by omega
  rw [he, Nat.mul_add, Nat.mul_one, BitVec.ofNat_add, BitVec.add_sub_cancel]

theorem count_test (v : Variant) (count index : Nat)
    (hi : index ≤ count) (hsize : v.rate * count < 2^64) :
    (BitVec.ofNat 64 (v.rate * (count - index))).toNat < v.rate ↔ ¬ index < count := by
  have hp := v.rate_pos
  have hle : v.rate * (count - index) ≤ v.rate * count :=
    Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hle hsize)]
  constructor
  · intro h hindex
    have hmore : 1 ≤ count - index := by omega
    have hm := Nat.mul_le_mul_left v.rate hmore
    omega
  · intro h
    have he : index = count := by omega
    simp [he, hp]

theorem saved_kept {s t : RamState} (h : CalleeSavedRegistersUnchanged s t)
    {r : BitVec 5} (hr : r ∈ keptRegisters) :
    (Operand.reg r : Operand 64).read t = (Operand.reg r : Operand 64).read s := by
  simp only [keptRegisters, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h .r13 (by simp)
  · exact h .rbx (by simp)
  · exact h .r12 (by simp)

theorem LoopInvariant.initial [Bindings] {initial s : RamState} {v : Variant}
    {bytes : ByteArray} {offset count : Nat}
    (machine : BodyInvariant initial s)
    (pointer : s.regValue .r15 = initial.regValue .rsi)
    (input : (Operand.reg 14 : Operand 64).read s = initial.regValue .rdx + .ofNat 64 offset)
    (counter : (Operand.reg 5 : Operand 64).read s = .ofNat 64 (v.rate * count))
    (rip : s.RIP = loopPC v count 0) : LoopInvariant initial s bytes v offset count 0 s := by
  refine ⟨machine, rfl, pointer, ?_, ?_, fun _ _ ↦ rfl, ?_, rfl, rip⟩
  · simpa only [Nat.zero_mul, Nat.add_zero] using input
  · simpa only [Nat.sub_zero] using counter
  · exact (absorbedPrefix_zero _ _ _ _).symm

theorem LoopInvariant.complete [Bindings] {initial origin s : RamState} {v : Variant}
    {bytes : ByteArray} {offset count : Nat}
    (h : LoopInvariant initial origin bytes v offset count count s) :
    s.RIP = tailAddress v ∧ (Operand.reg 5 : Operand 64).read s = 0 ∧
      memoryLanes (initial.regValue .rsi) s =
        absorbedPrefix (memoryLanes (initial.regValue .rsi) origin) v.rate bytes offset count := by
  refine ⟨?_, ?_, h.lanes⟩
  · simpa only [loopPC, Nat.lt_irrefl, ite_false] using h.rip
  · simpa only [Nat.sub_self, Nat.mul_zero, show BitVec.ofNat 64 0 = 0 from rfl] using h.counter

end Sha3.Proofs.Update.FullBlocks
