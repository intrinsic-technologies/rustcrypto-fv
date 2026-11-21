import Sha3.Proofs.Permutation.LoadStore.Load.Basic

namespace Sha3.Proofs.Permutation.Load

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

inductive Operation where
  | load (dst : BitVec 5) (lane : Fin 25)
  | store (src : BitVec 5) (slot : Fin 27)
  | clear
  | nop

def operations : Vector (BitVec 64 × Operation) 43 := #v[
  (0x11, .load 0 0),
  (0x14, .store 0 3),
  (0x19, .load 0 1),
  (0x1d, .store 0 16),
  (0x25, .load 0 10),
  (0x29, .load 5 15),
  (0x2d, .load 1 20),
  (0x34, .store 1 10),
  (0x39, .load 1 11),
  (0x3d, .store 1 5),
  (0x42, .load 1 16),
  (0x49, .load 2 21),
  (0x50, .store 2 12),
  (0x55, .load 12 12),
  (0x59, .load 15 17),
  (0x60, .load 2 22),
  (0x67, .store 2 11),
  (0x6c, .load 2 13),
  (0x70, .store 2 7),
  (0x75, .load 14 18),
  (0x7c, .load 2 23),
  (0x83, .store 2 13),
  (0x88, .load 13 14),
  (0x8c, .load 3 19),
  (0x93, .load 2 24),
  (0x9a, .store 2 0),
  (0x9e, .load 11 8),
  (0xa2, .load 2 9),
  (0xa6, .store 2 2),
  (0xab, .load 6 5),
  (0xaf, .store 6 4),
  (0xb4, .load 9 6),
  (0xb8, .load 6 2),
  (0xbc, .store 6 17),
  (0xc4, .load 6 7),
  (0xc8, .store 6 6),
  (0xcd, .load 6 3),
  (0xd1, .store 6 15),
  (0xd6, .store 7 20),
  (0xde, .load 6 4),
  (0xe2, .store 6 14),
  (0xe7, .clear),
  (0xe9, .nop)]

def execute (initial : RamState) (v : Values) : Operation → Values
  | .load dst lane => v.setReg dst (memoryLanes (initial.regValue .rdi) initial lane)
  | .store src slot => v.setSlot slot (v.registers src)
  | .clear => v.setReg 2 0
  | .nop => v

def valuesAt (initial : RamState) (k : Nat) : Values :=
  (operations.toList.take k).foldl (fun v item ↦ execute initial v item.2)
    (Values.initial initial)

def pcAt (copy : Copy) (k : Nat) : BitVec 64 :=
  if h : k < 43 then entryAddress copy + operations[k].1 else roundAddress copy

theorem valuesAt_zero (initial : RamState) : valuesAt initial 0 = Values.initial initial := rfl

theorem valuesAt_succ (initial : RamState) (i : Fin 43) :
    valuesAt initial (i.val + 1) = execute initial (valuesAt initial i.val) operations[i].2 := by
  unfold valuesAt
  rw [List.take_succ_eq_append_getElem (by exact i.isLt), List.foldl_append]
  rfl

set_option maxRecDepth 4096 in
theorem valuesAt_pointer (initial : RamState) (i : Fin 43) :
    match operations[i].2 with
    | .load _ _ => (valuesAt initial i.val).registers 7 = initial.regValue .rdi
    | _ => True := by
  finite_cases i <;> first | rfl | trivial

set_option maxRecDepth 4096 in
theorem final_frame {copy : Copy} {initial s : RamState}
    (hs : Progress initial (valuesAt initial 43) (roundAddress copy) s) : CallFrame initial s := by
  refine ⟨hs.stack, ?_, hs.saved, hs.returnSlot, ?_, hs.grow, hs.rest⟩
  · exact hs.slots 20 (initial.regValue .rdi) rfl
  · apply memoryWriteFrame_mono hs.memory
    intro region hr address ha
    simp only [Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    subst region
    exact ⟨_, by simp [writeRegions], ha⟩

set_option maxRecDepth 4096 in
theorem final_round {copy : Copy} {initial s : RamState}
    (hs : Progress initial (valuesAt initial 43) (roundAddress copy) s) :
    RoundInvariant copy initial 0 (memoryLanes (initial.regValue .rdi) initial) s := by
  refine ⟨final_frame hs, hs.rip, hs.registers 2 (by decide), ?_⟩
  apply funext
  intro i
  change Fin 25 at i
  finite_cases i
  · exact hs.slots 3 _ rfl
  · exact hs.slots 16 _ rfl
  · exact hs.slots 17 _ rfl
  · exact hs.slots 15 _ rfl
  · exact hs.slots 14 _ rfl
  · exact hs.slots 4 _ rfl
  · exact hs.registers 9 (by decide)
  · exact hs.slots 6 _ rfl
  · exact hs.registers 11 (by decide)
  · exact hs.slots 2 _ rfl
  · exact hs.registers 0 (by decide)
  · exact hs.slots 5 _ rfl
  · exact hs.registers 12 (by decide)
  · exact hs.slots 7 _ rfl
  · exact hs.registers 13 (by decide)
  · exact hs.registers 5 (by decide)
  · exact hs.registers 1 (by decide)
  · exact hs.registers 15 (by decide)
  · exact hs.registers 14 (by decide)
  · exact hs.registers 3 (by decide)
  · exact hs.slots 10 _ rfl
  · exact hs.slots 12 _ rfl
  · exact hs.slots 11 _ rfl
  · exact hs.slots 13 _ rfl
  · have h := hs.slots 0 (memoryLanes (initial.regValue .rdi) initial 24) rfl
    change (Operand.mem (frameBase initial + 0) : Operand 64).read s = _ at h
    rw [show frameBase initial + (0 : BitVec 64) = frameBase initial from
      BitVec.add_zero _] at h
    exact h

end Sha3.Proofs.Permutation.Load
