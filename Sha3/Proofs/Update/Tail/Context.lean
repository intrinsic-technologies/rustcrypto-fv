import Sha3.Proofs.Update.Layout
import Sha3.Proofs.Update.Frame
import Sha3.Proofs.LaneMemory
import Sha3.Proofs.Incremental.Chunks

namespace Sha3.Proofs.Update.Tail

open X86 X86.Machine X86.UserProcess X86Proofs Sha3.Spec.Program

structure Context [Bindings] (v : Variant) (pointer source completed : BitVec 64)
    (remaining : Nat) (initial input : Nat → UInt8) (s : RamState) : Prop where
  ready : ReadyToStep s
  code : CodeIn Extracted.programImage s
  rip : s.RIP = tailAddress v
  pointerReg : (Operand.reg 15 : Operand 64).read s = pointer
  sourceReg : (Operand.reg 3 : Operand 64).read s = source
  completedReg : (Operand.reg 13 : Operand 64).read s = completed
  remainingReg : (Operand.reg 12 : Operand 64).read s = BitVec.ofNat 64 remaining
  cursorRead : MemReadable s (s.regValue .rsp) 8
  cursorSlot : (Operand.mem (s.regValue .rsp) : Operand 64).read s = pointer + 200
  remaining_lt : remaining < v.rate
  sourceBytes : Bytes s.external (source + completed) remaining input
  stateBytes : Bytes s.external pointer 200 initial
  sourceLow : (source + completed).toNat + remaining ≤ 2 ^ 32
  stateLow : pointer.toNat + 200 ≤ 2 ^ 32
  apart : RangeApart pointer 200 (source + completed) remaining
  avoids : ∀ i < 200, ¬ (InProgram (pointer + BitVec.ofNat 64 i) ∨
    InPageTables (pointer + BitVec.ofNat 64 i))

def clobbers (pointer : BitVec 64) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 3, .reg 6, .reg 7, .reg 8, .reg 13, .reg 15,
    .mem pointer 200, .flags, .rip]

structure Result [Bindings] (v : Variant) (pointer : BitVec 64) (remaining : Nat)
    (initial input : Nat → UInt8) (s t : RamState) : Prop where
  ready : ReadyToStep t
  code : CodeIn Extracted.programImage t
  rip : t.RIP = cursorWriteAddress v
  remainingReg : (Operand.reg 1 : Operand 64).read t = BitVec.ofNat 64 remaining
  cursorReg : (Operand.reg 7 : Operand 64).read t = pointer + 200
  stateBytes : Bytes t.external pointer 200
    (fun i ↦ initial i ^^^ (if i < remaining then input i else 0))
  frame : AgreesExcept (clobbers pointer) s t

theorem Result.bodyInvariant [Bindings] {v : Variant} {caller s t : RamState}
    {bytes : ByteArray} {state : Incremental.State} {remaining : Nat}
    {initial input : Nat → UInt8} (hc : CallContext v caller bytes state)
    (hi : BodyInvariant caller s)
    (hr : Result v (caller.regValue .rsi) remaining initial input s t) :
    BodyInvariant caller t := by
  apply hi.of_stateWrites hc hr.ready hr.frame
  · intro c hcm address hcover
    simp only [clobbers, List.mem_cons, List.not_mem_nil, or_false] at hcm
    rcases hcm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hcover.elim
    obtain ⟨i, hi, rfl⟩ := hcover
    exact ⟨i, by omega, rfl⟩
  · simp [clobbers]

theorem Context.sourceBytes_of_frame [Bindings] {v : Variant} {pointer source completed : BitVec 64}
    {remaining : Nat} {initial input : Nat → UInt8} {s t : RamState}
    (hc : Context v pointer source completed remaining initial input s)
    (hframe : AgreesExcept (clobbers pointer) s t) :
    Bytes t.external (source + completed) remaining input := by
  apply hc.sourceBytes.of_agreesExcept hframe
  intro i hi c hcm hcover
  simp only [clobbers, List.mem_cons, List.not_mem_nil, or_false] at hcm
  rcases hcm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hcover.elim
  obtain ⟨j, hj, he⟩ := hcover
  exact hc.apart j hj i hi he.symm

theorem memoryLanes_xor_slice {s t : RamState} (pointer : BitVec 64) (bytes : ByteArray)
    (initial : Nat → UInt8) (hinitial : Bytes s.external pointer 200 initial)
    (hbytes : Bytes t.external pointer 200
      (fun i ↦ initial i ^^^ (if i < bytes.size then (bytes.data[i]?).getD 0 else 0))) :
    Permutation.memoryLanes pointer t = fun lane ↦
      Permutation.memoryLanes pointer s lane ^^^ Incremental.sliceLanes 0 bytes lane := by
  apply LaneMemory.memoryLanes_eq_of_byteFunction pointer t _ _ hbytes
  intro lane j
  rw [storedByte_xor, LaneMemory.storedByte_memoryLanes]
  have hi : 8 * lane.val + j.val < 200 := by omega
  have he : memByte s.external (pointer + BitVec.ofNat 64 (8 * lane.val + j.val)) =
      initial (8 * lane.val + j.val) := by
    change (s.external[pointer + BitVec.ofNat 64 (8 * lane.val + j.val)]?).getD 0 = _
    rw [hinitial _ hi]
    rfl
  rw [he, storedByte_eq_extract, Incremental.sliceLanes_extract_byte]
  by_cases hb : 8 * lane.val + j.val < bytes.size
  · simp only [Nat.zero_le, Nat.sub_zero, hb, and_self, ↓reduceDIte, ↓reduceIte,
      Array.getElem?_eq_getElem hb, Option.getD_some]
  · simp only [Nat.zero_le, Nat.sub_zero, hb, and_false, ↓reduceDIte, ↓reduceIte]

theorem Result.incremental [Bindings] {v : Variant} {pointer source completed : BitVec 64}
    {bytes : ByteArray} {initial : Nat → UInt8} {s t : RamState}
    (hc : Context v pointer source completed bytes.size initial
      (fun i ↦ (bytes.data[i]?).getD 0) s)
    (hr : Result v pointer bytes.size initial (fun i ↦ (bytes.data[i]?).getD 0) s t) :
    Permutation.memoryLanes pointer t =
        (Incremental.update Keccak.keccakLanes v.rate
          ⟨Permutation.memoryLanes pointer s, 0⟩ bytes).lanes ∧
      (Operand.reg 1 : Operand 64).read t =
        BitVec.ofNat 64 (Incremental.update Keccak.keccakLanes v.rate
          ⟨Permutation.memoryLanes pointer s, 0⟩ bytes).cursor := by
  rw [Incremental.update_lt _ _ _ _ (by simpa only [Nat.zero_add] using hc.remaining_lt)]
  exact ⟨memoryLanes_xor_slice pointer bytes initial hc.stateBytes hr.stateBytes,
    by simpa only [Nat.zero_add] using hr.remainingReg⟩

end Sha3.Proofs.Update.Tail
