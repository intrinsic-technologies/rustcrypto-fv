import Sha3.Proofs.Update.Partial.Context

namespace Sha3.Proofs.Update.Partial

open X86 X86.Machine X86.UserProcess X86Proofs Sha3.Spec.Program

theorem memoryLanes_xor_of_frame {s t : RamState} {pointer : BitVec 64}
    {position : Nat} {initial : Nat → UInt8} (bytes : ByteArray)
    (hposition : position ≤ 200)
    (hinitial : Bytes s.external pointer 200 initial)
    (hbytes : Bytes t.external (destination pointer position) (200 - position)
      (fun i ↦ initial (position + i) ^^^
        (if i < bytes.size then (bytes.data[i]?).getD 0 else 0)))
    (hframe : AgreesExcept (clobbers pointer position) s t) :
    Permutation.memoryLanes pointer t = fun lane ↦
      Permutation.memoryLanes pointer s lane ^^^ Incremental.sliceLanes position bytes lane := by
  have hpatch := bytes_patch_suffix_of_agreesExcept hposition (by decide : 200 ≤ 2 ^ 64)
    hinitial hbytes hframe (by
      intro c hc address hcover
      simp only [clobbers, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals try exact hcover.elim
      exact hcover)
  apply memoryLanes_xor_slice _ position bytes initial _
    (bytes_xor_slice_of_patch bytes hpatch)
  intro lane j
  rw [LaneMemory.storedByte_memoryLanes]
  change _ = (s.external[pointer + BitVec.ofNat 64 (8 * lane.val + j.val)]?).getD 0
  rw [hinitial _ (by omega)]
  rfl

theorem ShortResult.incremental [Bindings] {v : Variant} {pointer : BitVec 64}
    {position : Nat} {bytes : ByteArray} {initial : Nat → UInt8} {s t : RamState}
    (hinitial : Bytes s.external pointer 200 initial)
    (hposition : position ≤ 200) (hcount : position + bytes.size < v.rate)
    (hr : ShortResult v pointer position bytes.size (fun i ↦ initial (position + i))
      (fun i ↦ (bytes.data[i]?).getD 0) s t) :
    Permutation.memoryLanes pointer t =
        (Incremental.update Keccak.keccakLanes v.rate
          ⟨Permutation.memoryLanes pointer s, position⟩ bytes).lanes ∧
      (Operand.reg 1 : Operand 64).read t =
        BitVec.ofNat 64 (Incremental.update Keccak.keccakLanes v.rate
          ⟨Permutation.memoryLanes pointer s, position⟩ bytes).cursor := by
  rw [Incremental.update_lt _ _ _ _ hcount]
  exact ⟨memoryLanes_xor_of_frame bytes hposition hinitial hr.stateBytes hr.frame,
    hr.cursorReg⟩

theorem FillResult.lanes [Bindings] {v : Variant} {pointer source : BitVec 64}
    {position count : Nat} {bytes : ByteArray} {initial : Nat → UInt8} {s t : RamState}
    (hinitial : Bytes s.external pointer 200 initial)
    (hposition : position ≤ 200) (hcount : count ≤ bytes.size)
    (hr : FillResult v pointer source position count (fun i ↦ initial (position + i))
      (fun i ↦ (bytes.data[i]?).getD 0) s t) :
    Permutation.memoryLanes pointer t = fun lane ↦
      Permutation.memoryLanes pointer s lane ^^^
        Incremental.sliceLanes position (bytes.extract 0 count) lane := by
  apply memoryLanes_xor_of_frame (bytes.extract 0 count) hposition hinitial _ hr.frame
  apply hr.stateBytes.congr
  intro i _
  simp only [ByteArray.size_extract, Nat.min_eq_left hcount, Nat.sub_zero]
  by_cases hi : i < count
  · have hib : i < bytes.size := by omega
    have hit : i < (bytes.extract 0 count).size := by
      simpa only [ByteArray.size_extract, Nat.min_eq_left hcount, Nat.sub_zero] using hi
    simp only [hi, ↓reduceIte]
    have he : (bytes.extract 0 count).data[i]? = bytes.data[i]? := by
      rw [Array.getElem?_eq_getElem (xs := (bytes.extract 0 count).data) hit,
        Array.getElem?_eq_getElem (xs := bytes.data) hib]
      congr 1
      change (bytes.extract 0 count)[i] = bytes[i]
      simp only [ByteArray.getElem_extract, Nat.zero_add]
    rw [he]
  · simp only [hi, ↓reduceIte]

end Sha3.Proofs.Update.Partial
