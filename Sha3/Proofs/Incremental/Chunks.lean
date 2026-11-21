import Sha3.Proofs.Incremental.Basic

namespace Sha3.Proofs.Incremental

open Keccak Absorption

def sliceLanes (position : Nat) (bytes : ByteArray) : Lanes := fun lane ↦
  packLane fun z ↦
    let j := 8 * lane.val + z.val / 8
    if h : position ≤ j ∧ j - position < bytes.size then
      (bytes.data[j - position]'h.2).toBitVec.getLsbD (z.val % 8)
    else false

theorem getLsbD_sliceLanes (position : Nat) (bytes : ByteArray) (lane : Fin 25)
    (z : Fin 64) :
    (sliceLanes position bytes lane).getLsbD z.val =
      if h : position ≤ 8 * lane.val + z.val / 8 ∧
          8 * lane.val + z.val / 8 - position < bytes.size then
        (bytes.data[8 * lane.val + z.val / 8 - position]'h.2).toBitVec.getLsbD
          (z.val % 8)
      else false := by
  exact getLsbD_packLane _ z

theorem sliceLanes_empty (position : Nat) :
    sliceLanes position ByteArray.empty = fun _ ↦ 0#64 := by
  funext lane
  apply BitVec.eq_of_getLsbD_eq
  intro z hz
  simp [getLsbD_sliceLanes position ByteArray.empty lane ⟨z, hz⟩]

theorem sliceLanes_extract_byte (position : Nat) (bytes : ByteArray) (lane : Fin 25)
    (j : Fin 8) :
    UInt8.ofBitVec ((sliceLanes position bytes lane).extractLsb' (8 * j.val) 8) =
      if h : position ≤ 8 * lane.val + j.val ∧
          8 * lane.val + j.val - position < bytes.size then
        bytes.data[8 * lane.val + j.val - position]'h.2
      else 0 := by
  apply UInt8.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro z hz
  simp only [BitVec.getLsbD_extractLsb', hz, decide_true, Bool.true_and,
    getLsbD_sliceLanes position bytes lane ⟨8 * j.val + z, by omega⟩]
  have hdiv : (8 * j.val + z) / 8 = j.val := by omega
  have hmod : (8 * j.val + z) % 8 = z := by omega
  simp only [hdiv, hmod]
  split <;> simp_all

theorem sliceLanes_push (position : Nat) (bytes : ByteArray) (byte : UInt8) :
    sliceLanes position (bytes.push byte) =
      fun lane ↦ sliceLanes position bytes lane ^^^
        byteLanes (position + bytes.size) byte lane := by
  funext lane
  apply BitVec.eq_of_getLsbD_eq
  intro z hz
  simp only [BitVec.getLsbD_xor, getLsbD_sliceLanes _ _ _ ⟨z, hz⟩,
    getLsbD_byteLanes _ _ _ ⟨z, hz⟩, ByteArray.size_push]
  by_cases hpos : position ≤ 8 * lane.val + z / 8
  · by_cases hlt : 8 * lane.val + z / 8 - position < bytes.size
    · have hlt' : 8 * lane.val + z / 8 - position < bytes.size + 1 := by omega
      have hne : ¬8 * lane.val + z / 8 = position + bytes.size := by omega
      simp only [hpos, hlt, hlt', and_self, ↓reduceDIte, hne, ↓reduceIte,
        ByteArray.data_push, Array.getElem_push_lt hlt, Bool.xor_false]
    · by_cases heq : 8 * lane.val + z / 8 = position + bytes.size
      · have hindex : 8 * lane.val + z / 8 - position = bytes.size := by omega
        have hlt' : 8 * lane.val + z / 8 - position < bytes.size + 1 := by omega
        have hnot : ¬(position ≤ 8 * lane.val + z / 8 ∧
            8 * lane.val + z / 8 - position < bytes.size) := by omega
        simp only [dite_eq_left (And.intro hpos hlt'), dite_eq_right hnot, ite_eq_left heq,
          Bool.false_xor, ByteArray.data_push]
        simpa only [hindex, ByteArray.size_data] using
          congrArg (fun b : UInt8 ↦ b.toBitVec.getLsbD (z % 8))
            (Array.getElem_push_eq (xs := bytes.data) (x := byte))
      · have hlt' : ¬8 * lane.val + z / 8 - position < bytes.size + 1 := by omega
        simp [hlt, hlt', heq]
  · have hne : ¬8 * lane.val + z / 8 = position + bytes.size := by omega
    simp [hpos, hne]

theorem sliceLanes_zero_eq_blockLanes (bytes : ByteArray) (rate : Nat)
    (h : bytes.size = rate) : sliceLanes 0 bytes = blockLanes bytes 0 rate := by
  funext lane
  apply BitVec.eq_of_getLsbD_eq
  intro z hz
  simp [sliceLanes, blockLanes, getLsbD_packLane _ ⟨z, hz⟩, h]

private theorem byteArray_push_induction (motive : ByteArray → Prop)
    (empty : motive ByteArray.empty)
    (push : ∀ bytes byte, motive bytes → motive (bytes.push byte))
    (bytes : ByteArray) : motive bytes := by
  have hreverse : ∀ values : List UInt8, motive ⟨values.reverse.toArray⟩ := by
    intro values
    induction values with
    | nil => exact empty
    | cons byte values ih =>
      have heq : ByteArray.mk (byte :: values).reverse.toArray =
          (ByteArray.mk values.reverse.toArray).push byte := by
        apply ByteArray.ext
        simp [ByteArray.data_push]
      rw [heq]
      exact push _ _ ih
  cases bytes with
  | mk data => simpa using hreverse data.toList.reverse

theorem update_lt (permute : Lanes → Lanes) (rate : Nat) (state : State)
    (bytes : ByteArray) (h : state.cursor + bytes.size < rate) :
    update permute rate state bytes =
      ⟨fun lane ↦ state.lanes lane ^^^ sliceLanes state.cursor bytes lane,
        state.cursor + bytes.size⟩ := by
  induction bytes using byteArray_push_induction with
  | empty =>
    simp only [update_empty, sliceLanes_empty, BitVec.xor_zero, ByteArray.size_empty,
      Nat.add_zero]
  | push bytes byte ih =>
    have hlt : state.cursor + bytes.size < rate := by
      rw [ByteArray.size_push] at h
      omega
    have hne : ¬state.cursor + (bytes.size + 1) = rate := by
      rw [ByteArray.size_push] at h
      omega
    rw [update_push, ih hlt]
    simp only [absorbByte, hne, ↓reduceIte, sliceLanes_push, BitVec.xor_assoc,
      ByteArray.size_push, Nat.add_assoc]

theorem update_eq_rate (permute : Lanes → Lanes) (rate : Nat) (state : State)
    (bytes : ByteArray) (hc : state.cursor < rate) (h : state.cursor + bytes.size = rate) :
    update permute rate state bytes =
      ⟨permute (fun lane ↦ state.lanes lane ^^^ sliceLanes state.cursor bytes lane), 0⟩ := by
  induction bytes using byteArray_push_induction with
  | empty => simp only [ByteArray.size_empty, Nat.add_zero] at h; omega
  | push bytes byte _ =>
    have hlt : state.cursor + bytes.size < rate := by
      rw [ByteArray.size_push] at h
      omega
    have heq : state.cursor + bytes.size + 1 = rate := by
      rw [ByteArray.size_push] at h
      omega
    rw [update_push, update_lt permute rate state bytes hlt]
    simp only [absorbByte, heq, ↓reduceIte, sliceLanes_push, BitVec.xor_assoc]

theorem update_block (permute : Lanes → Lanes) (rate : Nat) (lanes : Lanes)
    (bytes : ByteArray) (hr : 0 < rate) (h : bytes.size = rate) :
    update permute rate ⟨lanes, 0⟩ bytes =
      ⟨permute (fun lane ↦ lanes lane ^^^ blockLanes bytes 0 rate lane), 0⟩ := by
  simpa only [sliceLanes_zero_eq_blockLanes bytes rate h] using
    update_eq_rate permute rate ⟨lanes, 0⟩ bytes hr (by simpa using h)

end Sha3.Proofs.Incremental
