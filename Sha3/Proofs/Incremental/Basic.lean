import Sha3.Proofs.Incremental.State

namespace Sha3.Proofs.Incremental

open Keccak Absorption

theorem update_empty (permute : Lanes → Lanes) (rate : Nat) (state : State) :
    update permute rate state ByteArray.empty = state := rfl

theorem update_append (permute : Lanes → Lanes) (rate : Nat) (state : State)
    (left right : ByteArray) :
    update permute rate state (left ++ right) =
      update permute rate (update permute rate state left) right := by
  simp only [update, ByteArray.data_append, Array.foldl_append]

theorem update_push (permute : Lanes → Lanes) (rate : Nat) (state : State)
    (bytes : ByteArray) (byte : UInt8) :
    update permute rate state (bytes.push byte) =
      absorbByte permute rate (update permute rate state bytes) byte := by
  simp only [update, ByteArray.data_push, Array.foldl_push]

theorem absorbByte_cursor_lt (permute : Lanes → Lanes) (rate : Nat) (hr : 0 < rate)
    (state : State) (hc : state.cursor < rate) (byte : UInt8) :
    (absorbByte permute rate state byte).cursor < rate := by
  unfold absorbByte
  split <;> dsimp only <;> omega

theorem update_cursor_lt (permute : Lanes → Lanes) (rate : Nat) (hr : 0 < rate)
    (state : State) (hc : state.cursor < rate) (bytes : ByteArray) :
    (update permute rate state bytes).cursor < rate := by
  exact Array.foldl_induction (motive := fun _ s ↦ s.cursor < rate) hc
    (fun _ s h ↦ absorbByte_cursor_lt permute rate hr s h _)

theorem getLsbD_byteLanes (position : Nat) (byte : UInt8) (lane : Fin 25)
    (z : Fin 64) :
    (byteLanes position byte lane).getLsbD z.val =
      if 8 * lane.val + z.val / 8 = position then
        byte.toBitVec.getLsbD (z.val % 8)
      else false := by
  exact getLsbD_packLane _ z

theorem byteLanes_extract_byte (position : Nat) (byte : UInt8) (lane : Fin 25)
    (j : Fin 8) :
    UInt8.ofBitVec ((byteLanes position byte lane).extractLsb' (8 * j.val) 8) =
      if 8 * lane.val + j.val = position then byte else 0 := by
  apply UInt8.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro z hz
  simp only [BitVec.getLsbD_extractLsb', hz, decide_true,
    Bool.true_and, getLsbD_byteLanes position byte lane ⟨8 * j.val + z, by omega⟩]
  have hdiv : (8 * j.val + z) / 8 = j.val := by omega
  have hmod : (8 * j.val + z) % 8 = z := by omega
  simp only [hdiv, hmod]
  split <;> simp_all

end Sha3.Proofs.Incremental
