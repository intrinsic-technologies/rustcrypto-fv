import Sha3.Proofs.Incremental.Basic
import Sha3.Spec.Program

namespace Sha3.Proofs.Incremental

open Keccak Sha3.Spec.Program

def updateInputs (permute : Lanes → Lanes) (rate : Nat) (state : State)
    (inputs : Array Input) : State :=
  inputs.foldl (fun s input ↦ update permute rate s input.bytes) state

theorem update_inputs (permute : Lanes → Lanes) (rate : Nat) (state : State)
    (inputs : Array Input) :
    updateInputs permute rate state inputs = update permute rate state (message inputs) := by
  exact Array.foldl_hom (fun bytes ↦ update permute rate state bytes)
    (g₁ := fun bytes input ↦ bytes ++ input.bytes) (xs := inputs) (init := ByteArray.empty)
    (g₂ := fun s input ↦ update permute rate s input.bytes)
    (fun bytes input ↦ (update_append permute rate state bytes input.bytes).symm)

theorem message_foldl (before : ByteArray) (inputs : Array Input) :
    inputs.foldl (fun bytes input ↦ bytes ++ input.bytes) before =
      before ++ message inputs := by
  simpa only [ByteArray.append_empty, message] using
    Array.foldl_hom (fun bytes ↦ before ++ bytes)
      (g₁ := fun bytes input ↦ bytes ++ input.bytes) (xs := inputs) (init := ByteArray.empty)
      (g₂ := fun bytes input ↦ bytes ++ input.bytes)
      (fun bytes input ↦ (ByteArray.append_assoc (a := before) (b := bytes)
        (c := input.bytes)))

theorem message_empty : message #[] = ByteArray.empty := rfl

theorem message_push (inputs : Array Input) (input : Input) :
    message (inputs.push input) = message inputs ++ input.bytes := by
  simp only [message, Array.foldl_push]

theorem message_append (left right : Array Input) :
    message (left ++ right) = message left ++ message right := by
  rw [message, Array.foldl_append]
  exact message_foldl (message left) right

theorem message_extract_split (inputs : Array Input) (split : Nat) :
    message inputs = message (inputs.extract 0 split) ++
      message (inputs.extract split inputs.size) := by
  rw [← message_append, Array.extract_append_extract]
  rw [Nat.zero_min, Array.extract_eq_self_of_le (Nat.le_max_right _ _)]

theorem message_extract_succ (inputs : Array Input) (start i : Nat)
    (hs : start ≤ i) (hi : i < inputs.size) :
    message (inputs.extract start (i + 1)) =
      message (inputs.extract start i) ++ inputs[i].bytes := by
  rw [Array.extract_succ_right (by omega) hi, message_push]

theorem updateInputs_empty (permute : Lanes → Lanes) (rate : Nat) (state : State) :
    updateInputs permute rate state #[] = state := rfl

theorem updateInputs_push (permute : Lanes → Lanes) (rate : Nat) (state : State)
    (inputs : Array Input) (input : Input) :
    updateInputs permute rate state (inputs.push input) =
      update permute rate (updateInputs permute rate state inputs) input.bytes := by
  simp only [updateInputs, Array.foldl_push]

theorem updateInputs_append (permute : Lanes → Lanes) (rate : Nat) (state : State)
    (left right : Array Input) :
    updateInputs permute rate state (left ++ right) =
      updateInputs permute rate (updateInputs permute rate state left) right := by
  simp only [updateInputs, Array.foldl_append]

theorem updateInputs_extract_succ (permute : Lanes → Lanes) (rate : Nat) (state : State)
    (inputs : Array Input) (start i : Nat) (hs : start ≤ i) (hi : i < inputs.size) :
    updateInputs permute rate state (inputs.extract start (i + 1)) =
      update permute rate (updateInputs permute rate state (inputs.extract start i))
        inputs[i].bytes := by
  rw [Array.extract_succ_right (by omega) hi, updateInputs_push]

end Sha3.Proofs.Incremental
