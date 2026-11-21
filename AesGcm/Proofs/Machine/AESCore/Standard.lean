import AesGcm.Proofs.Machine.Fixslice.Operations
import Standards.NIST.AES.Cipher

namespace AesGcm.Proofs.Machine.AESCore

open Standards.NIST.AES AesGcm.Proofs.Machine.Fixslice

abbrev RoundKey := Vector (Vector UInt8 4) 4

def encryptRound (keys : Nat → RoundKey) (round : Nat) (state : StandardBlocks) :
    StandardBlocks := fun b ↦
  addRoundKey (mixColumns (shiftRows (Standards.NIST.AES.subBytes (state b)))) (keys round)

def encryptRounds (keys : Nat → RoundKey) (count : Nat) (input : StandardBlocks) :
    StandardBlocks :=
  (List.range count).foldl (fun state j ↦ encryptRound keys (j + 1) state)
    (fun b ↦ addRoundKey (input b) (keys 0))

def encryptLast (keys : Nat → RoundKey) (nr : Nat) (state : StandardBlocks) :
    StandardBlocks := fun b ↦
  addRoundKey (shiftRows (Standards.NIST.AES.subBytes (state b))) (keys nr)

theorem encryptRounds_zero (keys : Nat → RoundKey) (input : StandardBlocks) :
    encryptRounds keys 0 input = fun b ↦ addRoundKey (input b) (keys 0) := rfl

theorem encryptRounds_succ (keys : Nat → RoundKey) (count : Nat) (input : StandardBlocks) :
    encryptRounds keys (count + 1) input =
      encryptRound keys (count + 1) (encryptRounds keys count input) := by
  simp only [encryptRounds, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem encryptRounds_apply (keys : Nat → RoundKey) (count : Nat) (input : StandardBlocks)
    (b : Fin 4) :
    encryptRounds keys count input b =
      (List.range count).foldl (fun state j ↦
        addRoundKey (mixColumns (shiftRows (Standards.NIST.AES.subBytes state))) (keys (j + 1)))
        (addRoundKey (input b) (keys 0)) :=
  (List.foldl_hom (fun state : StandardBlocks ↦ state b) (by intros; rfl)).symm

def cipherKeys (v : Variant) (key : Vector UInt8 v.keyBytes) (round : Nat) : RoundKey :=
  roundKey v (keyExpansion v key) ⟨min round v.Nr, by omega⟩

theorem encryptRounds_correct (v : Variant) (key : Vector UInt8 v.keyBytes)
    (input : StandardBlocks) :
    encryptLast (cipherKeys v key) v.Nr
      (encryptRounds (cipherKeys v key) (v.Nr - 1) input) = fun b ↦ cipher v key (input b) := by
  funext b
  simp only [encryptLast, encryptRounds_apply, cipherKeys, cipher]


end AesGcm.Proofs.Machine.AESCore
