import ChaCha20Poly1305.Spec.Program.Routine
import ChaCha20Poly1305.Proofs.Decrypt.PolyInit
import ChaCha20Poly1305.Proofs.Decrypt.PolyFinishArithmetic
import ChaCha20Poly1305.Proofs.Decrypt.MacData
import ChaCha20Poly1305.Proofs.Decrypt.Bytes

namespace ChaCha20Poly1305.Proofs.Decrypt.Poly1305
open Standards.RFC.ChaCha20Poly1305

def keyBits (key : Vector UInt8 32) : BitVec 256 := BitVec.ofNat 256 (leBytesToNum (key : ByteArray))
def rWords (key : Vector UInt8 32) : Vector (BitVec 32) 5 := Vector.ofFn (fun i => Init.limb (keyBits key) i)
def sWords (key : Vector UInt8 32) : Vector (BitVec 32) 4 :=
  Vector.ofFn (fun i => (keyBits key).extractLsb' (128+32*i.val) 32)

private theorem keyNat (key : Vector UInt8 32) : (keyBits key).toNat = leBytesToNum (key : ByteArray) := by
  have h := le_bound (key : ByteArray)
  rw [show (key : ByteArray).size = 32 from key.size_toArray] at h
  exact Nat.mod_eq_of_lt h

private theorem clamp_eq (key : Vector UInt8 32) : (Init.r (keyBits key)).toNat = rKey key := by
  let s : ByteArray := key
  have hs : s.size = 32 := key.size_toArray
  have lower := Bytes.lower s (k := 16) (by omega)
  have hl : leBytesToNum (s.extract 0 16) = leBytesToNum ⟨key.toArray.extract 0 16⟩ := by
    congr 1; apply ByteArray.ext; exact ByteArray.data_extract
  rw [hl] at lower
  simp only [Init.r,BitVec.toNat_and,keyNat,rKey,clamp]
  rw [← lower]
  change leBytesToNum s &&& 0x0ffffffc0ffffffc0ffffffc0fffffff =
    leBytesToNum s % 2^128 &&& 0x0ffffffc0ffffffc0ffffffc0fffffff
  rw [← Nat.and_two_pow_sub_one_eq_mod (leBytesToNum s) 128,Nat.and_assoc]
  rfl

private theorem rWords_eq (key : Vector UInt8 32) : Mul.asLimbs (rWords key) = splitLimbs (rKey key) := by
  have digit (i : Nat) : (Init.limb (keyBits key) i).toNat = rKey key / 2^(26*i) % B := by
    simp only [Init.limb, BitVec.toNat_and,BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow,clamp_eq]
    change (_ % 2^32 &&& 67108863) = _
    rw [Nat.and_two_pow_sub_one_eq_mod _ 26]
    exact Nat.mod_mod_of_dvd _ (by decide : 2^26 ∣ 2^32)
  simp only [Mul.asLimbs,rWords,Vector.getElem_ofFn,digit,splitLimbs,B]
  exact congrArg (fun v => Limbs.mk v _ _ _ _) (by simp)

theorem rWords_value (key : Vector UInt8 32) : (Mul.asLimbs (rWords key)).value = rKey key := by
  rw [rWords_eq,split_value]
  have h : clamp (leBytesToNum ⟨key.toArray.extract 0 16⟩) ≤ 0x0ffffffc0ffffffc0ffffffc0fffffff := Nat.and_le_right
  change clamp _ < 2^130; omega

theorem rWords_tight (key : Vector UInt8 32) : (Mul.asLimbs (rWords key)).Tight := rWords_eq key ▸ tight_split _

private theorem padBits (key : Vector UInt8 32) : (keyBits key).toNat/2^128 = padKey key := by
  let s : ByteArray := key
  have hs : s.size = 32 := key.size_toArray
  have upper := Bytes.upper s (i := 16) (by omega)
  rw [hs] at upper
  rw [keyNat]
  change leBytesToNum s/256^16 = _
  rw [upper]
  unfold padKey
  congr 1; apply ByteArray.ext; exact ByteArray.data_extract

theorem sWords_value (key : Vector UInt8 32) (acc : Vector (BitVec 32) 5) :
    Finish.padNum ⟨sWords key,acc⟩ = padKey key := by
  have h := (keyBits key).isLt
  rw [← padBits key]
  simp only [Finish.padNum,Finish.wordsNum,sWords,Vector.getElem_ofFn,BitVec.extractLsb'_toNat,
    Nat.shiftRight_eq_div_pow,Nat.reduceAdd,Nat.reduceMul,Nat.reducePow]
  omega

def zeroAcc : Vector (BitVec 32) 5 := #v[0,0,0,0,0]
def represents (ws : Vector (BitVec 32) 5) (a : Nat) :=
  (Mul.asLimbs ws).Bounded ∧ (Mul.asLimbs ws).value % modulus = a

theorem zeroRep : represents zeroAcc 0 := by
  unfold represents zeroAcc Mul.asLimbs Limbs.Bounded Limbs.value B modulus
  decide +kernel

theorem nextRep {key : Vector UInt8 32} {ws : Vector (BitVec 32) 5} {a} (h : represents ws a) (b : BitVec 128) :
    represents (Mul.output ⟨rWords key,ws,b⟩) (stepAcc (rKey key) a b.toNat) := by
  obtain ⟨bounds,hv⟩ := h
  unfold represents
  rw [Mul.output_eq bounds (rWords_tight key)]
  refine ⟨bounded_update bounds (rWords_tight key) (tight_split _),?_⟩
  rw [update_value,rWords_value,fullBlock_value _ b.isLt, ← hv]
  unfold stepAcc
  simp only [Nat.mul_mod, Nat.add_mod, Nat.mod_mod]

theorem finishRep {key : Vector UInt8 32} {ws : Vector (BitVec 32) 5} {a} (h : represents ws a) :
    Finish.tagNum ⟨sWords key,ws⟩ = (a + padKey key) % 2^128 := by
  rw [Finish.tagNum_eq h.1,h.2,sWords_value]

end ChaCha20Poly1305.Proofs.Decrypt.Poly1305
