import AesGcm.Proofs.Machine.Fixslice.Sbox
import AesGcm.Proofs.Machine.Fixslice16.Representation

namespace AesGcm.Proofs.Machine.Fixslice16

open AesGcm.Proofs.Machine.Fixslice (subBytesCircuit invSubBytesCircuit
  subBytesByte subBytesByte_eq invSubBytesByte invSubBytesByte_eq getLsbD_fromBits)

local instance : HXor Bool Bool Bool := ⟨Bool.xor⟩
local instance : HAnd Bool Bool Bool := ⟨Bool.and⟩

theorem getLsbD_subBytesCircuit {w : Nat} (x : Fin 8 → BitVec w) (p : Fin 8) (i : Nat) :
    (subBytesCircuit x p).getLsbD i =
      subBytesCircuit (fun q ↦ (x q).getLsbD i) p := by
  rcases p with ⟨p, hp⟩
  have h : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 7 := by omega
  rcases h with h | h | h | h | h | h | h | h <;> subst p <;>
    (simp only [subBytesCircuit, BitVec.getLsbD_xor, BitVec.getLsbD_and]; rfl)

theorem getLsbD_invSubBytesCircuit {w : Nat} (x : Fin 8 → BitVec w) (p : Fin 8) (i : Nat) :
    (invSubBytesCircuit x p).getLsbD i =
      invSubBytesCircuit (fun q ↦ (x q).getLsbD i) p := by
  rcases p with ⟨p, hp⟩
  have h : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 7 := by omega
  rcases h with h | h | h | h | h | h | h | h <;> subst p <;>
    (simp only [invSubBytesCircuit, BitVec.getLsbD_xor, BitVec.getLsbD_and]; rfl)

theorem setWidth_subBytesCircuit {m n : Nat} (x : Fin 8 → BitVec m) (p : Fin 8) :
    (subBytesCircuit x p).setWidth n =
      subBytesCircuit (fun q ↦ (x q).setWidth n) p := by
  rcases p with ⟨p, hp⟩
  have h : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 7 := by omega
  rcases h with h | h | h | h | h | h | h | h <;> subst p <;>
    (simp only [subBytesCircuit, BitVec.setWidth_xor, BitVec.setWidth_and])

theorem setWidth_invSubBytesCircuit {m n : Nat} (x : Fin 8 → BitVec m) (p : Fin 8) :
    (invSubBytesCircuit x p).setWidth n =
      invSubBytesCircuit (fun q ↦ (x q).setWidth n) p := by
  rcases p with ⟨p, hp⟩
  have h : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 7 := by omega
  rcases h with h | h | h | h | h | h | h | h <;> subst p <;>
    (simp only [invSubBytesCircuit, BitVec.setWidth_xor, BitVec.setWidth_and])

def subBytes (x : Planes16) : Planes16 := subBytesCircuit x

def invSubBytes (x : Planes16) : Planes16 := invSubBytesCircuit x

def subBytesNots (x : Planes16) : Planes16 := fun p ↦
  if p.val = 0 ∨ p.val = 1 ∨ p.val = 5 ∨ p.val = 6 then ~~~x p else x p

theorem subBytes_encode (x : Block) :
    subBytes (encode x) = encode (fun j ↦
      (Standards.NIST.AES.sbox (UInt8.ofBitVec (x j))).toBitVec ^^^ 0x63) := by
  funext p
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [subBytes, getLsbD_subBytesCircuit, getLsbD_encode _ _ ⟨i, hi⟩]
  simp only [getLsbD_encode _ _ (⟨i, hi⟩ : Fin 16)]
  have hb := congrArg (fun b ↦ b.getLsbD p.val)
    (subBytesByte_eq (x (transposeIndex ⟨i, hi⟩)))
  simpa only [subBytesByte, getLsbD_fromBits] using hb

theorem invSubBytes_encode (x : Block) :
    invSubBytes (encode x) = encode (fun j ↦
      (Standards.NIST.AES.invSbox (UInt8.ofBitVec (x j ^^^ 0x63))).toBitVec) := by
  funext p
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [invSubBytes, getLsbD_invSubBytesCircuit, getLsbD_encode _ _ ⟨i, hi⟩]
  simp only [getLsbD_encode _ _ (⟨i, hi⟩ : Fin 16)]
  have hb := congrArg (fun b ↦ b.getLsbD p.val)
    (invSubBytesByte_eq (x (transposeIndex ⟨i, hi⟩)))
  simpa only [invSubBytesByte, getLsbD_fromBits] using hb

theorem subBytesNots_involutive (x : Planes16) : subBytesNots (subBytesNots x) = x := by
  funext p
  simp only [subBytesNots]
  split <;> simp_all only [BitVec.not_not]

theorem getLsbD_subBytesNots (x : Planes16) (p : Fin 8) (i : Fin 16) :
    (subBytesNots x p).getLsbD i.val =
      if p.val = 0 ∨ p.val = 1 ∨ p.val = 5 ∨ p.val = 6
      then !(x p).getLsbD i.val else (x p).getLsbD i.val := by
  simp only [subBytesNots]
  split <;> simp only [BitVec.getLsbD_not, i.isLt, decide_true, Bool.true_and]

theorem subBytesNots_encode (x : Block) :
    subBytesNots (encode x) = encode (fun j ↦ x j ^^^ 0x63) := by
  funext p
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [show i = (⟨i, hi⟩ : Fin 16).val from rfl, getLsbD_subBytesNots,
    getLsbD_encode, getLsbD_encode, BitVec.getLsbD_xor]
  have h : ∀ p : Fin 8, (0x63 : BitVec 8).getLsbD p.val =
      decide (p.val = 0 ∨ p.val = 1 ∨ p.val = 5 ∨ p.val = 6) := by decide +kernel
  rw [h]
  split <;> simp_all

theorem subBytesNots_subBytes_encode (x : Block) :
    subBytesNots (subBytes (encode x)) = encode (fun j ↦
      (Standards.NIST.AES.sbox (UInt8.ofBitVec (x j))).toBitVec) := by
  rw [subBytes_encode, subBytesNots_encode]
  apply congrArg encode
  funext j
  simp only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem invSubBytes_subBytesNots_encode (x : Block) :
    invSubBytes (subBytesNots (encode x)) = encode (fun j ↦
      (Standards.NIST.AES.invSbox (UInt8.ofBitVec (x j))).toBitVec) := by
  rw [subBytesNots_encode, invSubBytes_encode]
  apply congrArg encode
  funext j
  simp only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem decode_subBytes (x : Planes16) :
    decode (subBytes x) = fun j ↦
      (Standards.NIST.AES.sbox (UInt8.ofBitVec (decode x j))).toBitVec ^^^ 0x63 := by
  have h := congrArg decode (subBytes_encode (decode x))
  simpa only [encode_decode, decode_encode] using h

theorem decode_subBytesNots_subBytes (x : Planes16) :
    decode (subBytesNots (subBytes x)) = fun j ↦
      (Standards.NIST.AES.sbox (UInt8.ofBitVec (decode x j))).toBitVec := by
  have h := congrArg decode (subBytesNots_subBytes_encode (decode x))
  simpa only [encode_decode, decode_encode] using h

end AesGcm.Proofs.Machine.Fixslice16
