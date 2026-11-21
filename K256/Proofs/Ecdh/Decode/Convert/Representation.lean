import K256.Proofs.Ecdh.Decode.Convert.State
import K256.Proofs.Ecdh.Decode.Repr
import K256.Proofs.Generate.Generator.Multiply.Constants

namespace K256.Proofs.Ecdh.Decode.Convert

open X86.Machine X86Proofs K256.Proofs.Refine K256.Proofs.Common.Field
open Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1 Generate.Generator.Affine
open Generate.Generator.Multiply
open Fin.NatCast

local instance : NeZero modulus := ⟨by decide⟩

theorem flag_cases {fr : Activation} {pt : Curve.Point}
    (h : AffinePointAt fr.original fr.rsi pt) : inputFlag fr = 0 ∨ inputFlag fr = 1 := by
  cases pt with
  | infinity => exact Or.inr h
  | affine x y =>
    obtain ⟨_, _, _, _, _, _, _, _, flag, _⟩ := h
    exact Or.inl flag

private theorem shiftAddr (base : Word) (n i : Nat) :
    wordAddr (base + BitVec.ofNat 64 (8*n)) 64 i = wordAddr base 64 (n+i) := by
  simp only [wordAddr, Nat.reduceDiv, Nat.mul_add, BitVec.ofNat_add, BitVec.add_assoc]

private theorem constantRepr (k : Fin 2) :
    FieldRepr (#v[BitVec.ofNat 64 k.val,0,0,0,0]) ⟨k.val, by have := k.isLt; exact Nat.lt_trans this (by decide)⟩ 1 := by
  have hk := k.isLt
  have cases : k = 0 ∨ k = 1 := by
    have : k.val = 0 ∨ k.val = 1 := by omega
    exact this.imp Fin.ext Fin.ext
  rcases cases with rfl|rfl <;> unfold FieldRepr <;> decide +kernel

theorem storedPoint {fr : Activation} {pt : Curve.Point} {m : Ram}
    (h : AffinePointAt fr.original fr.rsi pt)
    (onCurve : Curve.onCurve domain pt = true)
    (words : ∀ i < 15, memLoad m (wordAddr fr.rdi 64 i) 64 = outputWord fr i) :
    ∃ peer : Projective, peer.Stored m fr.rdi ∧ peer.valid ∧ peer.value = pt := by
  have constWords (n : Nat) (k : Fin 2)
      (block : ∀ i < 5, outputWord fr (n+i) = if i = 0 then BitVec.ofNat 64 k.val else 0)
      (bound : n + 5 ≤ 15) :
      WordsAt m (fr.rdi + BitVec.ofNat 64 (8*n)) 64 #v[BitVec.ofNat 64 k.val,0,0,0,0] := by
    intro i hi
    rw [shiftAddr, words (n+i) (by omega), block i hi]
    have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    rcases this with rfl|rfl|rfl|rfl|rfl <;> rfl
  cases pt with
  | infinity =>
    have flag : inputFlag fr = 1 := h
    have atZero := constWords 0 0 (fun i hi => by simp [outputWord, flag, show i ≠ 5 by omega]) (by decide)
    refine ⟨identity, ⟨_, _, _, ?_, ?_, ?_, constantRepr 0, constantRepr 1, constantRepr 0⟩, identity_valid, identity_value⟩
    · simpa using atZero
    · exact constWords 5 1 (fun i _ => by simp [outputWord, flag]) (by decide)
    · exact constWords 10 0 (fun i _ => by simp [outputWord, flag, show 10+i ≠ 5 by omega]) (by decide)
  | affine x y =>
    obtain ⟨a,b,rfl,rfl,xl,yl,wx,wy,flag,rx,ry⟩ := h
    have f : inputFlag fr = 0 := flag
    have xcopy : WordsAt m fr.rdi 64 xl := by
      intro i hi
      rw [words i (by omega), outputWord, f, ite_eq_right (by decide), ite_eq_left (by omega)]
      exact wx i hi
    have ycopy : WordsAt m (fr.rdi + 40) 64 yl := by
      intro i hi
      change memLoad m (wordAddr (fr.rdi + BitVec.ofNat 64 (8*5)) 64 i) 64 = _
      rw [shiftAddr fr.rdi 5, words (5+i) (by omega), outputWord, f, ite_eq_right (by decide), ite_eq_left (by omega)]
      unfold inputWord
      rw [← shiftAddr fr.rsi 5]
      exact wy i hi
    refine ⟨⟨a,b,1⟩, ⟨xl,yl,_,xcopy,ycopy,?_,rx,ry,constantRepr 1⟩, ?_, ?_⟩
    · exact constWords 10 1 (fun i _ => by simp [outputWord, f, show ¬ 10+i < 10 by omega]) (by decide)
    · have eq := Generate.Curve.Group.encode_onCurve _ onCurve
      change (b.val : Fin modulus) * (b.val : Fin modulus) =
        (a.val : Fin modulus) * (a.val : Fin modulus) * (a.val : Fin modulus) +
        0 * (a.val : Fin modulus) + 7 at eq
      have castId (t : Fin modulus) : (t.val : Fin modulus) = t := Fin.ext (Nat.mod_eq_of_lt t.isLt)
      simp only [castId, Fin.zero_mul, Fin.add_zero] at eq
      refine ⟨?_, Or.inr (Or.inr (show (1 : Fin modulus) ≠ 0 by decide))⟩
      change b * b * 1 = a * a * a + (7 : Fin modulus) * 1 * 1 * 1
      simpa only [Fin.mul_one] using eq
    · change toAffine a b 1 = _
      have inv : inverse (1 : Fin modulus) = 1 := by
        apply Fin.ext
        change Curve.inverse modulus 1 = 1
        rw [Curve.inverse, PowMod.powMod_eq_pow_mod, Nat.one_pow, Nat.mod_eq_of_lt (by decide)]
      rw [toAffine, ite_eq_right (by decide), inv]
      simp only [Fin.mul_one]

end K256.Proofs.Ecdh.Decode.Convert
