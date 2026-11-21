import K256.Proofs.Sec1.Affine.Compressed.Contract
import K256.Proofs.Common.Field.Decompress

namespace K256.Proofs.Sec1.Affine.Compressed

open K256.Proofs.Common K256.Proofs.Common.Field Standards.SECG.ECC

def Inputs.coordinate (v : Inputs) : Fin modulus := ⟨v.x % modulus, Nat.mod_lt _ (by decide)⟩

def Inputs.radicand (v : Inputs) : Fin modulus :=
  let x := limbValue v.masked
  ⟨(x * x * x + 7) % modulus, Nat.mod_lt _ (by decide)⟩

def Inputs.root (v : Inputs) : Fin modulus :=
  ⟨SqrtChain.result SqrtChain.modSq SqrtChain.modMul v.radicand.val SqrtChain.chain,
    by rw [SqrtChain.result_sqrt]; exact Nat.mod_lt _ (by decide)⟩

def Inputs.sqrtOK (v : Inputs) := decide (SqrtChain.modSq v.root.val = v.radicand.val)

theorem Inputs.masked_repr (v : Inputs) (h : v.valid = true) : FieldRepr v.masked v.coordinate 8 := by
  have hx : v.x < modulus := of_decide_eq_true h
  simp only [Inputs.masked, Uncompressed.CoordinateWords.masked,
      (show Uncompressed.CoordinateWords.valid v = true from h), ite_true]
  exact Uncompressed.unpack_repr v.a v.b v.c v.d v.coordinate (Nat.mod_eq_of_lt hx).symm (by decide)

private theorem root_pos_of_square {x r : Nat} (h : SqrtChain.modSq r = (x * x * x + 7) % modulus) :
    0 < r := by
  have hs : (x * x * x + 7) % modulus ≠ 0 := by
    simpa only [Arithmetic.decompressSquare, show Standards.SECG.DomainParameters.Secp256k1.domain.a = 0 from rfl,
      Nat.zero_mul, Nat.add_zero, show Standards.SECG.DomainParameters.Secp256k1.domain.b = 7 from rfl,
      modulus] using Arithmetic.decompressSquare_ne_zero x
  cases r with
  | zero => exact False.elim (hs h.symm)
  | succ _ => exact Nat.zero_lt_succ _

theorem Inputs.root_pos (v : Inputs) (h : v.sqrtOK = true) : 0 < v.root.val :=
  root_pos_of_square (x := limbValue v.masked) (r := v.root.val)
    (of_decide_eq_true (p := SqrtChain.modSq v.root.val = v.radicand.val) h)

attribute [local irreducible] SqrtChain.result

theorem Inputs.decompress (v : Inputs) (tag : UInt8) (want : BitVec 8)
    (parity : want.toNat = tag.toNat % 2) :
    Sec1.decompress tag v.x =
      if v.valid && v.sqrtOK then some (.affine v.coordinate.val (chosenY v.root want).val)
      else none := by
  rw [Field.decompress_eq]
  by_cases hx : v.x < modulus
  · have hv : v.valid = true := decide_eq_true hx
    have hrad : v.radicand.val = (v.x * v.x * v.x + 7) % modulus := by
      simp only [Inputs.radicand, Inputs.masked, Uncompressed.CoordinateWords.masked,
      (show Uncompressed.CoordinateWords.valid v = true from hv), ite_true, Inputs.x,
        Uncompressed.CoordinateWords.nat, Uncompressed.CoordinateWords.limbs]
    simp only [hx, true_and, hv, Bool.true_and, ← hrad]
    have rootEq : SqrtChain.result SqrtChain.modSq SqrtChain.modMul v.radicand.val SqrtChain.chain =
        v.root.val := by unfold Inputs.root; rfl
    simp only [rootEq]
    by_cases hs : v.root.val * v.root.val % modulus = v.radicand.val
    · have ok : v.sqrtOK = true := by unfold Inputs.sqrtOK SqrtChain.modSq; exact decide_eq_true hs
      have hpos := v.root_pos ok
      have hneg : modulus - v.root.val < modulus := by omega
      simp only [hs, ok, ite_true, Inputs.coordinate, Nat.mod_eq_of_lt hx, chosenY, parity]
      split <;> simp only [Nat.mod_eq_of_lt hneg]
    · have fail : v.sqrtOK = false := by unfold Inputs.sqrtOK SqrtChain.modSq; exact decide_eq_false hs
      simp [hs, fail]
  · have hv : v.valid = false := decide_eq_false hx
    simp [hx, hv]

end K256.Proofs.Sec1.Affine.Compressed
