import K256.Proofs.Generate.Generator.Multiply.Split.WideProduct

namespace K256.Proofs.Generate.Generator.Multiply.Split.Reduction

open Standards.SECG.DomainParameters.Secp256k1

abbrev complement : Nat := 0x14551231950b75fc4402da1732fc9bebf

def foldHigh (v : Nat) : Nat := v % 2^256 + complement * (v / 2^256)

theorem foldHigh_split (lo hi : Nat) (bound : lo < 2^256) :
    foldHigh (lo + 2^256 * hi) = lo + complement * hi := by
  unfold foldHigh
  congr 1
  · omega
  · congr 1 <;> omega

theorem foldHigh_mod (v : Nat) : foldHigh v % domain.n = v % domain.n := by
  have h : foldHigh v + domain.n * (v / 2^256) = v := by
    have hd := Nat.mod_add_div v (2^256)
    unfold foldHigh
    change _ + 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141 * _ = _
    unfold complement
    omega
  calc
    _ = (foldHigh v + domain.n * (v / 2^256)) % domain.n := by simp
    _ = _ := congrArg (· % domain.n) h

theorem threeFolds_lt {v : Nat} (bound : v < 2^512) :
    foldHigh (foldHigh (foldHigh v)) < 2 * domain.n := by
  have bound₁ : foldHigh v < 2^256 * (complement+1) := by
    rw [foldHigh]
    unfold complement
    omega
  have bound₂ : foldHigh (foldHigh v) < 3*2^256 := by
    rw [foldHigh]
    unfold complement at bound₁ ⊢
    omega
  change foldHigh (foldHigh v) % 2^256 + complement * (foldHigh (foldHigh v) / 2^256) <
    2 * 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141
  unfold complement
  omega

theorem selectResidue {v lo diff borrow high : Nat}
    (loBound : lo < 2^256) (diffBound : diff < 2^256)
    (borrowBit : borrow ≤ 1) (sub : diff + domain.n = lo + 2^256 * borrow)
    (folded : lo + 2^256 * high = foldHigh (foldHigh (foldHigh v))) (bound : v < 2^512) :
    (if borrow = 0 ∨ high ≠ 0 then diff else lo) = v % domain.n := by
  have small := threeFolds_lt bound
  rw [← foldHigh_mod v, ← foldHigh_mod (foldHigh v), ← foldHigh_mod (foldHigh (foldHigh v)), ← folded]
  rw [← folded] at small
  have modulus : domain.n = 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141 := rfl
  rw [modulus] at sub small ⊢
  split
  · rename_i h
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [Nat.mod_eq_of_lt (by omega)]
    omega

end K256.Proofs.Generate.Generator.Multiply.Split.Reduction
