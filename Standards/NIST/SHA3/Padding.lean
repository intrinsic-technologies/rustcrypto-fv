import Standards.NIST.SHA3.Sponge

/-!
# Multi-rate padding

The pad10*1 padding rule of the KECCAK sponge functions, from FIPS 202, §5.1.

Source: https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.202.pdf
-/

namespace Standards.NIST.SHA3

/--
pad10*1 (FIPS 202, §5.1, Algorithm 9)

Input: positive block length `x` and nonnegative message length `m`
Output: padding string `P` such that `m + len(P)` is a positive multiple of `x`

1. Set `j = (−m−2) mod x`
2. Return `P = 1 || 0^j || 1`
-/
def pad101 : PaddingRule where
  pad x m :=
    let j := ((-(m : Int) - 2) % (x : Int)).toNat
    #[true] ++ Array.replicate j false ++ #[true]
  valid x m hx := by
    simp only [Array.size_append, Array.size_replicate, Array.size_singleton]
    constructor
    · omega
    · have hnonneg : 0 ≤ (-(m : Int) - 2) % (x : Int) :=
        Int.emod_nonneg _ (by omega)
      have hmod : ((m : Int) + 2 + ((-(m : Int) - 2) % (x : Int))) % (x : Int) = 0 := by
        rw [Int.add_emod_emod]
        have hsum : (m : Int) + 2 + (-(m : Int) - 2) = 0 := by omega
        rw [hsum, Int.zero_emod]
      apply Int.ofNat_inj.mp
      simp only [Int.natCast_emod, Int.natCast_add, Int.natCast_one, Int.natCast_zero,
        Int.toNat_of_nonneg hnonneg]
      have hsum : (m : Int) + (1 + (-(m : Int) - 2) % (x : Int) + 1) =
          (m : Int) + 2 + (-(m : Int) - 2) % (x : Int) := by omega
      rw [hsum]
      exact hmod

end Standards.NIST.SHA3
