/-!
# Sponge construction

The generic sponge construction from FIPS 202, §4, with a padding rule.

Source: https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.202.pdf
-/

namespace Standards.NIST.SHA3

/--
A padding rule extends an `m`-bit message to a positive multiple of the block length `r`
(FIPS 202, §4)
-/
structure PaddingRule where
  pad : Nat → Nat → Array Bool
  valid : ∀ r m, 0 < r →
    0 < m + (pad r m).size ∧ (m + (pad r m).size) % r = 0

/--
Sponge absorption (FIPS 202, §4, Algorithm 8, steps 1–6)

Parameters: fixed-length function `f`, padding rule `pad`, and rate `0 < r < b`
Input: complete bit string `N`
Output: final `b`-bit state `S`, ready for squeezing

1. Pad the input: `P = N || pad(r,len(N))`
2. Set the block count to `len(P)/r`
3. Set the capacity to `c = b − r`
4. Split `P` into consecutive `r`-bit blocks `P₀, ..., Pₙ₋₁`
5. Initialize the `b`-bit state `S` to zero
6. For each block in order, set `S = f(S ⊕ (Pᵢ || 0^c))`
-/
def absorb {b : Nat} (f : Vector Bool b → Vector Bool b)
    (pad : PaddingRule) (r : Nat) (hr : 0 < r ∧ r < b)
    (n : Array Bool) : Vector Bool b := Id.run do
  let p := n ++ pad.pad r n.size
  let blockCount := p.size / r
  let c := b - r
  let blocks := Vector.ofFn fun i : Fin blockCount =>
    have hblock : ((i : Nat) + 1) * r ≤ p.size :=
      Nat.le_trans (Nat.mul_le_mul_right r (by omega)) (Nat.div_mul_le_self p.size r)
    Vector.ofFn fun j : Fin r =>
      p[(i : Nat) * r + (j : Nat)]'(by
        simp only [Nat.add_mul, Nat.one_mul] at hblock
        omega)
  let mut s := Vector.replicate b false
  for block in blocks.toArray do
    let paddedBlock := (block ++ Vector.replicate c false).cast (by omega)
    s := f (s.zipWith (· ^^ ·) paddedBlock)
  return s

/--
Sponge squeezing (FIPS 202, §4, Algorithm 8, steps 7–10)

Parameters: fixed-length function `f` and rate `0 < r < b`
Input: absorbed state `S` and nonnegative output length `d`
Output: bit string `Z` of exactly `d` bits

Steps 7–10 build `Z = Trunc_r(S) || Trunc_r(f(S)) || Trunc_r(f(f(S))) || ...` and return its
first `d` bits, so bit `i` of `Z` is bit `i mod r` of `f` applied `⌊i / r⌋` times to `S`.
-/
def squeeze {b : Nat} (f : Vector Bool b → Vector Bool b)
    (r : Nat) (hr : 0 < r ∧ r < b) (s : Vector Bool b) (d : Nat) : Vector Bool d :=
  Vector.ofFn fun i => (Nat.repeat f (i / r) s)[i % r]'(by have := Nat.mod_lt i hr.1; omega)

/--
Sponge construction (FIPS 202, §4, Algorithm 8)

Parameters: fixed-length function `f`, padding rule `pad`, and rate `0 < r < b`
Input: bit string `N` and nonnegative output length `d`
Output: bit string `Z` of exactly `d` bits

1. Pad the input: `P = N || pad(r,len(N))`
2. Set the block count to `len(P)/r`
3. Set the capacity to `c = b − r`
4. Split `P` into consecutive `r`-bit blocks `P₀, ..., Pₙ₋₁`
5. Initialize the `b`-bit state `S` to zero
6. For each block in order, set `S = f(S ⊕ (Pᵢ || 0^c))`
7. Initialize `Z` to the empty string
8. Append the first `r` state bits: `Z = Z || Trunc_r(S)`
9. If `d ≤ len(Z)`, return `Trunc_d(Z)`
10. Otherwise, set `S = f(S)` and continue at step 8

`absorb` implements steps 1–6 and `squeeze` steps 7–10.
-/
def sponge {b : Nat} (f : Vector Bool b → Vector Bool b)
    (pad : PaddingRule) (r : Nat) (hr : 0 < r ∧ r < b)
    (n : Array Bool) (d : Nat) : Vector Bool d :=
  squeeze f r hr (absorb f pad r hr n) d

end Standards.NIST.SHA3
