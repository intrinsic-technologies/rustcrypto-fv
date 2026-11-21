import Standards.NIST.SHA3.Steps

/-!
# Keccak permutations

Round function and Keccak-p permutation from FIPS 202, §3.3, and Keccak-f specialization from
§3.4.

Source: https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.202.pdf
-/

namespace Standards.NIST.SHA3

/--
Round function (FIPS 202, §3.3)

Input: state array `A` and integer round index `ir`
Output: state array `A′`

Apply θ, ρ, π, χ, and ι in order: `Rnd(A,ir) = ι(χ(π(ρ(θ(A)))),ir)`.
-/
def round {ℓ : Fin 7} (a : StateArray ℓ) (ir : Int) : StateArray ℓ :=
  ι (χ (π (ρ (θ a)))) ir

/--
Keccak-p (FIPS 202, §3.3, Algorithm 7)

Input: size parameter `ℓ`, round count `nr`, and `b`-bit string `S`
Output: `b`-bit string `S′`

1. Convert `S` to a state array `A` using §3.1.2
2. For `ir = 12+2ℓ−nr, ..., 12+2ℓ−1`, replace `A` with `Rnd(A,ir)`
3. Convert `A` to a bit string `S′` using §3.1.3
4. Return `S′`
-/
def keccakP (ℓ : Fin 7) (nr : Nat) (s : Vector Bool (b ℓ)) : Vector Bool (b ℓ) := Id.run do
  let mut a := StateArray.ofString s
  let firstRound : Int := 12 + 2 * (ℓ : Nat) - (nr : Int)
  for i in [:nr] do
    a := round a (firstRound + (i : Int))
  return a.toString

/--
Keccak-f (FIPS 202, §3.4)

Input: size parameter `ℓ` and `b`-bit string `S`
Output: `b`-bit string `S′`

Specialize Keccak-p to `12+2ℓ` rounds, indexed from `0` through `11+2ℓ`:
`Keccak-f[b] = Keccak-p[b,12+2ℓ]`.
-/
def keccakF (ℓ : Fin 7) (s : Vector Bool (b ℓ)) : Vector Bool (b ℓ) :=
  keccakP ℓ (12 + 2 * (ℓ : Nat)) s

end Standards.NIST.SHA3
