import Standards.NIST.SHA3.State

/-!
# Keccak step mappings

The five round mappings from FIPS 202, §3.2, and the round-constant bit generator. Coordinates
satisfy `0 ≤ x, y < 5` and `0 ≤ z < w`.

Source: https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.202.pdf
-/

namespace Standards.NIST.SHA3

variable {ℓ : Fin 7}

/--
θ (FIPS 202, §3.2.1, Algorithm 1)

Input: state array `A`
Output: state array `A′`

1. Compute column parities: `C[x,z] = A[x,0,z] ⊕ A[x,1,z] ⊕ ... ⊕ A[x,4,z]`
2. Set `D[x,z] = C[(x−1) mod 5,z] ⊕ C[(x+1) mod 5,(z−1) mod w]`
3. Set `A′[x,y,z] = A[x,y,z] ⊕ D[x,z]` for every coordinate
-/
def θ (a : StateArray ℓ) : StateArray ℓ :=
  let _ : NeZero (w ℓ) := ⟨Nat.ne_of_gt (Nat.pow_pos (by decide))⟩
  let c := Vector.ofFn fun x : Fin 5 => Vector.ofFn fun z : Fin (w ℓ) =>
    a[x, 0, z] ^^ a[x, 1, z] ^^ a[x, 2, z] ^^ a[x, 3, z] ^^ a[x, 4, z]
  let d := Vector.ofFn fun x : Fin 5 => Vector.ofFn fun z : Fin (w ℓ) =>
    c[x - 1][z] ^^ c[x + 1][z - 1]
  ⟨Vector.ofFn fun x => Vector.ofFn fun y => Vector.ofFn fun z =>
    a[x, y, z] ^^ d[x][z]⟩

/--
ρ (FIPS 202, §3.2.2, Algorithm 2)

Input: state array `A`
Output: state array `A′`

1. Copy lane `(0,0)`: `A′[0,0,z] = A[0,0,z]`
2. Start at `(x,y) = (1,0)`
3. For `t = 0, ..., 23`:
   a. Set `A′[x,y,z] = A[x,y,(z−(t+1)(t+2)/2) mod w]` for every `z`
   b. Update `(x,y)` simultaneously to `(y,(2x+3y) mod 5)`
4. Return `A′`
-/
def ρ (a : StateArray ℓ) : StateArray ℓ := Id.run do
  let _ : NeZero (w ℓ) := ⟨Nat.ne_of_gt (Nat.pow_pos (by decide))⟩
  let mut bits := a.bits
  let mut x : Fin 5 := 1
  let mut y : Fin 5 := 0
  for t in [:24] do
    let offset := (t + 1) * (t + 2) / 2
    let lane := Vector.ofFn fun z : Fin (w ℓ) =>
      a[x, y, (z - Fin.ofNat (w ℓ) offset : Fin (w ℓ))]
    bits := bits.set x (bits[x].set y lane)
    (x, y) := (y, 2 * x + 3 * y)
  return ⟨bits⟩

/--
π (FIPS 202, §3.2.3, Algorithm 3)

Input: state array `A`
Output: state array `A′`

1. Set `A′[x,y,z] = A[(x+3y) mod 5,x,z]` for every coordinate
2. Return `A′`
-/
def π (a : StateArray ℓ) : StateArray ℓ :=
  ⟨Vector.ofFn fun x => Vector.ofFn fun y => Vector.ofFn fun z =>
    a[(x + 3 * y : Fin 5), x, z]⟩

/--
χ (FIPS 202, §3.2.4, Algorithm 4)

Input: state array `A`
Output: state array `A′`

1. For every coordinate, set
   `A′[x,y,z] = A[x,y,z] ⊕ ((A[(x+1) mod 5,y,z] ⊕ 1) · A[(x+2) mod 5,y,z])`
2. Return `A′`
-/
def χ (a : StateArray ℓ) : StateArray ℓ :=
  ⟨Vector.ofFn fun x => Vector.ofFn fun y => Vector.ofFn fun z =>
    a[x, y, z] ^^ ((!a[(x + 1 : Fin 5), y, z]) && a[(x + 2 : Fin 5), y, z])⟩

/--
Round-constant bit generator (FIPS 202, §3.2.5, Algorithm 5)

Input: integer `t`
Output: bit `rc(t)`

1. If `t mod 255 = 0`, return `1`
2. Initialize the bit string `R = 10000000`, with `R[0] = 1`
3. Repeat `t mod 255` times:
   a. Prepend `0` to `R`, producing nine bits
   b. Replace `R[0]` with `R[0] ⊕ R[8]`
   c. Replace `R[4]` with `R[4] ⊕ R[8]`
   d. Replace `R[5]` with `R[5] ⊕ R[8]`
   e. Replace `R[6]` with `R[6] ⊕ R[8]`
   f. Keep the first eight bits of `R`
4. Return `R[0]`
-/
def rc (t : Int) : Bool := Id.run do
  let mut r : Vector Bool 8 := #v[true, false, false, false, false, false, false, false]
  for _ in [:(t % 255).toNat] do
    r := #v[r[7], r[0], r[1], r[2], r[3] ^^ r[7], r[4] ^^ r[7], r[5] ^^ r[7], r[6]]
  return r[0]

/--
ι (FIPS 202, §3.2.5, Algorithm 6)

Input: state array `A` and integer round index `ir`
Output: state array `A′`

1. Copy `A` into `A′`
2. Initialize the `w`-bit round constant `RC` to zero
3. For `j = 0, ..., ℓ`, set `RC[2^j−1] = rc(j+7ir)`
4. Set `A′[0,0,z] = A′[0,0,z] ⊕ RC[z]` for every `z`
5. Return `A′`; all lanes other than `(0,0)` are unchanged
-/
def ι (a : StateArray ℓ) (ir : Int) : StateArray ℓ := Id.run do
  let mut roundConstant := Vector.replicate (w ℓ) false
  for hj : j in [:(ℓ : Nat) + 1] do
    have hjlt : j < (ℓ : Nat) + 1 := hj.2.1
    have hpow : 2 ^ j ≤ w ℓ := Nat.pow_le_pow_right (by decide) (by omega)
    have hpos : 0 < 2 ^ j := Nat.pow_pos (by decide)
    roundConstant := roundConstant.set (2 ^ j - 1) (rc (j + 7 * ir)) (by omega)
  let lane := Vector.ofFn fun z => a[0, 0, z] ^^ roundConstant[z]
  return ⟨a.bits.set 0 (a.bits[0].set 0 lane)⟩

end Standards.NIST.SHA3
