import ChaCha20Poly1305.Proofs.Common.Poly1305State

namespace ChaCha20Poly1305.Proofs.Poly1305.BlockArith

open ChaCha20Poly1305.Proofs.Poly1305State

def mask26 : BitVec 32 := 0x3ffffff
def wide (x : BitVec 32) : BitVec 64 := x.setWidth 64
def lo26 (d : BitVec 64) : BitVec 32 := d.setWidth 32 &&& mask26
def hi26 (d : BitVec 64) : BitVec 32 := (d >>> 26).setWidth 32
def mac5 (x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 : BitVec 32) : BitVec 64 :=
  wide x0 * wide y0 + wide x1 * wide y1 + wide x2 * wide y2 + wide x3 * wide y3 + wide x4 * wide y4

theorem wide_toNat (x : BitVec 32) : (wide x).toNat = x.toNat := by
  simp [wide]; omega

theorem wide_mul_toNat (x y : BitVec 32) : (wide x * wide y).toNat = x.toNat * y.toNat := by
  rw [BitVec.toNat_mul, wide_toNat, wide_toNat]
  apply Nat.mod_eq_of_lt
  have := Nat.mul_lt_mul_of_lt_of_lt x.isLt y.isLt
  simpa using this

theorem mask26_toNat (x : BitVec 32) : (x &&& mask26).toNat = x.toNat % 2 ^ 26 := by
  rw [BitVec.toNat_and]
  show x.toNat &&& (2 ^ 26 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod]

theorem lo26_toNat (d : BitVec 64) : (lo26 d).toNat = d.toNat % 2 ^ 26 := by
  rw [lo26, mask26_toNat]
  simp

theorem hi26_toNat (d : BitVec 64) (hd : d.toNat < 2 ^ 58) : (hi26 d).toNat = d.toNat / 2 ^ 26 := by
  simp [hi26, Nat.shiftRight_eq_div_pow]
  omega

theorem mac5_toNat (x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 : BitVec 32)
    (h : x0.toNat * y0.toNat + x1.toNat * y1.toNat + x2.toNat * y2.toNat + x3.toNat * y3.toNat +
      x4.toNat * y4.toNat < 2 ^ 64) :
    (mac5 x0 y0 x1 y1 x2 y2 x3 y3 x4 y4).toNat = x0.toNat * y0.toNat + x1.toNat * y1.toNat +
      x2.toNat * y2.toNat + x3.toNat * y3.toNat + x4.toNat * y4.toNat := by
  simp only [mac5, BitVec.toNat_add, wide_mul_toNat]
  generalize x0.toNat * y0.toNat = a at *
  generalize x1.toNat * y1.toNat = b at *
  generalize x2.toNat * y2.toNat = c at *
  generalize x3.toNat * y3.toNat = d at *
  generalize x4.toNat * y4.toNat = e at *
  omega

theorem add_wide_toNat (d : BitVec 64) (c : BitVec 32) (h : d.toNat + c.toNat < 2 ^ 64) :
    (d + wide c).toNat = d.toNat + c.toNat := by
  rw [BitVec.toNat_add, wide_toNat]
  omega

theorem add32_toNat (x y : BitVec 32) (h : x.toNat + y.toNat < 2 ^ 32) :
    (x + y).toNat = x.toNat + y.toNat := by
  rw [BitVec.toNat_add]
  omega

theorem mul5_toNat (x : BitVec 32) (h : x.toNat < 2 ^ 29) : (x * 5).toNat = 5 * x.toNat := by
  rw [BitVec.toNat_mul]
  simp
  omega

theorem block_nat (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : Nat)
    (ha0 : a0 < 2^27) (ha1 : a1 < 2^27 + 2^6) (ha2 : a2 < 2^27) (ha3 : a3 < 2^27)
    (ha4 : a4 < 2^26 + 2^25)
    (hb0 : b0 < 2^26) (hb1 : b1 < 2^26) (hb2 : b2 < 2^26) (hb3 : b3 < 2^26) (hb4 : b4 < 2^20) :
    let D0 := a0*b0 + a1*(5*b4) + a2*(5*b3) + a3*(5*b2) + a4*(5*b1)
    let D1 := a0*b1 + a1*b0 + a2*(5*b4) + a3*(5*b3) + a4*(5*b2)
    let D2 := a0*b2 + a1*b1 + a2*b0 + a3*(5*b4) + a4*(5*b3)
    let D3 := a0*b3 + a1*b2 + a2*b1 + a3*b0 + a4*(5*b4)
    let D4 := a0*b4 + a1*b3 + a2*b2 + a3*b1 + a4*b0
    let E1 := D1 + D0 / 2^26
    let E2 := D2 + E1 / 2^26
    let E3 := D3 + E2 / 2^26
    let E4 := D4 + E3 / 2^26
    let g := D0 % 2^26 + 5 * (E4 / 2^26)
    D0 < 2^58 ∧ E1 < 2^58 ∧ E2 < 2^58 ∧ E3 < 2^58 ∧ E4 < 2^58 ∧ E4 / 2^26 < 2^29 ∧
    g < 2^32 ∧ E1 % 2^26 + g / 2^26 < 2^26 + 2^6 ∧
    (g % 2^26 + 2^26 * (E1 % 2^26 + g / 2^26) + 2^52 * (E2 % 2^26) + 2^78 * (E3 % 2^26) +
      2^104 * (E4 % 2^26)) % (2^130 - 5) =
    ((a0 + 2^26*a1 + 2^52*a2 + 2^78*a3 + 2^104*a4) *
      (b0 + 2^26*b1 + 2^52*b2 + 2^78*b3 + 2^104*b4)) % (2^130 - 5) := by
  dsimp only
  have m : ∀ {x y X Y : Nat}, x < X → y < Y → x * y < X * Y := fun hx hy =>
    Nat.mul_lt_mul_of_lt_of_lt hx hy
  have p00 := m ha0 hb0; have p01 := m ha0 hb1; have p02 := m ha0 hb2; have p03 := m ha0 hb3
  have p04 := m ha0 hb4
  have p10 := m ha1 hb0; have p11 := m ha1 hb1; have p12 := m ha1 hb2; have p13 := m ha1 hb3
  have p14 := m ha1 hb4
  have p20 := m ha2 hb0; have p21 := m ha2 hb1; have p22 := m ha2 hb2; have p23 := m ha2 hb3
  have p24 := m ha2 hb4
  have p30 := m ha3 hb0; have p31 := m ha3 hb1; have p32 := m ha3 hb2; have p33 := m ha3 hb3
  have p34 := m ha3 hb4
  have p40 := m ha4 hb0; have p41 := m ha4 hb1; have p42 := m ha4 hb2; have p43 := m ha4 hb3
  have p44 := m ha4 hb4
  have hring : (a0*b0 + a1*(5*b4) + a2*(5*b3) + a3*(5*b2) + a4*(5*b1)) +
      2^26*(a0*b1 + a1*b0 + a2*(5*b4) + a3*(5*b3) + a4*(5*b2)) +
      2^52*(a0*b2 + a1*b1 + a2*b0 + a3*(5*b4) + a4*(5*b3)) +
      2^78*(a0*b3 + a1*b2 + a2*b1 + a3*b0 + a4*(5*b4)) +
      2^104*(a0*b4 + a1*b3 + a2*b2 + a3*b1 + a4*b0) + (2^130-5) *
      (a1*b4 + a2*b3 + a3*b2 + a4*b1 + 2^26*(a2*b4 + a3*b3 + a4*b2) + 2^52*(a3*b4+a4*b3) +
        2^78*(a4*b4)) =
      (a0 + 2^26*a1 + 2^52*a2 + 2^78*a3 + 2^104*a4) *
        (b0 + 2^26*b1 + 2^52*b2 + 2^78*b3 + 2^104*b4) := by
    grind
  rw [← hring, Nat.add_mul_mod_self_left]
  have e : ∀ x y : Nat, x * (5 * y) = 5 * (x * y) := fun x y => by
    rw [← Nat.mul_assoc, Nat.mul_comm x 5, Nat.mul_assoc]
  simp only [e]
  generalize a0 * b0 = q00 at *
  generalize a0 * b1 = q01 at *
  generalize a0 * b2 = q02 at *
  generalize a0 * b3 = q03 at *
  generalize a0 * b4 = q04 at *
  generalize a1 * b0 = q10 at *
  generalize a1 * b1 = q11 at *
  generalize a1 * b2 = q12 at *
  generalize a1 * b3 = q13 at *
  generalize a1 * b4 = q14 at *
  generalize a2 * b0 = q20 at *
  generalize a2 * b1 = q21 at *
  generalize a2 * b2 = q22 at *
  generalize a2 * b3 = q23 at *
  generalize a2 * b4 = q24 at *
  generalize a3 * b0 = q30 at *
  generalize a3 * b1 = q31 at *
  generalize a3 * b2 = q32 at *
  generalize a3 * b3 = q33 at *
  generalize a3 * b4 = q34 at *
  generalize a4 * b0 = q40 at *
  generalize a4 * b1 = q41 at *
  generalize a4 * b2 = q42 at *
  generalize a4 * b3 = q43 at *
  generalize a4 * b4 = q44 at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

def limbs5 (a b c d e : BitVec 32) : Fin 5 → BitVec 32
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b
  | ⟨2, _⟩ => c
  | ⟨3, _⟩ => d
  | ⟨_ + 4, _⟩ => e

@[simp] theorem limbs5_0 (a b c d e : BitVec 32) : limbs5 a b c d e 0 = a := rfl
@[simp] theorem limbs5_1 (a b c d e : BitVec 32) : limbs5 a b c d e 1 = b := rfl
@[simp] theorem limbs5_2 (a b c d e : BitVec 32) : limbs5 a b c d e 2 = c := rfl
@[simp] theorem limbs5_3 (a b c d e : BitVec 32) : limbs5 a b c d e 3 = d := rfl
@[simp] theorem limbs5_4 (a b c d e : BitVec 32) : limbs5 a b c d e 4 = e := rfl

def msgLimbs (w : Fin 5 → BitVec 32) : Fin 5 → BitVec 32 :=
  limbs5 (w 0 &&& mask26) ((w 1 >>> 2) &&& mask26) ((w 2 >>> 4) &&& mask26) (w 3 >>> 6)
    (w 4 >>> 8)

def blockStep (r h w : Fin 5 → BitVec 32) (hibit : BitVec 32) : Fin 5 → BitVec 32 :=
  let m := msgLimbs w
  let a0 := h 0 + m 0
  let a1 := h 1 + m 1
  let a2 := h 2 + m 2
  let a3 := h 3 + m 3
  let a4 := hibit + h 4 + m 4
  let d0 := mac5 a0 (r 0) a1 (r 4 * 5) a2 (r 3 * 5) a3 (r 2 * 5) a4 (r 1 * 5)
  let d1 := mac5 a0 (r 1) a1 (r 0) a2 (r 4 * 5) a3 (r 3 * 5) a4 (r 2 * 5)
  let d2 := mac5 a0 (r 2) a1 (r 1) a2 (r 0) a3 (r 4 * 5) a4 (r 3 * 5)
  let d3 := mac5 a0 (r 3) a1 (r 2) a2 (r 1) a3 (r 0) a4 (r 4 * 5)
  let d4 := mac5 a0 (r 4) a1 (r 3) a2 (r 2) a3 (r 1) a4 (r 0)
  let e1 := d1 + wide (hi26 d0)
  let e2 := d2 + wide (hi26 e1)
  let e3 := d3 + wide (hi26 e2)
  let e4 := d4 + wide (hi26 e3)
  let g := lo26 d0 + hi26 e4 * 5
  limbs5 (g &&& mask26) (lo26 e1 + (g >>> 26)) (lo26 e2) (lo26 e3) (lo26 e4)

theorem limb_sum_regroup (h0 h1 h2 h3 h4 m0 m1 m2 m3 m4 c : Nat) :
    h0 + 2 ^ 26 * h1 + 2 ^ 52 * h2 + 2 ^ 78 * h3 + 2 ^ 104 * h4 +
      (m0 + 2 ^ 26 * m1 + 2 ^ 52 * m2 + 2 ^ 78 * m3 + 2 ^ 104 * m4) + 2 ^ 104 * c =
    (h0 + m0) + 2 ^ 26 * (h1 + m1) + 2 ^ 52 * (h2 + m2) + 2 ^ 78 * (h3 + m3) +
      2 ^ 104 * (c + h4 + m4) := by omega

theorem blockStep_spec (r h w : Fin 5 → BitVec 32) (hibit : BitVec 32)
    (hr0 : (r 0).toNat < 2^26) (hr1 : (r 1).toNat < 2^26) (hr2 : (r 2).toNat < 2^26)
    (hr3 : (r 3).toNat < 2^26) (hr4 : (r 4).toNat < 2^20)
    (hh0 : (h 0).toNat < 2^26) (hh1 : (h 1).toNat < 2^26 + 2^6) (hh2 : (h 2).toNat < 2^26)
    (hh3 : (h 3).toNat < 2^26) (hh4 : (h 4).toNat < 2^26) (hhi : hibit.toNat ≤ 2^24) :
    ((blockStep r h w hibit 0).toNat < 2^26 ∧ (blockStep r h w hibit 1).toNat < 2^26 + 2^6 ∧
      (blockStep r h w hibit 2).toNat < 2^26 ∧ (blockStep r h w hibit 3).toNat < 2^26 ∧
      (blockStep r h w hibit 4).toNat < 2^26) ∧
    limbValue (blockStep r h w hibit) % prime =
      ((limbValue h + limbValue (msgLimbs w) + 2^104 * hibit.toNat) * limbValue r) % prime := by
  unfold prime
  have hm0 : (msgLimbs w 0).toNat < 2^26 := by
    simp only [msgLimbs, limbs5, mask26_toNat]; omega
  have hm1 : (msgLimbs w 1).toNat < 2^26 := by
    simp only [msgLimbs, limbs5, mask26_toNat]; omega
  have hm2 : (msgLimbs w 2).toNat < 2^26 := by
    simp only [msgLimbs, limbs5, mask26_toNat]; omega
  have hm3 : (msgLimbs w 3).toNat < 2^26 := by
    simp only [msgLimbs, limbs5, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have := (w 3).isLt; omega
  have hm4 : (msgLimbs w 4).toNat < 2^24 := by
    simp only [msgLimbs, limbs5, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have := (w 4).isLt; omega
  simp only [blockStep, limbValue, limbs5_0, limbs5_1, limbs5_2, limbs5_3, limbs5_4]
  generalize msgLimbs w = m at *
  have ea0 : (h 0 + m 0).toNat = (h 0).toNat + (m 0).toNat := add32_toNat _ _ (by omega)
  have ea1 : (h 1 + m 1).toNat = (h 1).toNat + (m 1).toNat := add32_toNat _ _ (by omega)
  have ea2 : (h 2 + m 2).toNat = (h 2).toNat + (m 2).toNat := add32_toNat _ _ (by omega)
  have ea3 : (h 3 + m 3).toNat = (h 3).toNat + (m 3).toNat := add32_toNat _ _ (by omega)
  have ea4' : (hibit + h 4).toNat = hibit.toNat + (h 4).toNat := add32_toNat _ _ (by omega)
  have ea4 : (hibit + h 4 + m 4).toNat = hibit.toNat + (h 4).toNat + (m 4).toNat := by
    rw [add32_toNat _ _ (by omega), ea4']
  have es1 := mul5_toNat (r 1) (by omega)
  have es2 := mul5_toNat (r 2) (by omega)
  have es3 := mul5_toNat (r 3) (by omega)
  have es4 := mul5_toNat (r 4) (by omega)
  have key := block_nat ((h 0).toNat + (m 0).toNat) ((h 1).toNat + (m 1).toNat)
    ((h 2).toNat + (m 2).toNat) ((h 3).toNat + (m 3).toNat)
    (hibit.toNat + (h 4).toNat + (m 4).toNat) (r 0).toNat (r 1).toNat (r 2).toNat (r 3).toNat
    (r 4).toNat (by omega) (by omega) (by omega) (by omega) (by omega) hr0 hr1 hr2 hr3 hr4
  dsimp only at key
  obtain ⟨b0, b1, b2, b3, b4, bc, bg, bout1, bval⟩ := key
  generalize hA0 : h 0 + m 0 = A0 at *
  generalize hA1 : h 1 + m 1 = A1 at *
  generalize hA2 : h 2 + m 2 = A2 at *
  generalize hA3 : h 3 + m 3 = A3 at *
  generalize hA4 : hibit + h 4 + m 4 = A4 at *
  have ed0 : (mac5 A0 (r 0) A1 (r 4 * 5) A2 (r 3 * 5) A3 (r 2 * 5) A4 (r 1 * 5)).toNat =
      A0.toNat * (r 0).toNat + A1.toNat * (5 * (r 4).toNat) + A2.toNat * (5 * (r 3).toNat) +
        A3.toNat * (5 * (r 2).toNat) + A4.toNat * (5 * (r 1).toNat) := by
    rw [mac5_toNat _ _ _ _ _ _ _ _ _ _ (by rw [es1, es2, es3, es4, ea0, ea1, ea2, ea3, ea4]; omega),
      es1, es2, es3, es4]
  have ed1 : (mac5 A0 (r 1) A1 (r 0) A2 (r 4 * 5) A3 (r 3 * 5) A4 (r 2 * 5)).toNat =
      A0.toNat * (r 1).toNat + A1.toNat * (r 0).toNat + A2.toNat * (5 * (r 4).toNat) +
        A3.toNat * (5 * (r 3).toNat) + A4.toNat * (5 * (r 2).toNat) := by
    rw [mac5_toNat _ _ _ _ _ _ _ _ _ _ (by rw [es2, es3, es4, ea0, ea1, ea2, ea3, ea4]; omega),
      es2, es3, es4]
  have ed2 : (mac5 A0 (r 2) A1 (r 1) A2 (r 0) A3 (r 4 * 5) A4 (r 3 * 5)).toNat =
      A0.toNat * (r 2).toNat + A1.toNat * (r 1).toNat + A2.toNat * (r 0).toNat +
        A3.toNat * (5 * (r 4).toNat) + A4.toNat * (5 * (r 3).toNat) := by
    rw [mac5_toNat _ _ _ _ _ _ _ _ _ _ (by rw [es3, es4, ea0, ea1, ea2, ea3, ea4]; omega),
      es3, es4]
  have ed3 : (mac5 A0 (r 3) A1 (r 2) A2 (r 1) A3 (r 0) A4 (r 4 * 5)).toNat =
      A0.toNat * (r 3).toNat + A1.toNat * (r 2).toNat + A2.toNat * (r 1).toNat +
        A3.toNat * (r 0).toNat + A4.toNat * (5 * (r 4).toNat) := by
    rw [mac5_toNat _ _ _ _ _ _ _ _ _ _ (by rw [es4, ea0, ea1, ea2, ea3, ea4]; omega), es4]
  have ed4 : (mac5 A0 (r 4) A1 (r 3) A2 (r 2) A3 (r 1) A4 (r 0)).toNat =
      A0.toNat * (r 4).toNat + A1.toNat * (r 3).toNat + A2.toNat * (r 2).toNat +
        A3.toNat * (r 1).toNat + A4.toNat * (r 0).toNat := by
    rw [mac5_toNat _ _ _ _ _ _ _ _ _ _ (by rw [ea0, ea1, ea2, ea3, ea4]; omega)]
  rw [ea0, ea1, ea2, ea3, ea4] at ed0 ed1 ed2 ed3 ed4
  generalize mac5 A0 (r 0) A1 (r 4 * 5) A2 (r 3 * 5) A3 (r 2 * 5) A4 (r 1 * 5) = d0 at *
  generalize mac5 A0 (r 1) A1 (r 0) A2 (r 4 * 5) A3 (r 3 * 5) A4 (r 2 * 5) = d1 at *
  generalize mac5 A0 (r 2) A1 (r 1) A2 (r 0) A3 (r 4 * 5) A4 (r 3 * 5) = d2 at *
  generalize mac5 A0 (r 3) A1 (r 2) A2 (r 1) A3 (r 0) A4 (r 4 * 5) = d3 at *
  generalize mac5 A0 (r 4) A1 (r 3) A2 (r 2) A3 (r 1) A4 (r 0) = d4 at *
  have ee1 : (d1 + wide (hi26 d0)).toNat = d1.toNat + d0.toNat / 2^26 := by
    rw [add_wide_toNat _ _ (by rw [hi26_toNat _ (by omega)]; omega), hi26_toNat _ (by omega)]
  generalize d1 + wide (hi26 d0) = e1 at *
  have ee2 : (d2 + wide (hi26 e1)).toNat = d2.toNat + e1.toNat / 2^26 := by
    rw [add_wide_toNat _ _ (by rw [hi26_toNat _ (by omega)]; omega), hi26_toNat _ (by omega)]
  generalize d2 + wide (hi26 e1) = e2 at *
  have ee3 : (d3 + wide (hi26 e2)).toNat = d3.toNat + e2.toNat / 2^26 := by
    rw [add_wide_toNat _ _ (by rw [hi26_toNat _ (by omega)]; omega), hi26_toNat _ (by omega)]
  generalize d3 + wide (hi26 e2) = e3 at *
  have ee4 : (d4 + wide (hi26 e3)).toNat = d4.toNat + e3.toNat / 2^26 := by
    rw [add_wide_toNat _ _ (by rw [hi26_toNat _ (by omega)]; omega), hi26_toNat _ (by omega)]
  generalize d4 + wide (hi26 e3) = e4 at *
  have hc4 : (hi26 e4).toNat = e4.toNat / 2^26 := hi26_toNat _ (by omega)
  have hc45 : (hi26 e4 * 5).toNat = 5 * (e4.toNat / 2^26) := by
    rw [mul5_toNat _ (by omega), hc4]
  have eg : (lo26 d0 + hi26 e4 * 5).toNat = d0.toNat % 2^26 + 5 * (e4.toNat / 2^26) := by
    rw [add32_toNat _ _ (by rw [hc45, lo26_toNat]; omega), hc45, lo26_toNat]
  generalize lo26 d0 + hi26 e4 * 5 = g at *
  have eo1 : (lo26 e1 + (g >>> 26)).toNat = e1.toNat % 2^26 + g.toNat / 2^26 := by
    rw [add32_toNat _ _ (by
      rw [lo26_toNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega),
      lo26_toNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have o0 : (g &&& mask26).toNat = g.toNat % 2^26 := mask26_toNat g
  have o2 := lo26_toNat e2
  have o3 := lo26_toNat e3
  have o4 := lo26_toNat e4
  rw [o0, eo1, o2, o3, o4, eg, ee4, ee3, ee2, ee1, ed0, ed1, ed2, ed3, ed4]
  rw [limb_sum_regroup]
  exact ⟨⟨Nat.mod_lt _ (by decide), bout1, Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide),
    Nat.mod_lt _ (by decide)⟩, bval⟩

end ChaCha20Poly1305.Proofs.Poly1305.BlockArith
