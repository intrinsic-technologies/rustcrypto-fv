import ChaCha20Poly1305.Proofs.Decrypt.PolyFinish
import ChaCha20Poly1305.Proofs.Decrypt.PolyMulArithmetic
import ChaCha20Poly1305.Proofs.Decrypt.PolyReduction

namespace ChaCha20Poly1305.Proofs.Decrypt.Poly1305.Finish

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 150000

variable (x : Input)

def normalized := normalize (Mul.asLimbs x.acc)
def alternate := plusFive (normalized x)
def selected : Limbs := ⟨(v101da7 x).toNat,(v101dad x).toNat,(v101db2 x).toNat,
    (v101db6 x).toNat,(v101dbc x).toNat⟩

private theorem masked (v : BitVec 32) : (v &&& 67108863).toNat = v.toNat % B :=
  Nat.and_two_pow_sub_one_eq_mod _ 26

variable {x} (ha : (Mul.asLimbs x.acc).Bounded)
private theorem smallAdd (a b : BitVec 32) (h : a.toNat+b.toNat < 4294967296) :
    (a+b).toNat = a.toNat+b.toNat := Nat.mod_eq_of_lt h

include ha in
private theorem normWords :
    (v101d42 x).toNat = (normalized x).x0 ∧
    (v101d3f x).toNat = (normalized x).x1 ∧
    (v101d06 x).toNat = (normalized x).x2 ∧
    (v101d16 x).toNat = (normalized x).x3 ∧
    (v101d2a x).toNat = (normalized x).x4 := by
  obtain ⟨h0,h1,h2,h3,h4⟩ := ha
  simp only [Mul.asLimbs,B,Nat.reducePow] at h0 h1 h2 h3 h4
  have c1 : (v101cf4 x).toNat = x.acc[1].toNat/67108864 := by
    rw [v101cf4,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
  have c1b : (v101cf4 x).toNat ≤ 1 := by omega
  have a2 : (v101cf7 x).toNat = (v101cf4 x).toNat + x.acc[2].toNat :=
    smallAdd _ _ (by omega)
  have c2 : (v101d03 x).toNat = (v101cf7 x).toNat/67108864 := by
    rw [v101d03,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
  have c2b : (v101d03 x).toNat ≤ 1 := by omega
  have a3 : (v101d0c x).toNat = (v101d03 x).toNat + x.acc[3].toNat :=
    smallAdd _ _ (by omega)
  have c3 : (v101d12 x).toNat = (v101d0c x).toNat/67108864 := by
    rw [v101d12,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
  have c3b : (v101d12 x).toNat ≤ 1 := by omega
  have a4 : (v101d1c x).toNat = (v101d12 x).toNat + x.acc[4].toNat :=
    smallAdd _ _ (by omega)
  have c4 : (v101d23 x).toNat = (v101d1c x).toNat/67108864 := by
    rw [v101d23,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
  have c4b : (v101d23 x).toNat ≤ 1 := by omega
  have five : (v101d30 x).toNat = 5*(v101d23 x).toNat := by
    simp only [v101d30,BitVec.toNat_add,BitVec.toNat_shiftLeft,Nat.shiftLeft_eq,Nat.reducePow]
    omega
  have zero : (v101d34 x).toNat = (v101d30 x).toNat + x.acc[0].toNat :=
    smallAdd _ _ (by omega)
  have cz : (v101d3b x).toNat = (v101d34 x).toNat/67108864 := by
    rw [v101d3b,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
  have czb : (v101d3b x).toNat ≤ 1 := by omega
  have one : (v101d3f x).toNat = (v101d3b x).toNat + (v101cfa x).toNat := by
    apply smallAdd
    rw [v101cfa,masked]
    change _ + _ % 67108864 < 4294967296
    omega
  simp only [normalized,normalize,Mul.asLimbs,v101d42,v101d06,v101d16,v101d2a,v101cfa,
    one,masked,cz,zero,five,c4,a4,c3,a3,c2,a2,c1,B,Nat.reducePow,Nat.add_comm,Nat.mul_comm,and_true]

include ha in
private theorem norm0 : (v101d42 x).toNat = (normalized x).x0 := (normWords ha).1

include ha in
private theorem norm1 : (v101d3f x).toNat = (normalized x).x1 := (normWords ha).2.1

include ha in
private theorem norm2 : (v101d06 x).toNat = (normalized x).x2 := (normWords ha).2.2.1

include ha in
private theorem norm3 : (v101d16 x).toNat = (normalized x).x3 := (normWords ha).2.2.2.1

include ha in
private theorem norm4 : (v101d2a x).toNat = (normalized x).x4 := (normWords ha).2.2.2.2

include ha in
private theorem altWords :
    ((v101d49 x) &&& 67108863).toNat = (alternate x).x0 ∧
    ((v101d54 x) &&& 67108863).toNat = (alternate x).x1 ∧
    ((v101d5d x) &&& 67108863).toNat = (alternate x).x2 ∧
    ((v101d66 x) &&& 67108863).toNat = (alternate x).x3 ∧
    (v101d70 x).toNat = (alternate x).x4 := by
  obtain ⟨h0,h1,h2,h3,h4⟩ : (normalized x).Tight := normalize_tight ha
  simp only [B,Nat.reducePow] at h0 h1 h2 h3 h4
  have a0 : (v101d49 x).toNat = (normalized x).x0 + 5 := by
    change (_ + (5 : BitVec 32)).toNat = _
    have h : (v101d42 x).toNat + (5 : BitVec 32).toNat < 4294967296 := by
      rw [norm0 ha]; change _ + 5 < _; omega
    rw [smallAdd _ _ h, norm0 ha]; rfl
  have c1 : (v101d50 x).toNat = (v101d49 x).toNat/67108864 := by
    rw [v101d50,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
  have c1b : (v101d50 x).toNat ≤ 1 := by omega
  have a1 : (v101d54 x).toNat = (v101d50 x).toNat + (normalized x).x1 := by
    change (_ + (v101d3f x)).toNat = _
    rw [smallAdd, norm1 ha]
    rw [norm1 ha]; omega
  have c2 : (v101d5a x).toNat = (v101d54 x).toNat/67108864 := by
    rw [v101d5a,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
  have c2b : (v101d5a x).toNat ≤ 1 := by omega
  have a2 : (v101d5d x).toNat = (v101d5a x).toNat + (normalized x).x2 := by
    change (_ + (v101d06 x)).toNat = _
    rw [smallAdd, norm2 ha]
    rw [norm2 ha]; omega
  have c3 : (v101d62 x).toNat = (v101d5d x).toNat/67108864 := by
    rw [v101d62,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
  have c3b : (v101d62 x).toNat ≤ 1 := by omega
  have a3 : (v101d66 x).toNat = (v101d62 x).toNat + (normalized x).x3 := by
    change (_ + (v101d16 x)).toNat = _
    rw [smallAdd, norm3 ha]
    rw [norm3 ha]; omega
  have c4 : (v101d6c x).toNat = (v101d66 x).toNat/67108864 := by
    rw [v101d6c,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
  have c4b : (v101d6c x).toNat ≤ 1 := by omega
  have a4 : (v101d70 x).toNat = (v101d6c x).toNat + (normalized x).x4 := by
    change (_ + (v101d2a x)).toNat = _
    rw [smallAdd, norm4 ha]
    rw [norm4 ha]; omega
  simp only [alternate, plusFive, masked,a4,c4,a3,c3,a2,c2,a1,c1,a0,B,Nat.reducePow,Nat.add_comm,and_true]

include ha in
private theorem alt0 : ((v101d49 x) &&& 67108863).toNat = (alternate x).x0 := (altWords ha).1

include ha in
private theorem alt1 : ((v101d54 x) &&& 67108863).toNat = (alternate x).x1 := (altWords ha).2.1

include ha in
private theorem alt2 : ((v101d5d x) &&& 67108863).toNat = (alternate x).x2 := (altWords ha).2.2.1

include ha in
private theorem alt3 : ((v101d66 x) &&& 67108863).toNat = (alternate x).x3 := (altWords ha).2.2.2.1

include ha in
private theorem alt4 : (v101d70 x).toNat = (alternate x).x4 := (altWords ha).2.2.2.2

private theorem sign_high (t : BitVec 32) (high : 2147483648 ≤ t.toNat) :
    t.sshiftRight 31 = BitVec.allOnes 32 ∧ (t >>> 31)-1 = 0 := by
  have ms := BitVec.msb_eq_true_iff_two_mul_ge (x := t) |>.mpr (by omega)
  have lim := t.isLt
  constructor
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sshiftRight_of_msb_true ms, BitVec.toNat_allOnes, Nat.shiftRight_eq_div_pow]
    omega
  · have u : t >>> 31 = 1 := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,BitVec.toNat_one]
      change t.toNat / 2147483648 = 1; omega
    simp [u]

private theorem masks (b : BitVec 32) (h : b.toNat ≤ B) :
    let sign := (b+4227858432).sshiftRight 31
    let inv := ((b+4227858432) >>> 31) - 1
    if b.toNat < B then sign = BitVec.allOnes 32 ∧ inv = 0
    else sign = 0 ∧ inv = BitVec.allOnes 32 := by
  dsimp only
  have tr : (b + 4227858432 : BitVec 32).toNat = (b.toNat + 4227858432) % 4294967296 := by
    rw [BitVec.toNat_add]
    rfl
  split
  · apply sign_high
    rw [tr]; rename_i lt; change b.toNat < 67108864 at lt
    omega
  · have ht : b + 4227858432 = (0 : BitVec 32) := by
      apply BitVec.eq_of_toNat_eq; rw [tr]
      change _ = 0
      rename_i ge; change ¬ b.toNat < 67108864 at ge
      change b.toNat ≤ 67108864 at h
      omega
    rw [ht]
    decide

private theorem andZ (a : BitVec 32) : a &&& 0 = 0 := BitVec.and_zero
private theorem zAnd (a : BitVec 32) : 0 &&& a = 0 := BitVec.zero_and
private theorem orZ (a : BitVec 32) : a ||| 0 = a := BitVec.or_zero
private theorem zOr (a : BitVec 32) : 0 ||| a = a := BitVec.zero_or

include ha in
private theorem sel :
    (selected x).x0 < B ∧ (selected x).x1 < B ∧ (selected x).x2 < B ∧ (selected x).x3 < B ∧
    (selected x).value % 2^128 = (Mul.asLimbs x.acc).value % modulus % 2^128 := by
  have hn : (normalized x).Tight := normalize_tight ha
  have hv := chosen_value hn
  change (if (alternate x).x4 < B then _ else _) % 2^128 = _ at hv
  have hbase : (normalized x).value % modulus = _ := normalize_value (a := Mul.asLimbs x.acc)
  rw [← hbase, ← hv]
  have hm := masks (v101d70 x) ((alt4 ha).symm ▸ topBound hn)
  dsimp only at hm
  by_cases ht : (alternate x).x4 < B
  · rw [ite_eq_left ht]
    rw [alt4 ha, ite_eq_left ht] at hm
    obtain ⟨sg,iv⟩ := hm
    change v101d81 x = _ at sg
    change v101d88 x = _ at iv
    have raw : (v101d1c x).toNat % B = (normalized x).x4 := by
      simpa only [v101d2a, masked] using norm4 ha
    obtain ⟨h0,h1,h2,h3,h4⟩ := hn
    simp only [selected, v101da7, v101da4, v101d95, v101d8e, v101dad, v101daa, v101d98, v101db2, v101db0, v101d9b, v101db6, v101db4, v101d9e, v101dbc, v101db9, v101da1, sg,iv,andZ,zAnd,orZ,zOr,BitVec.and_zero,BitVec.zero_and,BitVec.and_allOnes,
      BitVec.allOnes_and,BitVec.or_zero,BitVec.zero_or, norm0 ha,norm1 ha,norm2 ha,norm3 ha]
    refine ⟨h0,h1,h2,h3,?_⟩
    simp only [Limbs.value,B,Nat.reducePow] at *
    omega
  · rw [ite_eq_right ht]
    rw [alt4 ha, ite_eq_right ht] at hm
    obtain ⟨sg,iv⟩ := hm
    change v101d81 x = _ at sg
    change v101d88 x = _ at iv
    have g4 : v101d7b x = v101d70 x := rfl
    simp only [selected, v101da7, v101da4, v101d95, v101d8e, v101dad, v101daa, v101d98, v101db2, v101db0, v101d9b, v101db6, v101db4, v101d9e, v101dbc, v101db9, v101da1, sg,iv,g4,andZ,zAnd,orZ,zOr,BitVec.and_zero,BitVec.zero_and,BitVec.and_allOnes,
      BitVec.allOnes_and,BitVec.or_zero,BitVec.zero_or,BitVec.and_comm (67108863 : BitVec 32),
      alt0 ha,alt1 ha,alt2 ha,alt3 ha,alt4 ha]
    simp only [alternate,plusFive,B,Nat.reducePow,Limbs.value]
    exact ⟨Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide), trivial⟩

private theorem pack {a b : BitVec 32} {k : Nat} (hb : b.toNat < 2^k) :
    ((a <<< k) ||| b).toNat = (a.toNat*2^k + b.toNat) % 2^32 := by
  simp only [BitVec.toNat_or,BitVec.toNat_shiftLeft]
  rw [← Nat.shiftLeft_eq, Nat.shiftLeft_add_eq_or_of_lt hb, Nat.or_mod_two_pow, Nat.mod_eq_of_lt b.isLt]

def wordsNum (a b c d : BitVec 32) : Nat :=
  a.toNat+2^32*(b.toNat+2^32*(c.toNat+2^32*d.toNat))

def tagNum (x : Input) := wordsNum (v101dec x) ((v101df5 x).setWidth 32)
  ((v101e02 x).setWidth 32) (v101e0e x)

def padNum (x : Input) := wordsNum x.s[0] x.s[1] x.s[2] x.s[3]

include ha in
private theorem packed : wordsNum (v101dc6 x) (v101dd4 x) (v101de1 x) (v101dea x) =
    (Mul.asLimbs x.acc).value % modulus % 2^128 := by
  obtain ⟨h0,h1,h2,h3,hv⟩ := sel ha
  simp only [selected,B,Nat.reducePow] at h0 h1 h2 h3
  have hb (b : BitVec 32) (n : Nat) : (b >>> n).toNat = b.toNat / 2^n :=
    Nat.shiftRight_eq_div_pow _ _
  have p0 := @pack (v101dad x) (v101da7 x) 26 h0
  have p1 := @pack (v101db2 x) (v101dc9 x) 20 (by rw [v101dc9,hb]; omega)
  have p2 := @pack (v101db6 x) (v101dd7 x) 14 (by rw [v101dd7,hb]; omega)
  have p3 := @pack (v101dbc x) (v101de4 x) 8 (by rw [v101de4,hb]; omega)
  change (v101dc6 x).toNat = _ at p0
  change (v101dd4 x).toNat = _ at p1
  change (v101de1 x).toNat = _ at p2
  change (v101dea x).toNat = _ at p3
  rw [← hv]
  simp only [wordsNum,selected,Limbs.value,B,p0,p1,p2,p3,v101dc9,v101dd7,v101de4,hb,Nat.reducePow]
  omega

private theorem wordsAdd (a b c d e f g h : BitVec 32) :
    let u := f.setWidth 64 + b.setWidth 64 + (if a+e<a then 1 else 0)
    let v := (u >>> 32) + (g.setWidth 64 + c.setWidth 64)
    wordsNum (a+e) (u.setWidth 32) (v.setWidth 32) ((v >>> 32).setWidth 32 + (d+h)) =
      (wordsNum a b c d + wordsNum e f g h) % 2^128 := by
  have wide (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat := BitVec.toNat_setWidth_of_le (by decide)
  have shr (x : BitVec 64) : (x >>> 32).toNat = x.toNat / 4294967296 := Nat.shiftRight_eq_div_pow _ _
  have narrow (x : BitVec 64) : (x.setWidth 32).toNat = x.toNat % 4294967296 := BitVec.toNat_setWidth 32 x
  have wsum (x y : BitVec 32) : (x.setWidth 64 + y.setWidth 64).toNat = x.toNat + y.toNat := by
    rw [BitVec.toNat_add,wide,wide,Nat.mod_eq_of_lt]
    have := x.isLt; have := y.isLt; omega
  let car : BitVec 64 := if a+e<a then 1 else 0
  let u := f.setWidth 64 + b.setWidth 64 + car
  let v := (u >>> 32) + (g.setWidth 64 + c.setWidth 64)
  change wordsNum (a+e) (u.setWidth 32) (v.setWidth 32) ((v >>> 32).setWidth 32 + (d+h)) = _
  have carr : car.toNat = (a.toNat + e.toNat) / 4294967296 := by
    have := a.isLt; have := e.isLt
    dsimp only [car]; split <;> rename_i hh
    · change _ % 4294967296 < _ at hh; change 1 = _; omega
    · change ¬ _ % 4294967296 < _ at hh; change 0 = _; omega
  have uc : u.toNat = f.toNat + b.toNat + car.toNat := by
    simp only [u,BitVec.toNat_add,wide,Nat.reducePow]
    have := f.isLt; have := b.isLt; have := a.isLt; have := e.isLt
    omega
  have vc : v.toNat = u.toNat / 4294967296 + (g.toNat+c.toNat) := by
    rw [show v = (u >>> 32) + (g.setWidth 64 + c.setWidth 64) from rfl,BitVec.toNat_add,wsum,shr,Nat.mod_eq_of_lt]
    have := u.isLt; have := g.isLt; have := c.isLt; omega
  simp only [wordsNum,BitVec.toNat_add,narrow,shr,vc,uc,carr,Nat.reducePow]
  have := a.isLt; have := b.isLt; have := c.isLt; have := d.isLt
  have := e.isLt; have := f.isLt; have := g.isLt; have := h.isLt
  omega

include ha in
theorem tagNum_eq : tagNum x = ((Mul.asLimbs x.acc).value % modulus + padNum x) % 2^128 := by
  have hw : tagNum x = (wordsNum (v101dc6 x) (v101dd4 x) (v101de1 x) (v101dea x) + padNum x) % 2^128 :=
    wordsAdd (v101dc6 x) (v101dd4 x) (v101de1 x) (v101dea x) x.s[0] x.s[1] x.s[2] x.s[3]
  rw [hw,packed ha,Nat.mod_add_mod]

end ChaCha20Poly1305.Proofs.Decrypt.Poly1305.Finish
