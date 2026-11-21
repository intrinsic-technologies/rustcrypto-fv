import P256.Proofs.Field.Montgomery.Words
import P256.Proofs.SecretKeyFromBytes.Arithmetic

set_option autoImplicit false

namespace P256.Proofs.Field.Montgomery.Reduction

open X86Proofs
open P256.Proofs.SecretKeyFromBytes.Scalar (Limbs)

attribute [local irreducible] add64 adc64 product64

def firstRound (a : Limbs) : Limbs :=
  let m := product64 a.l0 0xffffffff
  let x := add64 a.l1 a.l0
  let y := add64 m.1 x.1
  let z := adc64 (BitVec.ofNat 64 x.2.toNat) m.2 y.2
  let p := product64 a.l0 0xffffffff00000001
  let u := add64 p.1 a.l3
  let v := adc64 p.2 0 u.2
  let w := add64 z.1 a.l2
  let k := adc64 u.1 0 w.2
  let n := adc64 v.1 0 k.2
  ⟨y.1, w.1, k.1, n.1⟩

theorem firstRound_value (a : Limbs) :
    (firstRound a).toNat = reduceStep a.toNat := by
  let m := product64 a.l0 0xffffffff
  let x := add64 a.l1 a.l0
  let y := add64 m.1 x.1
  let z := adc64 (BitVec.ofNat 64 x.2.toNat) m.2 y.2
  let p := product64 a.l0 0xffffffff00000001
  let u := add64 p.1 a.l3
  let v := adc64 p.2 0 u.2
  let w := add64 z.1 a.l2
  let k := adc64 u.1 0 w.2
  let n := adc64 v.1 0 k.2
  have hm := product64_value a.l0 0xffffffff
  have hx := add64_value a.l1 a.l0
  have hy := add64_value m.1 x.1
  have hz := adc64_value (BitVec.ofNat 64 x.2.toNat) m.2 y.2
  have hp := product64_value a.l0 0xffffffff00000001
  have hu := add64_value p.1 a.l3
  have hv := adc64_value p.2 0 u.2
  have hw := add64_value z.1 a.l2
  have hk := adc64_value u.1 0 w.2
  have hn := adc64_value v.1 0 k.2
  change m.1.toNat + wordBase*m.2.toNat = a.l0.toNat*4294967295 at hm
  change x.1.toNat + wordBase*x.2.toNat = a.l1.toNat+a.l0.toNat at hx
  change y.1.toNat + wordBase*y.2.toNat = m.1.toNat+x.1.toNat at hy
  change z.1.toNat + wordBase*z.2.toNat = x.2.toNat%wordBase+m.2.toNat+y.2.toNat at hz
  change p.1.toNat + wordBase*p.2.toNat = a.l0.toNat*18446744069414584321 at hp
  change u.1.toNat + wordBase*u.2.toNat = p.1.toNat+a.l3.toNat at hu
  change v.1.toNat + wordBase*v.2.toNat = p.2.toNat+0+u.2.toNat at hv
  change w.1.toNat + wordBase*w.2.toNat = z.1.toNat+a.l2.toNat at hw
  change k.1.toNat + wordBase*k.2.toNat = u.1.toNat+0+w.2.toNat at hk
  change n.1.toNat + wordBase*n.2.toNat = v.1.toNat+0+k.2.toNat at hn
  have ha := a.l0.isLt
  have hx2 := Bool.toNat_le x.2
  have hy2 := Bool.toNat_le y.2
  have hu2 := Bool.toNat_le u.2
  have hk2 := Bool.toNat_le k.2
  have hred := P256.Proofs.Field.Montgomery.reduceStep_limbs_sparse a.l0.toNat a.l1.toNat
    a.l2.toNat a.l3.toNat a.l0.isLt
  change reduceStep a.toNat = _ at hred
  rw [hred]
  change y.1.toNat+wordBase*(w.1.toNat+wordBase*(k.1.toNat+wordBase*n.1.toNat)) = _
  clear_value m x y z p u v w k n
  clear hred
  dsimp only [wordBase, P256.Proofs.Field.Montgomery.wordBase] at *
  have hmhi : m.2.toNat < 2^32 := by
    clear hx hy hz hp hu hv hw hk hn hx2 hy2 hu2 hk2
    omega
  have hphi : p.2.toNat < 18446744069414584321 := by
    clear hm hx hy hz hu hv hw hk hn hx2 hy2 hu2 hk2 hmhi
    omega
  have hz0 : z.2.toNat = 0 := by
    clear hm hx hy hp hu hv hw hk hn ha hu2 hk2 hphi
    omega
  have hv0 : v.2.toNat = 0 := by
    clear hm hx hy hz hp hu hw hk hn ha hx2 hy2 hk2 hmhi hz0
    omega
  have hn0 : n.2.toNat = 0 := by
    clear hm hx hy hz hp hu hw hk ha hx2 hy2 hmhi hz0
    omega
  rw [hz0, Nat.mul_zero, Nat.add_zero] at hz
  rw [hv0, Nat.mul_zero, Nat.add_zero] at hv
  rw [hn0, Nat.mul_zero, Nat.add_zero] at hn
  omega

def shiftRound (a : Limbs) (z : BitVec 64) : Limbs × Bool :=
  let p := product64 a.l0 0xffffffff00000001
  let x := add64 a.l3 z
  let y := add64 x.1 p.1
  let h := adc64 p.2 0 y.2
  let u := add64 (a.l0 <<< 32) a.l1
  let v := adc64 (a.l0 >>> 32) a.l2 u.2
  let w := adc64 y.1 0 v.2
  let k := adc64 h.1 0 w.2
  (⟨u.1, v.1, w.1, k.1⟩, x.2)

theorem split32_value (a : BitVec 64) :
    (a <<< 32).toNat + wordBase*(a >>> 32).toNat = a.toNat*2^32 := by
  have ha := a.isLt
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  dsimp only [wordBase]
  omega

theorem shiftRound_value (a : Limbs) (z : BitVec 64) :
    (shiftRound a z).1.toNat + wordBase^3*(shiftRound a z).2.toNat =
      reduceStep a.toNat + wordBase^2*z.toNat := by
  let p := product64 a.l0 0xffffffff00000001
  let x := add64 a.l3 z
  let y := add64 x.1 p.1
  let h := adc64 p.2 0 y.2
  let u := add64 (a.l0 <<< 32) a.l1
  let v := adc64 (a.l0 >>> 32) a.l2 u.2
  let w := adc64 y.1 0 v.2
  let k := adc64 h.1 0 w.2
  have hp := product64_value a.l0 0xffffffff00000001
  have hx := add64_value a.l3 z
  have hy := add64_value x.1 p.1
  have hh := adc64_value p.2 0 y.2
  have hu := add64_value (a.l0 <<< 32) a.l1
  have hv := adc64_value (a.l0 >>> 32) a.l2 u.2
  have hw := adc64_value y.1 0 v.2
  have hk := adc64_value h.1 0 w.2
  have hs := split32_value a.l0
  change p.1.toNat+wordBase*p.2.toNat = a.l0.toNat*18446744069414584321 at hp
  change x.1.toNat+wordBase*x.2.toNat = a.l3.toNat+z.toNat at hx
  change y.1.toNat+wordBase*y.2.toNat = x.1.toNat+p.1.toNat at hy
  change h.1.toNat+wordBase*h.2.toNat = p.2.toNat+0+y.2.toNat at hh
  change u.1.toNat+wordBase*u.2.toNat = (a.l0 <<< 32).toNat+a.l1.toNat at hu
  change v.1.toNat+wordBase*v.2.toNat = (a.l0 >>> 32).toNat+a.l2.toNat+u.2.toNat at hv
  change w.1.toNat+wordBase*w.2.toNat = y.1.toNat+0+v.2.toNat at hw
  change k.1.toNat+wordBase*k.2.toNat = h.1.toNat+0+w.2.toNat at hk
  have ha := a.l0.isLt
  have hy2 := Bool.toNat_le y.2
  have hw2 := Bool.toNat_le w.2
  have hred := P256.Proofs.Field.Montgomery.reduceStep_limbs_sparse a.l0.toNat a.l1.toNat
    a.l2.toNat a.l3.toNat a.l0.isLt
  change reduceStep a.toNat = _ at hred
  rw [hred]
  change u.1.toNat+wordBase*(v.1.toNat+wordBase*(w.1.toNat+wordBase*k.1.toNat)) +
    wordBase^3*x.2.toNat = _
  clear_value p x y h u v w k
  clear hred
  dsimp only [wordBase, P256.Proofs.Field.Montgomery.wordBase] at *
  have hphi : p.2.toNat < 18446744069414584321 := by
    clear hx hy hh hu hv hw hk hs hy2 hw2
    omega
  have hh0 : h.2.toNat = 0 := by
    clear hp hx hy hu hv hw hk hs ha hw2
    omega
  have hk0 : k.2.toNat = 0 := by
    clear hp hx hy hu hv hw hs ha
    omega
  rw [hh0, Nat.mul_zero, Nat.add_zero] at hh
  rw [hk0, Nat.mul_zero, Nat.add_zero] at hk
  omega


end P256.Proofs.Field.Montgomery.Reduction
