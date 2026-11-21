import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Arithmetic.Words

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Montgomery

structure TopWords where
  low : BitVec 64
  mid : BitVec 64
  high : BitVec 64
  carry : Bool

def TopWords.value (t : TopWords) : Nat :=
  t.low.toNat + wordBase*t.mid.toNat + wordBase^2*t.high.toNat + wordBase^3*t.carry.toNat

def firstTop (c0 c1 a b next : BitVec 64) : TopWords :=
  let x := product64 a b
  let y := product64 next b
  let l := add64 c0 x.1
  let m := adc64 c1 x.2 l.2
  let n := add64 m.1 y.1
  let h := adc64 y.2 0 n.2
  let k := adc64 h.1 0 m.2
  ⟨l.1, n.1, k.1, k.2⟩

theorem firstTop_value (c0 c1 a b next : BitVec 64) :
    (firstTop c0 c1 a b next).value =
      c0.toNat + wordBase*c1.toNat + a.toNat*b.toNat + wordBase*(next.toNat*b.toNat) := by
  let x := product64 a b
  let y := product64 next b
  let l := add64 c0 x.1
  let m := adc64 c1 x.2 l.2
  let n := add64 m.1 y.1
  let h := adc64 y.2 0 n.2
  let k := adc64 h.1 0 m.2
  have hx := product64_value a b
  have hy := product64_value next b
  have hl := add64_value c0 x.1
  have hm := adc64_value c1 x.2 l.2
  have hn := add64_value m.1 y.1
  have hh := adc64_value y.2 0 n.2
  have hk := adc64_value h.1 0 m.2
  have hylt := product64_high_lt next b
  have hnlt := Bool.toNat_le n.2
  change x.1.toNat + 18446744073709551616*x.2.toNat = _ at hx
  change y.1.toNat + 18446744073709551616*y.2.toNat = _ at hy
  change l.1.toNat + 18446744073709551616*l.2.toNat = _ at hl
  change m.1.toNat + 18446744073709551616*m.2.toNat = _ at hm
  change n.1.toNat + 18446744073709551616*n.2.toNat = _ at hn
  change h.1.toNat + 18446744073709551616*h.2.toNat = y.2.toNat + 0 + n.2.toNat at hh
  change k.1.toNat + 18446744073709551616*k.2.toNat = h.1.toNat + 0 + m.2.toNat at hk
  change y.2.toNat < 18446744073709551616 - 1 at hylt
  change l.1.toNat + 18446744073709551616*n.1.toNat + 18446744073709551616^2*k.1.toNat + 18446744073709551616^3*k.2.toNat = _
  clear_value x y l m n h k
  change l.1.toNat + 18446744073709551616*n.1.toNat + 18446744073709551616^2*k.1.toNat +
      18446744073709551616^3*k.2.toNat =
      c0.toNat + 18446744073709551616*c1.toNat + a.toNat*b.toNat + 18446744073709551616*(next.toNat*b.toNat)
  have hzero : h.2.toNat = 0 := by
    clear hx hy hl hm hn hk
    omega
  omega

def mergeTop (c0 c1 old0 old1 : BitVec 64) (old2 : Bool) (a b : BitVec 64) : TopWords :=
  let x := product64 a b
  let h := add64 c1 old1
  let top := adc64 (BitVec.ofNat 64 old2.toNat) 0 h.2
  let l := add64 c0 old0
  let m := adc64 h.1 0 l.2
  let n := add64 m.1 x.1
  let j := adc64 x.2 0 n.2
  let k := adc64 j.1 top.1 m.2
  ⟨l.1, n.1, k.1, k.2⟩

theorem mergeTop_value (c0 c1 old0 old1 : BitVec 64) (old2 : Bool) (a b : BitVec 64) :
    (mergeTop c0 c1 old0 old1 old2 a b).value =
      c0.toNat + wordBase*c1.toNat + old0.toNat + wordBase*old1.toNat +
        wordBase^2*old2.toNat + wordBase*(a.toNat*b.toNat) := by
  let x := product64 a b
  let h := add64 c1 old1
  let top := adc64 (BitVec.ofNat 64 old2.toNat) 0 h.2
  let l := add64 c0 old0
  let m := adc64 h.1 0 l.2
  let n := add64 m.1 x.1
  let j := adc64 x.2 0 n.2
  let k := adc64 j.1 top.1 m.2
  have hx := product64_value a b
  have hh := add64_value c1 old1
  have ht := adc64_value (BitVec.ofNat 64 old2.toNat) 0 h.2
  have hl := add64_value c0 old0
  have hm := adc64_value h.1 0 l.2
  have hn := add64_value m.1 x.1
  have hj := adc64_value x.2 0 n.2
  have hk := adc64_value j.1 top.1 m.2
  have hxlt := product64_high_lt a b
  have hnlt := Bool.toNat_le n.2
  have hhcarry := Bool.toNat_le h.2
  have hold2 := Bool.toNat_le old2
  have hcast : (BitVec.ofNat 64 old2.toNat).toNat = old2.toNat :=
    Nat.mod_eq_of_lt (by omega)
  change x.1.toNat + 18446744073709551616*x.2.toNat = _ at hx
  change h.1.toNat + 18446744073709551616*h.2.toNat = _ at hh
  change top.1.toNat + 18446744073709551616*top.2.toNat = (BitVec.ofNat 64 old2.toNat).toNat + 0 + h.2.toNat at ht
  rw [hcast] at ht
  change l.1.toNat + 18446744073709551616*l.2.toNat = _ at hl
  change m.1.toNat + 18446744073709551616*m.2.toNat = h.1.toNat + 0 + l.2.toNat at hm
  change n.1.toNat + 18446744073709551616*n.2.toNat = _ at hn
  change j.1.toNat + 18446744073709551616*j.2.toNat = x.2.toNat + 0 + n.2.toNat at hj
  change k.1.toNat + 18446744073709551616*k.2.toNat = _ at hk
  change x.2.toNat < 18446744073709551616 - 1 at hxlt
  change l.1.toNat + 18446744073709551616*n.1.toNat + 18446744073709551616^2*k.1.toNat + 18446744073709551616^3*k.2.toNat = _
  clear_value x h top l m n j k
  change l.1.toNat + 18446744073709551616*n.1.toNat + 18446744073709551616^2*k.1.toNat +
      18446744073709551616^3*k.2.toNat =
      c0.toNat + 18446744073709551616*c1.toNat + old0.toNat + 18446744073709551616*old1.toNat +
        18446744073709551616^2*old2.toNat + 18446744073709551616*(a.toNat*b.toNat)
  have htzero : top.2.toNat = 0 := by
    clear hx hh hl hm hn hj hk
    omega
  have hjzero : j.2.toNat = 0 := by
    clear hx hh ht hl hm hn hk
    omega
  omega

structure FinalTop where
  low : BitVec 64
  mid : BitVec 64
  high : BitVec 64
  highBeforeCarry : BitVec 64
  carry : Bool

def finishTop (c0 c1 old0 old1 : BitVec 64) (old2 : Bool) : FinalTop :=
  let h := add64 c1 old1
  let top := adc64 (BitVec.ofNat 64 old2.toNat) 0 h.2
  let l := add64 c0 old0
  let m := adc64 h.1 0 l.2
  let n := adc64 top.1 0 m.2
  ⟨l.1, m.1, n.1, top.1, m.2⟩

theorem finishTop_value (c0 c1 old0 old1 : BitVec 64) (old2 : Bool) :
    let r := finishTop c0 c1 old0 old1 old2
    r.low.toNat + wordBase*r.mid.toNat + wordBase^2*r.high.toNat =
      c0.toNat + wordBase*c1.toNat + old0.toNat + wordBase*old1.toNat + wordBase^2*old2.toNat := by
  let h := add64 c1 old1
  let top := adc64 (BitVec.ofNat 64 old2.toNat) 0 h.2
  let l := add64 c0 old0
  let m := adc64 h.1 0 l.2
  let n := adc64 top.1 0 m.2
  have hh := add64_value c1 old1
  have ht := adc64_value (BitVec.ofNat 64 old2.toNat) 0 h.2
  have hl := add64_value c0 old0
  have hm := adc64_value h.1 0 l.2
  have hn := adc64_value top.1 0 m.2
  have hhcarry := Bool.toNat_le h.2
  have hmcarry := Bool.toNat_le m.2
  have hold2 := Bool.toNat_le old2
  have hcast : (BitVec.ofNat 64 old2.toNat).toNat = old2.toNat :=
    Nat.mod_eq_of_lt (by omega)
  change h.1.toNat + 18446744073709551616*h.2.toNat = _ at hh
  change top.1.toNat + 18446744073709551616*top.2.toNat = (BitVec.ofNat 64 old2.toNat).toNat + 0 + h.2.toNat at ht
  rw [hcast] at ht
  change l.1.toNat + 18446744073709551616*l.2.toNat = _ at hl
  change m.1.toNat + 18446744073709551616*m.2.toNat = h.1.toNat + 0 + l.2.toNat at hm
  change n.1.toNat + 18446744073709551616*n.2.toNat = top.1.toNat + 0 + m.2.toNat at hn
  change l.1.toNat + 18446744073709551616*m.1.toNat + 18446744073709551616^2*n.1.toNat = _
  clear_value h top l m n
  change l.1.toNat + 18446744073709551616*m.1.toNat + 18446744073709551616^2*n.1.toNat =
      c0.toNat + 18446744073709551616*c1.toNat + old0.toNat + 18446744073709551616*old1.toNat +
        18446744073709551616^2*old2.toNat
  have htzero : top.2.toNat = 0 := by
    clear hh hl hm hn
    omega
  have hnzero : n.2.toNat = 0 := by
    clear hh hl hm
    omega
  omega

end P256.Proofs.Sec1.SquareRoot.Montgomery
