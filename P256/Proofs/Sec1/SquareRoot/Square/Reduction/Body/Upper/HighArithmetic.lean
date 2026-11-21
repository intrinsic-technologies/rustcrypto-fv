import P256.Proofs.Field.Montgomery.Reduction.Arithmetic

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Upper

open P256.Proofs.Field.Montgomery

attribute [local irreducible] add64 adc64 product64

def highWords (a upper extra carry : BitVec 64) (middleCarry : Bool) :
    BitVec 64 × (BitVec 64 × Bool) :=
  let d := add64 upper extra
  let p3 := product64 0xffffffff00000001 a
  let q := add64 (BitVec.ofNat 64 middleCarry.toNat) d.1
  let r := add64 q.1 p3.1
  let rh := adc64 (BitVec.ofNat 64 q.2.toNat) p3.2 r.2
  let top := adc64 carry rh.1 d.2
  (r.1, top)

theorem highWords_value (a upper extra carry : BitVec 64) (middleCarry : Bool) :
    (highWords a upper extra carry middleCarry).1.toNat +
      wordBase*(highWords a upper extra carry middleCarry).2.1.toNat +
      wordBase^2*(highWords a upper extra carry middleCarry).2.2.toNat =
        middleCarry.toNat + upper.toNat + extra.toNat +
          0xffffffff00000001*a.toNat + wordBase*carry.toNat := by
  dsimp only [highWords]
  generalize eq_d : add64 upper extra = d
  generalize eq_p3 : product64 0xffffffff00000001 a = p3
  generalize eq_q : add64 (BitVec.ofNat 64 middleCarry.toNat) d.1 = q
  generalize eq_r : add64 q.1 p3.1 = r
  generalize eq_rh : adc64 (BitVec.ofNat 64 q.2.toNat) p3.2 r.2 = rh
  generalize eq_top : adc64 carry rh.1 d.2 = top
  have hd := add64_value upper extra
  rw [eq_d] at hd
  have hp3 := product64_value 0xffffffff00000001 a
  rw [eq_p3] at hp3
  have hq := add64_value (BitVec.ofNat 64 middleCarry.toNat) d.1
  rw [eq_q] at hq
  have hr := add64_value q.1 p3.1
  rw [eq_r] at hr
  have hrh := adc64_value (BitVec.ofNat 64 q.2.toNat) p3.2 r.2
  rw [eq_rh] at hrh
  have ht := adc64_value carry rh.1 d.2
  rw [eq_top] at ht
  clear eq_d eq_p3 eq_q eq_r eq_rh eq_top
  change p3.1.toNat + wordBase*p3.2.toNat = 18446744069414584321*a.toNat at hp3
  simp only [wordBase, BitVec.toNat_ofNat] at *
  have ha := a.isLt
  have hphi : p3.2.toNat < 18446744069414584321 := by
    clear hd hq hr hrh ht
    omega
  have hrhc : rh.2.toNat = 0 := by
    clear hd hp3 hq hr ht
    have := Bool.toNat_le q.2
    have := Bool.toNat_le r.2
    omega
  have := Bool.toNat_le middleCarry
  have := Bool.toNat_le q.2
  omega

end P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Upper
