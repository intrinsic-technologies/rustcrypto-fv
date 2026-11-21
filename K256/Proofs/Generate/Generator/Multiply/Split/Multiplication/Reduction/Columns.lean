import K256.Proofs.Generate.Generator.Multiply.Split.WideProduct
import K256.Proofs.Common.Arithmetic.Carry
import K256.Proofs.Common.Field.WordOps

namespace K256.Proofs.Generate.Generator.Multiply.Split.Reduction

open Standards.SECG.DomainParameters.Secp256k1
open K256.Proofs.Common.Invert.LinearCombination
open X86Proofs K256.Proofs.Common.Arithmetic

abbrev complementLo : BitVec 64 := 0x402da1732fc9bebf
abbrev complementHi : BitVec 64 := 0x4551231950b75fc4

def carryWord (c : Bool) : BitVec 64 := BitVec.ofNat 64 c.toNat

theorem carryWord_value (c : Bool) : (carryWord c).toNat = c.toNat := by
  cases c <;> rfl

theorem carry_le_one (c : Bool) : c.toNat ≤ 1 := by cases c <;> decide

structure LowColumns where
  low : BitVec 64
  next : BitVec 64
  carry : BitVec 64

def lowColumns (a b x y : BitVec 64) : LowColumns :=
  let p := mulResult x complementLo
  let q := mulResult y complementLo
  let t := mulResult x complementHi
  let u := addSpec p.1 a
  let v := adcSpec u.2.CF p.2 b
  let hi := adcSpec v.2.CF t.2 q.2
  let l := addSpec v.1 q.1
  let r := addSpec l.1 t.1
  let c := adcSpec r.2.CF (carryWord l.2.CF) hi.1
  ⟨u.1,r.1,c.1⟩

theorem lowColumns_value (a b x y : BitVec 64) :
    let k := lowColumns a b x y
    k.low.toNat + 2^64 * (k.next.toNat + 2^64 * k.carry.toNat) =
      a.toNat + x.toNat * complementLo.toNat +
        2^64 * (b.toNat + y.toNat * complementLo.toNat + x.toNat * complementHi.toNat) := by
  generalize he : lowColumns a b x y = k
  unfold lowColumns at he
  extract_lets p q t u v hi l r c at he
  subst k
  dsimp only
  have hp : p.1.toNat + 2^64*p.2.toNat = x.toNat * complementLo.toNat :=
    Common.Field.mulResult_toNat_add _ _
  have hq : q.1.toNat + 2^64*q.2.toNat = y.toNat * complementLo.toNat :=
    Common.Field.mulResult_toNat_add _ _
  have ht : t.1.toNat + 2^64*t.2.toNat = x.toNat * complementHi.toNat :=
    Common.Field.mulResult_toNat_add _ _
  have hu : u.1.toNat + 2^64*u.2.CF.toNat = p.1.toNat + a.toNat :=
    Carry.add_carry _ _
  have hv : v.1.toNat + 2^64*v.2.CF.toNat = p.2.toNat + b.toNat + u.2.CF.toNat :=
    Carry.adc_carry _ _ _
  have hhi : hi.1.toNat + 2^64*hi.2.CF.toNat = t.2.toNat + q.2.toNat + v.2.CF.toNat :=
    Carry.adc_carry _ _ _
  have hl : l.1.toNat + 2^64*l.2.CF.toNat = v.1.toNat + q.1.toNat :=
    Carry.add_carry _ _
  have hr : r.1.toNat + 2^64*r.2.CF.toNat = l.1.toNat + t.1.toNat :=
    Carry.add_carry _ _
  have hc : c.1.toNat + 2^64*c.2.CF.toNat = (carryWord l.2.CF).toNat + hi.1.toNat + r.2.CF.toNat :=
    Carry.adc_carry _ _ _

  rw [carryWord_value] at hc
  have hx := x.isLt
  have hy := y.isLt
  have hmod₀ : complementLo.toNat = 0x402da1732fc9bebf := rfl
  have hmod₁ : complementHi.toNat = 0x4551231950b75fc4 := rfl
  simp only [hmod₀, hmod₁] at hp hq ht ⊢
  have hvbit := carry_le_one v.2.CF
  have hlbit := carry_le_one l.2.CF
  have hrbit := carry_le_one r.2.CF
  have hi0 : hi.2.CF.toNat = 0 := by omega
  have c0 : c.2.CF.toNat = 0 := by omega
  omega

structure Column where
  low : BitVec 64
  carry : BitVec 64

def middleColumn (a incoming x y z : BitVec 64) : Column :=
  let u := addSpec incoming a
  let p := mulResult x complementLo
  let t := mulResult y complementHi
  let hi := addSpec t.2 p.2
  let v := addSpec p.1 u.1
  let q := adcSpec v.2.CF hi.1 (carryWord u.2.CF)
  let l := addSpec v.1 t.1
  let r := addSpec l.1 z
  let c := adcSpec r.2.CF (carryWord l.2.CF) q.1
  ⟨r.1,c.1⟩

theorem middleColumn_value (a incoming x y z : BitVec 64) :
    let k := middleColumn a incoming x y z
    k.low.toNat + 2^64*k.carry.toNat = a.toNat + incoming.toNat +
      x.toNat * complementLo.toNat + y.toNat * complementHi.toNat + z.toNat := by
  generalize he : middleColumn a incoming x y z = k
  unfold middleColumn at he
  extract_lets u p t hi v q l r c at he
  subst k
  dsimp only
  have hu : u.1.toNat + 2^64*u.2.CF.toNat = incoming.toNat + a.toNat :=
    Carry.add_carry _ _
  have hp : p.1.toNat + 2^64*p.2.toNat = x.toNat * complementLo.toNat :=
    Common.Field.mulResult_toNat_add _ _
  have ht : t.1.toNat + 2^64*t.2.toNat = y.toNat * complementHi.toNat :=
    Common.Field.mulResult_toNat_add _ _
  have hhi : hi.1.toNat + 2^64*hi.2.CF.toNat = t.2.toNat + p.2.toNat :=
    Carry.add_carry _ _
  have hv : v.1.toNat + 2^64*v.2.CF.toNat = p.1.toNat + u.1.toNat :=
    Carry.add_carry _ _
  have hq : q.1.toNat + 2^64*q.2.CF.toNat = hi.1.toNat + (carryWord u.2.CF).toNat + v.2.CF.toNat :=
    Carry.adc_carry _ _ _
  have hl : l.1.toNat + 2^64*l.2.CF.toNat = v.1.toNat + t.1.toNat :=
    Carry.add_carry _ _
  have hr : r.1.toNat + 2^64*r.2.CF.toNat = l.1.toNat + z.toNat :=
    Carry.add_carry _ _
  have hc : c.1.toNat + 2^64*c.2.CF.toNat = (carryWord l.2.CF).toNat + q.1.toNat + r.2.CF.toNat :=
    Carry.adc_carry _ _ _
  have halt := a.isLt
  have hincominglt := incoming.isLt
  have hxlt := x.isLt
  have hylt := y.isLt
  have hzlt := z.isLt
  have hlbit := carry_le_one l.2.CF
  have hrbit := carry_le_one r.2.CF
  have hubit := carry_le_one u.2.CF
  have hvbit := carry_le_one v.2.CF
  clear_value c r l q v hi t p u
  simp only [carryWord_value, show complementLo.toNat = 0x402da1732fc9bebf from rfl,
    show complementHi.toNat = 0x4551231950b75fc4 from rfl] at *
  have hi0 : hi.2.CF.toNat = 0 := by omega
  have q0 : q.2.CF.toNat = 0 := by omega
  have c0 : c.2.CF.toNat = 0 := by omega
  omega

def upperColumns (incoming x y : BitVec 64) : LowColumns :=
  let p := mulResult y complementHi
  let l := addSpec p.1 incoming
  let r := addSpec l.1 x
  let c := adcSpec r.2.CF (carryWord l.2.CF) p.2
  let t := addSpec c.1 y
  ⟨r.1,t.1,carryWord t.2.CF⟩

theorem upperColumns_value (incoming x y : BitVec 64) :
    let k := upperColumns incoming x y
    k.low.toNat + 2^64*(k.next.toNat + 2^64*k.carry.toNat) =
      incoming.toNat + x.toNat + y.toNat*complementHi.toNat + 2^64*y.toNat := by
  generalize he : upperColumns incoming x y = k
  unfold upperColumns at he
  extract_lets p l r c t at he
  subst k
  dsimp only
  have hp : p.1.toNat + 2^64*p.2.toNat = y.toNat * complementHi.toNat :=
    Common.Field.mulResult_toNat_add _ _
  have hl : l.1.toNat + 2^64*l.2.CF.toNat = p.1.toNat + incoming.toNat :=
    Carry.add_carry _ _
  have hr : r.1.toNat + 2^64*r.2.CF.toNat = l.1.toNat + x.toNat :=
    Carry.add_carry _ _
  have hc : c.1.toNat + 2^64*c.2.CF.toNat = (carryWord l.2.CF).toNat + p.2.toNat + r.2.CF.toNat :=
    Carry.adc_carry _ _ _
  have ht : t.1.toNat + 2^64*t.2.CF.toNat = c.1.toNat + y.toNat :=
    Carry.add_carry _ _
  have hincominglt := incoming.isLt
  have hxlt := x.isLt
  have hylt := y.isLt
  have hlbit := carry_le_one l.2.CF
  have hrbit := carry_le_one r.2.CF
  clear_value t c r l p
  simp only [carryWord_value, show complementHi.toNat = 0x4551231950b75fc4 from rfl] at *
  have c0 : c.2.CF.toNat = 0 := by omega
  omega

end K256.Proofs.Generate.Generator.Multiply.Split.Reduction
