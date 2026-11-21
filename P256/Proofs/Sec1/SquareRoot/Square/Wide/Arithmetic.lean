import P256.Proofs.Field.Schoolbook.WordSpecs
import P256.Proofs.Field.Schoolbook.Arithmetic
import P256.Proofs.Sec1.SquareRoot.Square.Wide.Arithmetic.DoubleTriple
import P256.Proofs.Sec1.SquareRoot.Square.Wide.Arithmetic.Shift

set_option autoImplicit false

open P256.Proofs.Field.Schoolbook (mulHigh64_toNat mulWord_bound mulWord_high_lt packEight packFour packSix)
open P256.Proofs.Field.Montgomery (wordBase product64_value)
open P256.Proofs.Common.Instructions (mulHigh64)
open P256.Proofs.Common.Instructions.Carry (adcSpec adcSpec_toNat_add_carry addSpec_toNat_add_carry)
open P256.Proofs.Common.Instructions.ShiftLeft (shldOneResult)

namespace P256.Proofs.Sec1.SquareRoot.Square.Wide


open X86Proofs

def crossWords (a : Vector (BitVec 64) 4) : Vector (BitVec 64) 6 :=
  let t1 := addSpec (a[2] * a[0]) (mulHigh64 a[0] a[1])
  let t2 := adcSpec (a[2] * a[1]) (mulHigh64 a[2] a[0]) (BitVec.ofBool t1.2.CF)
  let t3 := adcSpec (a[3] * a[1]) (mulHigh64 a[2] a[1]) (BitVec.ofBool t2.2.CF)
  let t4 := adcSpec (mulHigh64 a[3] a[1]) 0 (BitVec.ofBool t3.2.CF)
  let t5 := addSpec t2.1 (a[3] * a[0])
  let t6 := adcSpec t3.1 (mulHigh64 a[3] a[0]) (BitVec.ofBool t5.2.CF)
  let t7 := adcSpec t4.1 0 (BitVec.ofBool t6.2.CF)
  let t8 := addSpec (a[3] * a[2]) t7.1
  let t9 := adcSpec (mulHigh64 a[3] a[2]) 0 (BitVec.ofBool t8.2.CF)
  #v[a[0] * a[1], t1.1, t5.1, t6.1, t8.1, t9.1]

def squareWords (a : Vector (BitVec 64) 4) : Vector (BitVec 64) 8 :=
  let c := crossWords a
  let rsi := shldOneResult c[4] c[3]
  let r10 := shldOneResult c[2] c[1]
  let r9 := c[5] >>> 63
  let r13 := shldOneResult c[1] c[0]
  let rax := addSpec c[0] c[0]
  let rax := addSpec rax.1 (mulHigh64 a[0] a[0])
  let r13 := adcSpec r13 (a[1] * a[1]) (BitVec.ofBool rax.2.CF)
  let r11 := adcSpec (mulHigh64 a[1] a[1]) 0 (BitVec.ofBool r13.2.CF)
  let r8 := shldOneResult c[3] c[2]
  let r11 := addSpec r11.1 r10
  let r8 := adcSpec r8 (a[2] * a[2]) (BitVec.ofBool r11.2.CF)
  let r14 := adcSpec (mulHigh64 a[2] a[2]) 0 (BitVec.ofBool r8.2.CF)
  let rbx := shldOneResult c[5] c[4]
  let rbx := addSpec rbx (a[3] * a[3])
  let r15 := adcSpec (mulHigh64 a[3] a[3]) 0 (BitVec.ofBool rbx.2.CF)
  let r14 := addSpec r14.1 rsi
  let rbx := adcSpec rbx.1 0 (BitVec.ofBool r14.2.CF)
  let r15 := adcSpec r15.1 r9 (BitVec.ofBool rbx.2.CF)
  #v[a[0] * a[0], rax.1, r13.1, r11.1, r8.1, r14.1, rbx.1, r15.1]

section

attribute [local irreducible] addSpec adcSpec mulHigh64 shldOneResult

set_option maxHeartbeats 500000 in
theorem packSix_crossWords (a : Vector (BitVec 64) 4) :
    packSix ((crossWords a).map BitVec.toNat) =
      a[0].toNat * a[1].toNat + wordBase * (a[2].toNat * a[0].toNat) +
      wordBase^2 * (a[2].toNat * a[1].toNat + a[3].toNat * a[0].toNat) +
      wordBase^3 * (a[3].toNat * a[1].toNat) +
      wordBase^4 * (a[3].toNat * a[2].toNat) := by
  let t1 := addSpec (a[2] * a[0]) (mulHigh64 a[0] a[1])
  let t2 := adcSpec (a[2] * a[1]) (mulHigh64 a[2] a[0]) (BitVec.ofBool t1.2.CF)
  let t3 := adcSpec (a[3] * a[1]) (mulHigh64 a[2] a[1]) (BitVec.ofBool t2.2.CF)
  let t4 := adcSpec (mulHigh64 a[3] a[1]) 0 (BitVec.ofBool t3.2.CF)
  let t5 := addSpec t2.1 (a[3] * a[0])
  let t6 := adcSpec t3.1 (mulHigh64 a[3] a[0]) (BitVec.ofBool t5.2.CF)
  let t7 := adcSpec t4.1 0 (BitVec.ofBool t6.2.CF)
  let t8 := addSpec (a[3] * a[2]) t7.1
  let t9 := adcSpec (mulHigh64 a[3] a[2]) 0 (BitVec.ofBool t8.2.CF)
  have hresult : crossWords a = #v[a[0]*a[1], t1.1, t5.1, t6.1, t8.1, t9.1] := rfl
  have ht1 := addSpec_toNat_add_carry (a[2] * a[0]) (mulHigh64 a[0] a[1])
  change t1.1.toNat + 2^64 * t1.2.CF.toNat = _ at ht1
  have ht2 := adcSpec_toNat_add_carry (a[2] * a[1]) (mulHigh64 a[2] a[0]) (BitVec.ofBool t1.2.CF)
  change t2.1.toNat + 2^64 * t2.2.CF.toNat = _ at ht2
  have ht3 := adcSpec_toNat_add_carry (a[3] * a[1]) (mulHigh64 a[2] a[1]) (BitVec.ofBool t2.2.CF)
  change t3.1.toNat + 2^64 * t3.2.CF.toNat = _ at ht3
  have ht4 := adcSpec_toNat_add_carry (mulHigh64 a[3] a[1]) 0 (BitVec.ofBool t3.2.CF)
  change t4.1.toNat + 2^64 * t4.2.CF.toNat = _ at ht4
  have ht5 := addSpec_toNat_add_carry t2.1 (a[3] * a[0])
  change t5.1.toNat + 2^64 * t5.2.CF.toNat = _ at ht5
  have ht6 := adcSpec_toNat_add_carry t3.1 (mulHigh64 a[3] a[0]) (BitVec.ofBool t5.2.CF)
  change t6.1.toNat + 2^64 * t6.2.CF.toNat = _ at ht6
  have ht7 := adcSpec_toNat_add_carry t4.1 0 (BitVec.ofBool t6.2.CF)
  change t7.1.toNat + 2^64 * t7.2.CF.toNat = _ at ht7
  have ht8 := addSpec_toNat_add_carry (a[3] * a[2]) t7.1
  change t8.1.toNat + 2^64 * t8.2.CF.toNat = _ at ht8
  have ht9 := adcSpec_toNat_add_carry (mulHigh64 a[3] a[2]) 0 (BitVec.ofBool t8.2.CF)
  change t9.1.toNat + 2^64 * t9.2.CF.toNat = _ at ht9
  clear_value t1 t2 t3 t4 t5 t6 t7 t8 t9
  have hp01 := product64_value a[0] a[1]
  have hp20 := product64_value a[2] a[0]
  have hp21 := product64_value a[2] a[1]
  have hp30 := product64_value a[3] a[0]
  have hp31 := product64_value a[3] a[1]
  have hp32 := product64_value a[3] a[2]
  simp only [P256.Proofs.Field.Montgomery.product64] at hp01 hp20 hp21 hp30 hp31 hp32
  have hh21 := mulWord_high_lt a[2].isLt a[1].isLt
  rw [← mulHigh64_toNat] at hh21
  have hh30 := mulWord_high_lt a[3].isLt a[0].isLt
  rw [← mulHigh64_toNat] at hh30
  have hh32 := mulWord_high_lt a[3].isLt a[2].isLt
  rw [← mulHigh64_toNat] at hh32
  have h13bound := mulWord_bound a[3].isLt a[1].isLt
  have hc2 := Bool.toNat_le t2.2.CF
  have hc5 := Bool.toNat_le t5.2.CF
  have hc8 := Bool.toNat_le t8.2.CF
  simp only [BitVec.toNat_ofBool] at ht2 ht3 ht4 ht6 ht7 ht9
  simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.zero_mod, Nat.add_zero] at ht4 ht7 ht9
  have hc47 : t4.2.CF.toNat = 0 ∧ t7.2.CF.toNat = 0 := by
    dsimp only [wordBase] at *
    omega
  have hc9 : t9.2.CF.toNat = 0 := by
    dsimp only [wordBase] at *
    omega
  rw [hresult]
  simp only [packSix, Vector.getElem_map]
  change (a[0]*a[1]).toNat + wordBase*t1.1.toNat + wordBase^2*t5.1.toNat +
    wordBase^3*t6.1.toNat + wordBase^4*t8.1.toNat + wordBase^5*t9.1.toNat = _
  dsimp only [wordBase] at *
  omega

set_option maxHeartbeats 500000 in
theorem squareWords_value (a : Vector (BitVec 64) 4) :
    ∃ k : Nat, packEight ((squareWords a).map BitVec.toNat) + wordBase^8*k =
      a[0].toNat*a[0].toNat + wordBase^2*(a[1].toNat*a[1].toNat) +
      wordBase^4*(a[2].toNat*a[2].toNat) + wordBase^6*(a[3].toNat*a[3].toNat) +
      2*wordBase*packSix ((crossWords a).map BitVec.toNat) := by
  let c := crossWords a
  let s4 := shldOneResult c[4] c[3]
  let s2 := shldOneResult c[2] c[1]
  let top := c[5] >>> 63
  let s1 := shldOneResult c[1] c[0]
  let d0 := addSpec c[0] c[0]
  let r1 := addSpec d0.1 (mulHigh64 a[0] a[0])
  let r2 := adcSpec s1 (a[1]*a[1]) (BitVec.ofBool r1.2.CF)
  let h3 := adcSpec (mulHigh64 a[1] a[1]) 0 (BitVec.ofBool r2.2.CF)
  let s3 := shldOneResult c[3] c[2]
  let r3 := addSpec h3.1 s2
  let r4 := adcSpec s3 (a[2]*a[2]) (BitVec.ofBool r3.2.CF)
  let h5 := adcSpec (mulHigh64 a[2] a[2]) 0 (BitVec.ofBool r4.2.CF)
  let s5 := shldOneResult c[5] c[4]
  let l6 := addSpec s5 (a[3]*a[3])
  let h7 := adcSpec (mulHigh64 a[3] a[3]) 0 (BitVec.ofBool l6.2.CF)
  let r5 := addSpec h5.1 s4
  let r6 := adcSpec l6.1 0 (BitVec.ofBool r5.2.CF)
  let r7 := adcSpec h7.1 top (BitVec.ofBool r6.2.CF)
  have hresult : squareWords a =
      #v[a[0]*a[0],r1.1,r2.1,r3.1,r4.1,r5.1,r6.1,r7.1] := rfl
  change ∃ k : Nat, packEight ((squareWords a).map BitVec.toNat) + wordBase^8*k =
      a[0].toNat*a[0].toNat + wordBase^2*(a[1].toNat*a[1].toNat) +
      wordBase^4*(a[2].toNat*a[2].toNat) + wordBase^6*(a[3].toNat*a[3].toNat) +
      2*wordBase*packSix (c.map BitVec.toNat)
  have hs1 := shldOneResult_toNat c[1] c[0]
  change s1.toNat + wordBase * (c[1] >>> 63).toNat = _ at hs1
  have hs2 := shldOneResult_toNat c[2] c[1]
  change s2.toNat + wordBase * (c[2] >>> 63).toNat = _ at hs2
  have hs3 := shldOneResult_toNat c[3] c[2]
  change s3.toNat + wordBase * (c[3] >>> 63).toNat = _ at hs3
  have hs4 := shldOneResult_toNat c[4] c[3]
  change s4.toNat + wordBase * (c[4] >>> 63).toNat = _ at hs4
  have hs5 := shldOneResult_toNat c[5] c[4]
  change s5.toNat + wordBase * top.toNat = _ at hs5
  have hd0 := addSpec_self_toNat c[0]
  change d0.1.toNat + wordBase * (c[0] >>> 63).toNat = _ at hd0
  have h_r1 := addSpec_toNat_add_carry d0.1 (mulHigh64 a[0] a[0])
  change r1.1.toNat + 2^64 * r1.2.CF.toNat = _ at h_r1
  have h_r2 := adcSpec_toNat_add_carry s1 (a[1]*a[1]) (BitVec.ofBool r1.2.CF)
  change r2.1.toNat + 2^64 * r2.2.CF.toNat = _ at h_r2
  have h_h3 := adcSpec_toNat_add_carry (mulHigh64 a[1] a[1]) 0 (BitVec.ofBool r2.2.CF)
  change h3.1.toNat + 2^64 * h3.2.CF.toNat = _ at h_h3
  have h_r3 := addSpec_toNat_add_carry h3.1 s2
  change r3.1.toNat + 2^64 * r3.2.CF.toNat = _ at h_r3
  have h_r4 := adcSpec_toNat_add_carry s3 (a[2]*a[2]) (BitVec.ofBool r3.2.CF)
  change r4.1.toNat + 2^64 * r4.2.CF.toNat = _ at h_r4
  have h_h5 := adcSpec_toNat_add_carry (mulHigh64 a[2] a[2]) 0 (BitVec.ofBool r4.2.CF)
  change h5.1.toNat + 2^64 * h5.2.CF.toNat = _ at h_h5
  have h_l6 := addSpec_toNat_add_carry s5 (a[3]*a[3])
  change l6.1.toNat + 2^64 * l6.2.CF.toNat = _ at h_l6
  have h_h7 := adcSpec_toNat_add_carry (mulHigh64 a[3] a[3]) 0 (BitVec.ofBool l6.2.CF)
  change h7.1.toNat + 2^64 * h7.2.CF.toNat = _ at h_h7
  have h_r5 := addSpec_toNat_add_carry h5.1 s4
  change r5.1.toNat + 2^64 * r5.2.CF.toNat = _ at h_r5
  have h_r6 := adcSpec_toNat_add_carry l6.1 0 (BitVec.ofBool r5.2.CF)
  change r6.1.toNat + 2^64 * r6.2.CF.toNat = _ at h_r6
  have h_r7 := adcSpec_toNat_add_carry h7.1 top (BitVec.ofBool r6.2.CF)
  change r7.1.toNat + 2^64 * r7.2.CF.toNat = _ at h_r7
  clear_value c s4 s2 top s1 d0 r1 r2 h3 s3 r3 r4 h5 s5 l6 h7 r5 r6 r7
  have hp0 := product64_value a[0] a[0]
  have hp1 := product64_value a[1] a[1]
  have hp2 := product64_value a[2] a[2]
  have hp3 := product64_value a[3] a[3]
  simp only [P256.Proofs.Field.Montgomery.product64] at hp0 hp1 hp2 hp3
  have hh1 := mulWord_high_lt a[1].isLt a[1].isLt
  rw [← mulHigh64_toNat] at hh1
  have hc1 := Bool.toNat_le r2.2.CF
  have hh2 := mulWord_high_lt a[2].isLt a[2].isLt
  rw [← mulHigh64_toNat] at hh2
  have hc2 := Bool.toNat_le r4.2.CF
  have hh3 := mulWord_high_lt a[3].isLt a[3].isLt
  rw [← mulHigh64_toNat] at hh3
  have hc3 := Bool.toNat_le l6.2.CF
  simp only [BitVec.toNat_ofBool] at h_r2 h_h3 h_r4 h_h5 h_h7 h_r6 h_r7
  simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.zero_mod, Nat.add_zero] at h_h3 h_h5 h_h7 h_r6
  have hc : h3.2.CF.toNat = 0 ∧ h5.2.CF.toNat = 0 ∧ h7.2.CF.toNat = 0 := by
    dsimp only [wordBase] at *
    omega
  refine ⟨r7.2.CF.toNat, ?_⟩
  rw [hresult]
  simp only [packEight, packSix, Vector.getElem_map]
  change (a[0]*a[0]).toNat + wordBase*r1.1.toNat + wordBase^2*r2.1.toNat +
      wordBase^3*r3.1.toNat + wordBase^4*r4.1.toNat + wordBase^5*r5.1.toNat +
      wordBase^6*r6.1.toNat + wordBase^7*r7.1.toNat + wordBase^8*r7.2.CF.toNat = _
  dsimp only [wordBase] at *
  omega

theorem squareWords_correct (a : Vector (BitVec 64) 4) :
    packEight ((squareWords a).map BitVec.toNat) =
      (packFour (a.map BitVec.toNat))^2 := by
  obtain ⟨k,hk⟩ := squareWords_value a
  have hexpand :
      a[0].toNat*a[0].toNat + wordBase^2*(a[1].toNat*a[1].toNat) +
      wordBase^4*(a[2].toNat*a[2].toNat) + wordBase^6*(a[3].toNat*a[3].toNat) +
      2*wordBase*packSix ((crossWords a).map BitVec.toNat) =
        (packFour (a.map BitVec.toNat))^2 := by
    rw [packSix_crossWords]
    simp only [packFour, Vector.getElem_map]
    grind only
  rw [hexpand] at hk
  have hsmall : packFour (a.map BitVec.toNat) < wordBase^4 := by
    have h0 := a[0].isLt
    have h1 := a[1].isLt
    have h2 := a[2].isLt
    have h3 := a[3].isLt
    simp only [packFour, Vector.getElem_map, wordBase]
    omega
  have hsquare : (packFour (a.map BitVec.toNat))^2 < wordBase^8 := by
    have h := Nat.mul_self_lt_mul_self hsmall
    simpa only [Nat.pow_two, ← Nat.pow_add] using h
  have hk0 : k = 0 := by
    dsimp only [wordBase] at hk hsquare
    omega
  simpa only [hk0, Nat.mul_zero, Nat.add_zero] using hk

end

end P256.Proofs.Sec1.SquareRoot.Square.Wide
