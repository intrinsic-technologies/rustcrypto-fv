import P256.Proofs.Field.Schoolbook.WordSpecs
import P256.Proofs.Field.Schoolbook.Arithmetic
import P256.Proofs.Common.Field.Montgomery.Schoolbook.Words

set_option autoImplicit false

open P256.Proofs.Common.Instructions (mulHigh64)
open P256.Proofs.Common.Instructions.Carry (adcSpec)

namespace P256.Proofs.Field.Schoolbook

open P256.Proofs.Field.Montgomery (wordBase)
open P256.Proofs.Common.Field.Montgomery.Schoolbook
open X86Proofs

theorem lowerSums_firstRow (a b0 b1 b2 b3 : BitVec 64) :
    let v1 := addSpec (mulHigh64 b0 a) (b1*a)
    let v2 := adcSpec (b2*a) (mulHigh64 b1 a) (BitVec.ofBool v1.2.CF)
    let v3 := adcSpec (b3*a) (mulHigh64 b2 a) (BitVec.ofBool v2.2.CF)
    firstRow (b0.toNat*a.toNat) (b1.toNat*a.toNat) (b2.toNat*a.toNat) (b3.toNat*a.toNat) =
      #v[(b0*a).toNat, v1.1.toNat, v2.1.toNat, v3.1.toNat,
        (mulHigh64 b3 a).toNat + v3.2.CF.toNat] := by
  dsimp only
  have p0 := mul64_toNat b0 a
  have p1 := mul64_toNat b1 a
  have p2 := mul64_toNat b2 a
  have p3 := mul64_toNat b3 a
  have h1 := addSpec_addWord (mulHigh64 b0 a) (b1*a)
  have h2 := adcSpec_addWord (b2*a) (mulHigh64 b1 a)
    (BitVec.ofBool (addSpec (mulHigh64 b0 a) (b1*a)).2.CF)
  have h3 := adcSpec_addWord (b3*a) (mulHigh64 b2 a)
    (BitVec.ofBool (adcSpec (b2*a) (mulHigh64 b1 a)
      (BitVec.ofBool (addSpec (mulHigh64 b0 a) (b1*a)).2.CF)).2.CF)
  simp only [Prod.mk.injEq] at p0 p1 p2 p3
  simp only [BitVec.toNat_ofBool] at h2 h3
  simp only [firstRow, ← p0.1, ← p0.2, ← p1.1, ← p1.2, ← p2.1, ← p2.2, ← p3.1, ← p3.2,
    ← h1, ← h2, ← h3]

theorem lowerSums_adcSpec_comm {n : Nat} (a b : BitVec n) (carry : BitVec 1) :
    adcSpec a b carry = adcSpec b a carry := by
  simp only [adcSpec, Int.add_comm]

theorem lowerSums_add_adc_addProduct (lo hi c d : BitVec 64) (carry : BitVec 1) :
    let l1 := addSpec lo c
    let h1 := adcSpec hi 0 (BitVec.ofBool l1.2.CF)
    let l2 := adcSpec l1.1 d carry
    let h2 := adcSpec h1.1 0 (BitVec.ofBool l2.2.CF)
    (l2.1.toNat, h2.1.toNat) =
      addProduct (lo.toNat + wordBase*hi.toNat) c.toNat (d.toNat + carry.toNat) := by
  have hlo : (lo.toNat + wordBase*hi.toNat) % wordBase = lo.toNat := by
    have h := lo.isLt
    dsimp only [wordBase]
    omega
  have hhi : (lo.toNat + wordBase*hi.toNat) / wordBase = hi.toNat := by
    have h := lo.isLt
    dsimp only [wordBase]
    omega
  have hl := adcSpec_addWord (addSpec lo c).1 d carry
  have he : addWord (addSpec lo c).1.toNat (d.toNat + carry.toNat) 0 =
      addWord (addSpec lo c).1.toNat d.toNat carry.toNat := by
    simp only [addWord, Nat.add_zero, Nat.add_assoc]
  have h1 := adcSpec_addWord hi 0 (BitVec.ofBool (addSpec lo c).2.CF)
  simp only [BitVec.toNat_ofBool, show (0 : BitVec 64).toNat = 0 from rfl] at h1
  have h2 := adcSpec_addWord (adcSpec hi 0 (BitVec.ofBool (addSpec lo c).2.CF)).1 0
    (BitVec.ofBool (adcSpec (addSpec lo c).1 d carry).2.CF)
  simp only [BitVec.toNat_ofBool, show (0 : BitVec 64).toNat = 0 from rfl] at h2
  simp only [addProduct, hlo, hhi, ← addSpec_addWord lo c, he, ← hl, ← h1, ← h2]

theorem lowerSums_secondRow (r0 r1 r2 r3 h4 a b0 b1 b2 b3 : BitVec 64) (saved : Bool) :
    let l1 := addSpec r1 (b0*a)
    let m2 := adcSpec (mulHigh64 b0 a) (b1*a) (BitVec.ofBool l1.2.CF)
    let n2 := adcSpec (mulHigh64 b1 a) 0 (BitVec.ofBool m2.2.CF)
    let l2 := addSpec m2.1 r2
    let c2 := adcSpec n2.1 0 (BitVec.ofBool l2.2.CF)
    let m3 := addSpec (b2*a) c2.1
    let n3 := adcSpec (mulHigh64 b2 a) 0 (BitVec.ofBool m3.2.CF)
    let l3 := addSpec m3.1 r3
    let c3 := adcSpec n3.1 0 (BitVec.ofBool l3.2.CF)
    let m4 := addSpec (b3*a) c3.1
    let n4 := adcSpec (mulHigh64 b3 a) 0 (BitVec.ofBool m4.2.CF)
    let l4 := adcSpec m4.1 h4 (BitVec.ofBool saved)
    let c4 := adcSpec n4.1 0 (BitVec.ofBool l4.2.CF)
    secondRow #v[r0.toNat, r1.toNat, r2.toNat, r3.toNat, h4.toNat + saved.toNat]
      (b0.toNat*a.toNat) (b1.toNat*a.toNat) (b2.toNat*a.toNat) (b3.toNat*a.toNat) =
      #v[r0.toNat, l1.1.toNat, l2.1.toNat, l3.1.toNat, l4.1.toNat, c4.1.toNat] := by
  dsimp only
  let l1 := addSpec r1 (b0*a)
  let m2 := adcSpec (mulHigh64 b0 a) (b1*a) (BitVec.ofBool l1.2.CF)
  let n2 := adcSpec (mulHigh64 b1 a) 0 (BitVec.ofBool m2.2.CF)
  let l2 := addSpec m2.1 r2
  let c2 := adcSpec n2.1 0 (BitVec.ofBool l2.2.CF)
  let m3 := addSpec (b2*a) c2.1
  let n3 := adcSpec (mulHigh64 b2 a) 0 (BitVec.ofBool m3.2.CF)
  let l3 := addSpec m3.1 r3
  let c3 := adcSpec n3.1 0 (BitVec.ofBool l3.2.CF)
  let m4 := addSpec (b3*a) c3.1
  let n4 := adcSpec (mulHigh64 b3 a) 0 (BitVec.ofBool m4.2.CF)
  let l4 := adcSpec m4.1 h4 (BitVec.ofBool saved)
  let c4 := adcSpec n4.1 0 (BitVec.ofBool l4.2.CF)
  change secondRow #v[r0.toNat, r1.toNat, r2.toNat, r3.toNat, h4.toNat + saved.toNat]
      (b0.toNat*a.toNat) (b1.toNat*a.toNat) (b2.toNat*a.toNat) (b3.toNat*a.toNat) =
      #v[r0.toNat, l1.1.toNat, l2.1.toNat, l3.1.toNat, l4.1.toNat, c4.1.toNat]
  have p0 := mul64_toNat b0 a
  simp only [Prod.mk.injEq] at p0
  have e1 := addSpec_addWord r1 (b0*a)
  change (l1.1.toNat, l1.2.CF.toNat) = _ at e1
  have e2 := adcSpec_addProduct (b1*a) (mulHigh64 b1 a) (mulHigh64 b0 a) r2
    (BitVec.ofBool l1.2.CF)
  rw [show (b1*a).toNat + wordBase*(mulHigh64 b1 a).toNat = b1.toNat*a.toNat from
    Montgomery.product64_value b1 a] at e2
  simp only [lowerSums_adcSpec_comm (b1*a) (mulHigh64 b0 a), BitVec.toNat_ofBool] at e2
  change (l2.1.toNat, c2.1.toNat) = _ at e2
  have e3 := addSpec_addProduct (b2*a) (mulHigh64 b2 a) c2.1 r3
  rw [show (b2*a).toNat + wordBase*(mulHigh64 b2 a).toNat = b2.toNat*a.toNat from
    Montgomery.product64_value b2 a] at e3
  change (l3.1.toNat, c3.1.toNat) = _ at e3
  have e4 := lowerSums_add_adc_addProduct (b3*a) (mulHigh64 b3 a) c3.1 h4
    (BitVec.ofBool saved)
  rw [show (b3*a).toNat + wordBase*(mulHigh64 b3 a).toNat = b3.toNat*a.toNat from
    Montgomery.product64_value b3 a] at e4
  simp only [BitVec.toNat_ofBool] at e4
  change (l4.1.toNat, c4.1.toNat) = _ at e4
  simp only [secondRow, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ, ← p0.1, ← p0.2, ← e1, ← e2, ← e3, ← e4]

end P256.Proofs.Field.Schoolbook
