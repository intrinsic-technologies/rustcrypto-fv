import P256.Proofs.Field.Schoolbook.UpperSums
import P256.Proofs.Field.Schoolbook.Store
import P256.Proofs.Field.Schoolbook.WordSpecs
import P256.Proofs.Field.Schoolbook.Arithmetic

set_option autoImplicit false

open P256.Proofs.Common.Instructions (mulHigh64)
open P256.Proofs.Common.Instructions.Carry (adcSpec)

namespace P256.Proofs.Field.Schoolbook

open P256.Proofs.Field.Montgomery (wordBase)
open P256.Proofs.Common.Field.Montgomery.Schoolbook

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

private theorem addSpec_comm (a b : BitVec 64) : addSpec a b = addSpec b a := by
  simp only [addSpec, BitVec.add_comm, Nat.add_comm, Int.add_comm]

private theorem adcSpec_comm (a b : BitVec 64) (c : BitVec 1) :
    adcSpec a b c = adcSpec b a c := by
  simp only [adcSpec, Int.add_comm]

private def addProductWords (lo hi c d : BitVec 64) : BitVec 64 × BitVec 64 :=
  let l1 := addSpec lo c
  let h1 := adcSpec hi 0 (BitVec.ofBool l1.2.CF)
  let l2 := addSpec l1.1 d
  let h2 := adcSpec h1.1 0 (BitVec.ofBool l2.2.CF)
  (l2.1, h2.1)

private def adcProductWords (lo hi c d : BitVec 64) (carry : Bool) : BitVec 64 × BitVec 64 :=
  let l1 := adcSpec lo c (BitVec.ofBool carry)
  let h1 := adcSpec hi 0 (BitVec.ofBool l1.2.CF)
  let l2 := addSpec l1.1 d
  let h2 := adcSpec h1.1 0 (BitVec.ofBool l2.2.CF)
  (l2.1, h2.1)

private def orderedAdd (flip : Bool) (a b : BitVec 64) :=
  if flip then addSpec b a else addSpec a b

private def orderedAdc (flip : Bool) (a b : BitVec 64) (c : BitVec 1) :=
  if flip then adcSpec b a c else adcSpec a b c

private theorem orderedAdd_eq (flip : Bool) (a b : BitVec 64) :
    orderedAdd flip a b = addSpec a b := by
  cases flip <;> simp only [orderedAdd, Bool.false_eq_true, ↓reduceIte, addSpec_comm]

private theorem orderedAdc_eq (flip : Bool) (a b : BitVec 64) (c : BitVec 1) :
    orderedAdc flip a b c = adcSpec a b c := by
  cases flip <;> simp only [orderedAdc, Bool.false_eq_true, ↓reduceIte, adcSpec_comm]

private def orderedProduct (first second : Bool) (lo hi c d : BitVec 64) : BitVec 64 × BitVec 64 :=
  let l1 := orderedAdd first lo c
  let h1 := adcSpec hi 0 (BitVec.ofBool l1.2.CF)
  let l2 := orderedAdd second l1.1 d
  let h2 := adcSpec h1.1 0 (BitVec.ofBool l2.2.CF)
  (l2.1, h2.1)

private def orderedAdcProduct (first second : Bool) (lo hi c d : BitVec 64) (carry : Bool) : BitVec 64 × BitVec 64 :=
  let l1 := orderedAdc first lo c (BitVec.ofBool carry)
  let h1 := adcSpec hi 0 (BitVec.ofBool l1.2.CF)
  let l2 := orderedAdd second l1.1 d
  let h2 := adcSpec h1.1 0 (BitVec.ofBool l2.2.CF)
  (l2.1, h2.1)

private theorem orderedProduct_eq (first second : Bool) (lo hi c d : BitVec 64) :
    orderedProduct first second lo hi c d = addProductWords lo hi c d := by
  simp only [orderedProduct, orderedAdd_eq, addProductWords]

private theorem orderedAdcProduct_eq (first second : Bool) (lo hi c d : BitVec 64) (carry : Bool) :
    orderedAdcProduct first second lo hi c d carry = adcProductWords lo hi c d carry := by
  simp only [orderedAdcProduct, orderedAdd_eq, orderedAdc_eq, adcProductWords]

private theorem addProductWords_nat (lo hi c d : BitVec 64) :
    addProduct (lo.toNat+wordBase*hi.toNat) c.toNat d.toNat =
      ((addProductWords lo hi c d).1.toNat, (addProductWords lo hi c d).2.toNat) :=
  (addSpec_addProduct lo hi c d).symm

private theorem adcProductWords_nat (lo hi c d : BitVec 64) (carry : Bool) :
    addProduct (lo.toNat+wordBase*hi.toNat) (c.toNat+carry.toNat) d.toNat =
      ((adcProductWords lo hi c d carry).1.toNat, (adcProductWords lo hi c d carry).2.toNat) := by
  simpa only [BitVec.toNat_ofBool, adcProductWords] using (adcSpec_addProduct lo hi c d (BitVec.ofBool carry)).symm

private def productNat (x : BitVec 64 × BitVec 64) : Nat := x.1.toNat+wordBase*x.2.toNat

private theorem productNat_low (x : BitVec 64 × BitVec 64) :
    productNat x % wordBase = x.1.toNat := by
  have h := x.1.isLt
  dsimp only [productNat, wordBase]
  omega

private theorem productNat_high (x : BitVec 64 × BitVec 64) :
    productNat x / wordBase = x.2.toNat := by
  have h := x.1.isLt
  dsimp only [productNat, wordBase]
  omega

private def lastRowsWords (r : Vector (BitVec 64) 6)
    (q p : Vector (BitVec 64 × BitVec 64) 4) : Vector (BitVec 64) 8 :=
  let v2 := addSpec q[0].1 r[2]
  let q1 := orderedAdcProduct true false q[1].1 q[1].2 q[0].2 r[3] v2.2.CF
  let v3 := addSpec q1.1 p[0].1
  let q2 := orderedProduct false false q[2].1 q[2].2 q1.2 r[4]
  let p1 := orderedAdcProduct true true p[1].1 p[1].2 p[0].2 q2.1 v3.2.CF
  let q3 := orderedProduct false false q[3].1 q[3].2 q2.2 r[5]
  let p2 := orderedProduct true true p[2].1 p[2].2 p1.2 q3.1
  let p3 := orderedProduct true false p[3].1 p[3].2 p2.2 q3.2
  #v[r[0], r[1], v2.1, v3.1, p1.1, p2.1, p3.1, p3.2]

private theorem lastRowsWords_nat (r : Vector (BitVec 64) 6)
    (q p : Vector (BitVec 64 × BitVec 64) 4) :
    (lastRowsWords r q p).map BitVec.toNat =
      lastRows (r.map BitVec.toNat) (q.map productNat) (p.map productNat) := by
  simp only [lastRows, Vector.getElem_map, productNat_low, productNat_high]
  simp only [← addSpec_addWord, productNat, adcProductWords_nat, addProductWords_nat,
    lastRowsWords, orderedProduct_eq, orderedAdcProduct_eq]
  ext i hi
  have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Vector.getElem_map] <;> rfl

private def upperRowWords (s : RamState) : Vector (BitVec 64) 6 :=
  #v[((Operand.mem (rspOf s+80) : Operand 64).read s),
    ((Operand.mem (rspOf s+24) : Operand 64).read s),
    ((Operand.mem (rspOf s+0) : Operand 64).read s),
    ((Operand.reg 8 : Operand 64).read s),
    ((Operand.reg 11 : Operand 64).read s),
    ((Operand.reg 12 : Operand 64).read s)]

private def upperQWords (s : RamState) : Vector (BitVec 64 × BitVec 64) 4 :=
  #v[(((Operand.reg 10 : Operand 64).read s), ((Operand.reg 6 : Operand 64).read s)),
    (((Operand.reg 1 : Operand 64).read s), ((Operand.reg 3 : Operand 64).read s)),
    ((((Operand.mem (rspOf s+40) : Operand 64).read s)*((Operand.reg 14 : Operand 64).read s)), (mulHigh64 ((Operand.mem (rspOf s+40) : Operand 64).read s) ((Operand.reg 14 : Operand 64).read s))),
    ((((Operand.mem (rspOf s+56) : Operand 64).read s)*((Operand.reg 14 : Operand 64).read s)), (mulHigh64 ((Operand.mem (rspOf s+56) : Operand 64).read s) ((Operand.reg 14 : Operand 64).read s)))]

private def upperPWords (s : RamState) : Vector (BitVec 64 × BitVec 64) 4 :=
  #v[(((Operand.mem (rspOf s+8) : Operand 64).read s), ((Operand.reg 9 : Operand 64).read s)),
    (((Operand.mem (rspOf s+32) : Operand 64).read s), ((Operand.reg 5 : Operand 64).read s)),
    (((Operand.mem (rspOf s+48) : Operand 64).read s), ((Operand.reg 13 : Operand 64).read s)),
    (((Operand.mem (rspOf s+16) : Operand 64).read s), ((Operand.reg 15 : Operand 64).read s))]

def upperInputRow (s : RamState) : Vector Nat 6 :=
  #v[((Operand.mem (rspOf s+80) : Operand 64).read s).toNat,
    ((Operand.mem (rspOf s+24) : Operand 64).read s).toNat,
    ((Operand.mem (rspOf s+0) : Operand 64).read s).toNat,
    ((Operand.reg 8 : Operand 64).read s).toNat,
    ((Operand.reg 11 : Operand 64).read s).toNat,
    ((Operand.reg 12 : Operand 64).read s).toNat]

def upperInputQ (s : RamState) : Vector Nat 4 :=
  #v[((Operand.reg 10 : Operand 64).read s).toNat + wordBase*((Operand.reg 6 : Operand 64).read s).toNat,
    ((Operand.reg 1 : Operand 64).read s).toNat + wordBase*((Operand.reg 3 : Operand 64).read s).toNat,
    ((Operand.mem (rspOf s+40) : Operand 64).read s).toNat*((Operand.reg 14 : Operand 64).read s).toNat,
    ((Operand.mem (rspOf s+56) : Operand 64).read s).toNat*((Operand.reg 14 : Operand 64).read s).toNat]

def upperInputP (s : RamState) : Vector Nat 4 :=
  #v[((Operand.mem (rspOf s+8) : Operand 64).read s).toNat + wordBase*((Operand.reg 9 : Operand 64).read s).toNat,
    ((Operand.mem (rspOf s+32) : Operand 64).read s).toNat + wordBase*((Operand.reg 5 : Operand 64).read s).toNat,
    ((Operand.mem (rspOf s+48) : Operand 64).read s).toNat + wordBase*((Operand.reg 13 : Operand 64).read s).toNat,
    ((Operand.mem (rspOf s+16) : Operand 64).read s).toNat + wordBase*((Operand.reg 15 : Operand 64).read s).toNat]

private theorem effect_cf {state : RamState} {flags : StatusFlags}
    (h : (StatusFlagsOutcome.ofStatusFlags flags).Allows (StatusFlags.ofRFLAGS state.RFLAGS)) :
    state.RFLAGS.extractLsb' 0 1 = BitVec.ofBool flags.CF := by
  rw [extractLsb'_one_eq_ofBool]
  exact congrArg BitVec.ofBool h.1

attribute [local irreducible] addSpec adcSpec mulHigh64

set_option maxRecDepth 2048 in
set_option maxHeartbeats 800000 in
private theorem upper_sums_words {s t u v : RamState}
    (low : (upperSumsLowEffect s).Holds s t)
    (middle : (upperSumsMiddleEffect t).Holds t u)
    (high : (upperSumsHighEffect u).Holds u v) :
    outputLimbs v = lastRowsWords (upperRowWords s) (upperQWords s) (upperPWords s) := by
  have lmem : t.external = s.external :=
    low.agrees.external (by simp [upperSumsLowEffect, Effect.components, Component.Covers])
  have l0 : (Operand.reg 0 : Operand 64).read t = (Operand.reg 0 : Operand 64).read s :=
    low.agrees.read (by simp [upperSumsLowEffect, Effect.components])
  have l1 : (Operand.reg 1 : Operand 64).read t = (Operand.reg 1 : Operand 64).read s :=
    low.agrees.read (by simp [upperSumsLowEffect, Effect.components])
  have l2 : (Operand.reg 2 : Operand 64).read t = (Operand.reg 2 : Operand 64).read s :=
    low.agrees.read (by simp [upperSumsLowEffect, Effect.components])
  have l3 := low.writes.2.2.1
  dsimp only [upperSumsLowEffect, Write.AllHold] at l3
  have l4 : (Operand.reg 4 : Operand 64).read t = (Operand.reg 4 : Operand 64).read s :=
    low.agrees.read (by simp [upperSumsLowEffect, Effect.components])
  have l5 := low.writes.2.2.2.2
  dsimp only [upperSumsLowEffect, Write.AllHold] at l5
  have l6 := low.writes.2.1
  dsimp only [upperSumsLowEffect, Write.AllHold] at l6
  have l7 : (Operand.reg 7 : Operand 64).read t = (Operand.reg 7 : Operand 64).read s :=
    low.agrees.read (by simp [upperSumsLowEffect, Effect.components])
  have l8 : (Operand.reg 8 : Operand 64).read t = (Operand.reg 8 : Operand 64).read s :=
    low.agrees.read (by simp [upperSumsLowEffect, Effect.components])
  have l9 := low.writes.2.2.2.1
  dsimp only [upperSumsLowEffect, Write.AllHold] at l9
  have l10 := low.writes.1
  dsimp only [upperSumsLowEffect, Write.AllHold] at l10
  have l11 : (Operand.reg 11 : Operand 64).read t = (Operand.reg 11 : Operand 64).read s :=
    low.agrees.read (by simp [upperSumsLowEffect, Effect.components])
  have l12 : (Operand.reg 12 : Operand 64).read t = (Operand.reg 12 : Operand 64).read s :=
    low.agrees.read (by simp [upperSumsLowEffect, Effect.components])
  have l13 : (Operand.reg 13 : Operand 64).read t = (Operand.reg 13 : Operand 64).read s :=
    low.agrees.read (by simp [upperSumsLowEffect, Effect.components])
  have l14 : (Operand.reg 14 : Operand 64).read t = (Operand.reg 14 : Operand 64).read s :=
    low.agrees.read (by simp [upperSumsLowEffect, Effect.components])
  have l15 : (Operand.reg 15 : Operand 64).read t = (Operand.reg 15 : Operand 64).read s :=
    low.agrees.read (by simp [upperSumsLowEffect, Effect.components])
  have lsp : rspOf t = rspOf s := l4
  have lread (a : BitVec 64) : (Operand.mem a : Operand 64).read t = (Operand.mem a : Operand 64).read s := by
    change memLoad t.external a 64 = memLoad s.external a 64
    rw [lmem]
  have mmem : u.external = t.external :=
    middle.agrees.external (by simp [upperSumsMiddleEffect, Effect.components, Component.Covers])
  have m0 := middle.writes.1
  dsimp only [upperSumsMiddleEffect, Write.AllHold] at m0
  have m1 := middle.writes.2.2.1
  dsimp only [upperSumsMiddleEffect, Write.AllHold] at m1
  have m2 := middle.writes.2.1
  dsimp only [upperSumsMiddleEffect, Write.AllHold] at m2
  have m3 : (Operand.reg 3 : Operand 64).read u = (Operand.reg 3 : Operand 64).read t :=
    middle.agrees.read (by simp [upperSumsMiddleEffect, Effect.components])
  have m4 : (Operand.reg 4 : Operand 64).read u = (Operand.reg 4 : Operand 64).read t :=
    middle.agrees.read (by simp [upperSumsMiddleEffect, Effect.components])
  have m5 := middle.writes.2.2.2.2.1
  dsimp only [upperSumsMiddleEffect, Write.AllHold] at m5
  have m6 : (Operand.reg 6 : Operand 64).read u = (Operand.reg 6 : Operand 64).read t :=
    middle.agrees.read (by simp [upperSumsMiddleEffect, Effect.components])
  have m7 : (Operand.reg 7 : Operand 64).read u = (Operand.reg 7 : Operand 64).read t :=
    middle.agrees.read (by simp [upperSumsMiddleEffect, Effect.components])
  have m8 := middle.writes.2.2.2.1
  dsimp only [upperSumsMiddleEffect, Write.AllHold] at m8
  have m9 : (Operand.reg 9 : Operand 64).read u = (Operand.reg 9 : Operand 64).read t :=
    middle.agrees.read (by simp [upperSumsMiddleEffect, Effect.components])
  have m10 : (Operand.reg 10 : Operand 64).read u = (Operand.reg 10 : Operand 64).read t :=
    middle.agrees.read (by simp [upperSumsMiddleEffect, Effect.components])
  have m11 : (Operand.reg 11 : Operand 64).read u = (Operand.reg 11 : Operand 64).read t :=
    middle.agrees.read (by simp [upperSumsMiddleEffect, Effect.components])
  have m12 : (Operand.reg 12 : Operand 64).read u = (Operand.reg 12 : Operand 64).read t :=
    middle.agrees.read (by simp [upperSumsMiddleEffect, Effect.components])
  have m13 := middle.writes.2.2.2.2.2
  dsimp only [upperSumsMiddleEffect, Write.AllHold] at m13
  have m14 : (Operand.reg 14 : Operand 64).read u = (Operand.reg 14 : Operand 64).read t :=
    middle.agrees.read (by simp [upperSumsMiddleEffect, Effect.components])
  have m15 : (Operand.reg 15 : Operand 64).read u = (Operand.reg 15 : Operand 64).read t :=
    middle.agrees.read (by simp [upperSumsMiddleEffect, Effect.components])
  have msp : rspOf u = rspOf t := m4
  have mread (a : BitVec 64) : (Operand.mem a : Operand 64).read u = (Operand.mem a : Operand 64).read t := by
    change memLoad u.external a 64 = memLoad t.external a 64
    rw [mmem]
  have hmem : v.external = u.external :=
    high.agrees.external (by simp [upperSumsHighEffect, Effect.components, Component.Covers])
  have h0 := high.writes.1
  dsimp only [upperSumsHighEffect, Write.AllHold] at h0
  have h1 : (Operand.reg 1 : Operand 64).read v = (Operand.reg 1 : Operand 64).read u :=
    high.agrees.read (by simp [upperSumsHighEffect, Effect.components])
  have h2 := high.writes.2.1
  dsimp only [upperSumsHighEffect, Write.AllHold] at h2
  have h3 : (Operand.reg 3 : Operand 64).read v = (Operand.reg 3 : Operand 64).read u :=
    high.agrees.read (by simp [upperSumsHighEffect, Effect.components])
  have h4 : (Operand.reg 4 : Operand 64).read v = (Operand.reg 4 : Operand 64).read u :=
    high.agrees.read (by simp [upperSumsHighEffect, Effect.components])
  have h5 : (Operand.reg 5 : Operand 64).read v = (Operand.reg 5 : Operand 64).read u :=
    high.agrees.read (by simp [upperSumsHighEffect, Effect.components])
  have h6 : (Operand.reg 6 : Operand 64).read v = (Operand.reg 6 : Operand 64).read u :=
    high.agrees.read (by simp [upperSumsHighEffect, Effect.components])
  have h7 : (Operand.reg 7 : Operand 64).read v = (Operand.reg 7 : Operand 64).read u :=
    high.agrees.read (by simp [upperSumsHighEffect, Effect.components])
  have h8 : (Operand.reg 8 : Operand 64).read v = (Operand.reg 8 : Operand 64).read u :=
    high.agrees.read (by simp [upperSumsHighEffect, Effect.components])
  have h9 : (Operand.reg 9 : Operand 64).read v = (Operand.reg 9 : Operand 64).read u :=
    high.agrees.read (by simp [upperSumsHighEffect, Effect.components])
  have h10 : (Operand.reg 10 : Operand 64).read v = (Operand.reg 10 : Operand 64).read u :=
    high.agrees.read (by simp [upperSumsHighEffect, Effect.components])
  have h11 : (Operand.reg 11 : Operand 64).read v = (Operand.reg 11 : Operand 64).read u :=
    high.agrees.read (by simp [upperSumsHighEffect, Effect.components])
  have h12 : (Operand.reg 12 : Operand 64).read v = (Operand.reg 12 : Operand 64).read u :=
    high.agrees.read (by simp [upperSumsHighEffect, Effect.components])
  have h13 := high.writes.2.2.1
  dsimp only [upperSumsHighEffect, Write.AllHold] at h13
  have h14 : (Operand.reg 14 : Operand 64).read v = (Operand.reg 14 : Operand 64).read u :=
    high.agrees.read (by simp [upperSumsHighEffect, Effect.components])
  have h15 := high.writes.2.2.2
  dsimp only [upperSumsHighEffect, Write.AllHold] at h15
  have hsp : rspOf v = rspOf u := h4
  have hread (a : BitVec 64) : (Operand.mem a : Operand 64).read v = (Operand.mem a : Operand 64).read u := by
    change memLoad v.external a 64 = memLoad u.external a 64
    rw [hmem]
  have hcf := effect_cf high.flags
  simp only [outputLimbs]
  simp only [hsp, h15, h13, h10, h8, h6, h0, hread, msp, m15, m14, m13, m12, m10, m8, m6, m5, m1, mread, lsp, l15, l14, l13, l12, l11, l10, l9, l6, l5, l3, lread, hcf]
  simp only [lastRowsWords, upperRowWords, upperQWords, upperPWords, orderedProduct, orderedAdcProduct, orderedAdd, orderedAdc, Bool.false_eq_true, ↓reduceIte]
  ext i hi
  have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem upper_sums_output {s t u v : RamState}
    (low : (upperSumsLowEffect s).Holds s t)
    (middle : (upperSumsMiddleEffect t).Holds t u)
    (high : (upperSumsHighEffect u).Holds u v) :
    (outputLimbs v).map BitVec.toNat = lastRows (upperInputRow s) (upperInputQ s) (upperInputP s) := by
  have hr : (upperRowWords s).map BitVec.toNat = upperInputRow s := by
    ext i hi
    have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Vector.getElem_map] <;> rfl
  have hq : (upperQWords s).map productNat = upperInputQ s := by
    ext i hi
    have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hc with rfl | rfl | rfl | rfl
    all_goals simp only [Vector.getElem_map]
    · rfl
    · rfl
    · exact P256.Proofs.Field.Montgomery.product64_value _ _
    · exact P256.Proofs.Field.Montgomery.product64_value _ _
  have hp : (upperPWords s).map productNat = upperInputP s := by
    ext i hi
    have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hc with rfl | rfl | rfl | rfl <;> simp only [Vector.getElem_map] <;> rfl
  rw [upper_sums_words low middle high, lastRowsWords_nat, hr, hq, hp]

end P256.Proofs.Field.Schoolbook
