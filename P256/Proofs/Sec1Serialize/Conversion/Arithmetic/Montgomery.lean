import P256.Proofs.Sec1Serialize.Conversion.Arithmetic.Natural
import P256.Proofs.Common.Instructions.Carry.Arithmetic
import P256.Proofs.Common.Instructions.Mul.Spec

set_option autoImplicit false

open P256.Proofs.Common.Instructions (mulHigh64)
open P256.Proofs.Common.Instructions.Carry (adcSpec adcSpec_toNat adcSpec_toNat_add_carry addSpec_toNat_add_carry)

namespace P256.Proofs.Sec1Serialize.Conversion.Montgomery

open X86Proofs

theorem addSpec_carry_toNat {n : Nat} (a b : BitVec n) :
    (addSpec a b).2.CF.toNat = (a.toNat + b.toNat) / 2 ^ n := by
  conv => rhs; rw [← addSpec_toNat_add_carry a b]
  rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos n),
    Nat.div_eq_of_lt (addSpec a b).1.isLt, Nat.zero_add]

theorem adcSpec_carry_toNat {n : Nat} (a b : BitVec n) (c : BitVec 1) :
    (adcSpec a b c).2.CF.toNat = (a.toNat + b.toNat + c.toNat) / 2 ^ n := by
  conv => rhs; rw [← adcSpec_toNat_add_carry a b c]
  rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos n),
    Nat.div_eq_of_lt (adcSpec a b c).1.isLt, Nat.zero_add]

theorem mulHigh64_toNat (a b : BitVec 64) :
    (mulHigh64 a b).toNat = a.toNat * b.toNat / wordBase := by
  have hp := Nat.mul_lt_mul_of_lt_of_lt a.isLt b.isLt
  exact Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul hp)

def compilerRoundBV (a b c d z : BitVec 64) : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 :=
  let q := addSpec a z
  let e := (BitVec.ofBool q.2.CF).setWidth 64
  let neg := addSpec (q.1 * 0xffffffffffffffff) q.1
  let ec := adcSpec e (mulHigh64 q.1 0xffffffffffffffff) (BitVec.ofBool neg.2.CF)
  let l := addSpec (q.1 * 0xffffffff) b
  let h := adcSpec (mulHigh64 q.1 0xffffffff) 0 (BitVec.ofBool l.2.CF)
  let k := addSpec (q.1 * 0xffffffff00000001) d
  let j := adcSpec (mulHigh64 q.1 0xffffffff00000001) 0 (BitVec.ofBool k.2.CF)
  let o0 := addSpec l.1 ec.1
  let o1 := adcSpec h.1 c (BitVec.ofBool o0.2.CF)
  let o2 := adcSpec k.1 0 (BitVec.ofBool o1.2.CF)
  let o3 := adcSpec j.1 0 (BitVec.ofBool o2.2.CF)
  (o0.1, o1.1, o2.1, o3.1)

theorem toNat_shiftLeft32 (a : BitVec 64) :
    (a <<< 32).toNat = a.toNat * halfBase % wordBase := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

theorem toNat_ushiftRight32 (a : BitVec 64) :
    (a >>> 32).toNat = a.toNat / halfBase := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem toNat_mul_modulusHigh (a : BitVec 64) :
    (a * 0xffffffff00000001).toNat = a.toNat * modulusHigh % wordBase := by
  rw [BitVec.toNat_mul]
  rw [show (0xffffffff00000001 : BitVec 64).toNat = modulusHigh by decide +kernel]

theorem toNat_mulHigh_modulusHigh (a : BitVec 64) :
    (mulHigh64 a 0xffffffff00000001).toNat = a.toNat * modulusHigh / wordBase := by
  rw [mulHigh64_toNat]
  rw [show (0xffffffff00000001 : BitVec 64).toNat = modulusHigh by decide +kernel]

theorem compilerInitial_eq_reduceStep (a : Nat) (ha : a < wordBase) :
    limbsToNat (a * halfBase % wordBase) (a / halfBase)
      (a * modulusHigh % wordBase) (a * modulusHigh / wordBase) = reduceStep a := by
  have hs := reduceStep_limbs_sparse a 0 0 0 ha
  simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add] at hs
  rw [hs]
  dsimp [limbsToNat, wordBase, halfBase, modulusHigh]
  omega

theorem compilerInitialBV_eq_reduceStep (a : BitVec 64) :
    limbsToNat (a <<< 32).toNat (a >>> 32).toNat
      (a * 0xffffffff00000001).toNat (mulHigh64 a 0xffffffff00000001).toNat =
      reduceStep a.toNat := by
  rw [toNat_shiftLeft32, toNat_ushiftRight32, toNat_mul_modulusHigh,
    toNat_mulHigh_modulusHigh]
  exact compilerInitial_eq_reduceStep a.toNat a.isLt

theorem toNat_wordBase_sub_one :
    (0xffffffffffffffff : BitVec 64).toNat = wordBase - 1 := by decide +kernel

theorem toNat_halfBase_sub_one :
    (0xffffffff : BitVec 64).toNat = halfBase - 1 := by decide +kernel

theorem toNat_modulusHigh :
    (0xffffffff00000001 : BitVec 64).toNat = modulusHigh := by decide +kernel

structure CompilerRoundTrace (a b c d z : BitVec 64) where
  q : BitVec 64 × StatusFlags
  neg : BitVec 64 × StatusFlags
  ec : BitVec 64 × StatusFlags
  l : BitVec 64 × StatusFlags
  h : BitVec 64 × StatusFlags
  k : BitVec 64 × StatusFlags
  j : BitVec 64 × StatusFlags
  o0 : BitVec 64 × StatusFlags
  o1 : BitVec 64 × StatusFlags
  o2 : BitVec 64 × StatusFlags
  o3 : BitVec 64 × StatusFlags
  q_eq : addSpec a z = q
  neg_eq : addSpec (q.1 * 0xffffffffffffffff) q.1 = neg
  ec_eq : adcSpec ((BitVec.ofBool q.2.CF).setWidth 64)
    (mulHigh64 q.1 0xffffffffffffffff) (BitVec.ofBool neg.2.CF) = ec
  l_eq : addSpec (q.1 * 0xffffffff) b = l
  h_eq : adcSpec (mulHigh64 q.1 0xffffffff) 0 (BitVec.ofBool l.2.CF) = h
  k_eq : addSpec (q.1 * 0xffffffff00000001) d = k
  j_eq : adcSpec (mulHigh64 q.1 0xffffffff00000001) 0 (BitVec.ofBool k.2.CF) = j
  o0_eq : addSpec l.1 ec.1 = o0
  o1_eq : adcSpec h.1 c (BitVec.ofBool o0.2.CF) = o1
  o2_eq : adcSpec k.1 0 (BitVec.ofBool o1.2.CF) = o2
  o3_eq : adcSpec j.1 0 (BitVec.ofBool o2.2.CF) = o3

theorem addSpec_values (a b : BitVec 64) :
    ((addSpec a b).1.toNat, (addSpec a b).2.CF.toNat) =
      ((a.toNat + b.toNat) % wordBase, (a.toNat + b.toNat) / wordBase) :=
  Prod.ext (BitVec.toNat_add a b) (addSpec_carry_toNat a b)

theorem adcSpec_values (a b : BitVec 64) (carry : BitVec 1) :
    ((adcSpec a b carry).1.toNat, (adcSpec a b carry).2.CF.toNat) =
      ((a.toNat + b.toNat + carry.toNat) % wordBase,
        (a.toNat + b.toNat + carry.toNat) / wordBase) :=
  Prod.ext (adcSpec_toNat a b carry) (adcSpec_carry_toNat a b carry)

theorem CompilerRoundTrace.q_values {a b c d z : BitVec 64} (t : CompilerRoundTrace a b c d z) :
    (t.q.1.toNat, t.q.2.CF.toNat) =
      ((a.toNat + z.toNat) % wordBase, (a.toNat + z.toNat) / wordBase) := by
  have v := (congrArg (fun r : BitVec 64 × StatusFlags => (r.1.toNat, r.2.CF.toNat))
    t.q_eq).symm.trans (addSpec_values a z)
  exact v

theorem CompilerRoundTrace.neg_values {a b c d z : BitVec 64} (t : CompilerRoundTrace a b c d z) :
    (t.neg.1.toNat, t.neg.2.CF.toNat) =
      ((t.q.1.toNat * (wordBase - 1) % wordBase + t.q.1.toNat) % wordBase, (t.q.1.toNat * (wordBase - 1) % wordBase + t.q.1.toNat) / wordBase) := by
  have v := (congrArg (fun r : BitVec 64 × StatusFlags => (r.1.toNat, r.2.CF.toNat))
    t.neg_eq).symm.trans (addSpec_values (t.q.1 * 0xffffffffffffffff) t.q.1)
  rw [BitVec.toNat_mul, toNat_wordBase_sub_one] at v
  exact v

theorem CompilerRoundTrace.ec_values {a b c d z : BitVec 64} (t : CompilerRoundTrace a b c d z) :
    (t.ec.1.toNat, t.ec.2.CF.toNat) =
      ((t.q.2.CF.toNat + t.q.1.toNat * (wordBase - 1) / wordBase + t.neg.2.CF.toNat) % wordBase, (t.q.2.CF.toNat + t.q.1.toNat * (wordBase - 1) / wordBase + t.neg.2.CF.toNat) / wordBase) := by
  have he : t.q.2.CF.toNat < wordBase := by
    cases t.q.2.CF <;> decide +kernel
  have v := (congrArg (fun r : BitVec 64 × StatusFlags => (r.1.toNat, r.2.CF.toNat))
    t.ec_eq).symm.trans (adcSpec_values ((BitVec.ofBool t.q.2.CF).setWidth 64) (mulHigh64 t.q.1 0xffffffffffffffff) (BitVec.ofBool t.neg.2.CF))
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofBool, mulHigh64_toNat, toNat_wordBase_sub_one, Nat.mod_eq_of_lt he, BitVec.toNat_ofBool] at v
  exact v

theorem CompilerRoundTrace.l_values {a b c d z : BitVec 64} (t : CompilerRoundTrace a b c d z) :
    (t.l.1.toNat, t.l.2.CF.toNat) =
      ((t.q.1.toNat * (halfBase - 1) % wordBase + b.toNat) % wordBase, (t.q.1.toNat * (halfBase - 1) % wordBase + b.toNat) / wordBase) := by
  have v := (congrArg (fun r : BitVec 64 × StatusFlags => (r.1.toNat, r.2.CF.toNat))
    t.l_eq).symm.trans (addSpec_values (t.q.1 * 0xffffffff) b)
  rw [BitVec.toNat_mul, toNat_halfBase_sub_one] at v
  exact v

theorem CompilerRoundTrace.h_values {a b c d z : BitVec 64} (t : CompilerRoundTrace a b c d z) :
    (t.h.1.toNat, t.h.2.CF.toNat) =
      ((t.q.1.toNat * (halfBase - 1) / wordBase + t.l.2.CF.toNat) % wordBase, (t.q.1.toNat * (halfBase - 1) / wordBase + t.l.2.CF.toNat) / wordBase) := by
  have v := (congrArg (fun r : BitVec 64 × StatusFlags => (r.1.toNat, r.2.CF.toNat))
    t.h_eq).symm.trans (adcSpec_values (mulHigh64 t.q.1 0xffffffff) 0 (BitVec.ofBool t.l.2.CF))
  rw [mulHigh64_toNat, toNat_halfBase_sub_one, show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero, BitVec.toNat_ofBool] at v
  exact v

theorem CompilerRoundTrace.k_values {a b c d z : BitVec 64} (t : CompilerRoundTrace a b c d z) :
    (t.k.1.toNat, t.k.2.CF.toNat) =
      ((t.q.1.toNat * modulusHigh % wordBase + d.toNat) % wordBase, (t.q.1.toNat * modulusHigh % wordBase + d.toNat) / wordBase) := by
  have v := (congrArg (fun r : BitVec 64 × StatusFlags => (r.1.toNat, r.2.CF.toNat))
    t.k_eq).symm.trans (addSpec_values (t.q.1 * 0xffffffff00000001) d)
  rw [BitVec.toNat_mul, toNat_modulusHigh] at v
  exact v

theorem CompilerRoundTrace.j_values {a b c d z : BitVec 64} (t : CompilerRoundTrace a b c d z) :
    (t.j.1.toNat, t.j.2.CF.toNat) =
      ((t.q.1.toNat * modulusHigh / wordBase + t.k.2.CF.toNat) % wordBase, (t.q.1.toNat * modulusHigh / wordBase + t.k.2.CF.toNat) / wordBase) := by
  have v := (congrArg (fun r : BitVec 64 × StatusFlags => (r.1.toNat, r.2.CF.toNat))
    t.j_eq).symm.trans (adcSpec_values (mulHigh64 t.q.1 0xffffffff00000001) 0 (BitVec.ofBool t.k.2.CF))
  rw [mulHigh64_toNat, toNat_modulusHigh, show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero, BitVec.toNat_ofBool] at v
  exact v

theorem CompilerRoundTrace.o0_values {a b c d z : BitVec 64} (t : CompilerRoundTrace a b c d z) :
    (t.o0.1.toNat, t.o0.2.CF.toNat) =
      ((t.l.1.toNat + t.ec.1.toNat) % wordBase, (t.l.1.toNat + t.ec.1.toNat) / wordBase) := by
  have v := (congrArg (fun r : BitVec 64 × StatusFlags => (r.1.toNat, r.2.CF.toNat))
    t.o0_eq).symm.trans (addSpec_values t.l.1 t.ec.1)
  exact v

theorem CompilerRoundTrace.o1_values {a b c d z : BitVec 64} (t : CompilerRoundTrace a b c d z) :
    (t.o1.1.toNat, t.o1.2.CF.toNat) =
      ((t.h.1.toNat + c.toNat + t.o0.2.CF.toNat) % wordBase, (t.h.1.toNat + c.toNat + t.o0.2.CF.toNat) / wordBase) := by
  have v := (congrArg (fun r : BitVec 64 × StatusFlags => (r.1.toNat, r.2.CF.toNat))
    t.o1_eq).symm.trans (adcSpec_values t.h.1 c (BitVec.ofBool t.o0.2.CF))
  rw [BitVec.toNat_ofBool] at v
  exact v

theorem CompilerRoundTrace.o2_values {a b c d z : BitVec 64} (t : CompilerRoundTrace a b c d z) :
    (t.o2.1.toNat, t.o2.2.CF.toNat) =
      ((t.k.1.toNat + t.o1.2.CF.toNat) % wordBase, (t.k.1.toNat + t.o1.2.CF.toNat) / wordBase) := by
  have v := (congrArg (fun r : BitVec 64 × StatusFlags => (r.1.toNat, r.2.CF.toNat))
    t.o2_eq).symm.trans (adcSpec_values t.k.1 0 (BitVec.ofBool t.o1.2.CF))
  rw [show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero, BitVec.toNat_ofBool] at v
  exact v

theorem CompilerRoundTrace.o3_values {a b c d z : BitVec 64} (t : CompilerRoundTrace a b c d z) :
    (t.o3.1.toNat, t.o3.2.CF.toNat) =
      ((t.j.1.toNat + t.o2.2.CF.toNat) % wordBase, (t.j.1.toNat + t.o2.2.CF.toNat) / wordBase) := by
  have v := (congrArg (fun r : BitVec 64 × StatusFlags => (r.1.toNat, r.2.CF.toNat))
    t.o3_eq).symm.trans (adcSpec_values t.j.1 0 (BitVec.ofBool t.o2.2.CF))
  rw [show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero, BitVec.toNat_ofBool] at v
  exact v

theorem CompilerRoundTrace.toNat {a b c d z : BitVec 64} (t : CompilerRoundTrace a b c d z) :
    (t.o0.1.toNat, t.o1.1.toNat, t.o2.1.toNat, t.o3.1.toNat) =
      compilerRound a.toNat b.toNat c.toNat d.toNat z.toNat := by
  have hi := compilerRound_intermediates a.toNat b.toNat c.toNat d.toNat z.toNat
    a.isLt b.isLt c.isLt d.isLt z.isLt
  have ⟨qv, qc⟩ := Prod.mk.inj t.q_values
  have ⟨negv, negc⟩ := Prod.mk.inj t.neg_values
  have ⟨ecv, ecc⟩ := Prod.mk.inj t.ec_values
  have ⟨lv, lc⟩ := Prod.mk.inj t.l_values
  have ⟨hv, hc⟩ := Prod.mk.inj t.h_values
  have ⟨kv, kc⟩ := Prod.mk.inj t.k_values
  have ⟨jv, jc⟩ := Prod.mk.inj t.j_values
  have ⟨o0v, o0c⟩ := Prod.mk.inj t.o0_values
  have ⟨o1v, o1c⟩ := Prod.mk.inj t.o1_values
  have ⟨o2v, o2c⟩ := Prod.mk.inj t.o2_values
  have ⟨o3v, o3c⟩ := Prod.mk.inj t.o3_values
  dsimp only at hi
  simp only [compilerRound, ← qv, ← qc] at hi ⊢
  rw [lc, Nat.mod_eq_of_lt hi.1] at hv
  rw [kc, Nat.mod_eq_of_lt hi.2.1] at jv
  rw [negc] at ecv
  simp only [← ecv, ← lv, ← kv, ← hv, ← jv, ← o0v, ← o0c,
    ← o1v, ← o1c, ← o2v, ← o2c, ← o3v]

theorem compilerRoundBV_toNat (a b c d z : BitVec 64) :
    let r := compilerRoundBV a b c d z
    (r.1.toNat, r.2.1.toNat, r.2.2.1.toNat, r.2.2.2.toNat) =
      compilerRound a.toNat b.toNat c.toNat d.toNat z.toNat := by
  let q := addSpec a z
  let e := (BitVec.ofBool q.2.CF).setWidth 64
  let neg := addSpec (q.1 * 0xffffffffffffffff) q.1
  let ec := adcSpec e (mulHigh64 q.1 0xffffffffffffffff) (BitVec.ofBool neg.2.CF)
  let l := addSpec (q.1 * 0xffffffff) b
  let h := adcSpec (mulHigh64 q.1 0xffffffff) 0 (BitVec.ofBool l.2.CF)
  let k := addSpec (q.1 * 0xffffffff00000001) d
  let j := adcSpec (mulHigh64 q.1 0xffffffff00000001) 0 (BitVec.ofBool k.2.CF)
  let o0 := addSpec l.1 ec.1
  let o1 := adcSpec h.1 c (BitVec.ofBool o0.2.CF)
  let o2 := adcSpec k.1 0 (BitVec.ofBool o1.2.CF)
  let o3 := adcSpec j.1 0 (BitVec.ofBool o2.2.CF)
  let t : CompilerRoundTrace a b c d z :=
    ⟨q, neg, ec, l, h, k, j, o0, o1, o2, o3,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  exact t.toNat

theorem compilerRoundBV_eq_reduceStep (a b c d z : BitVec 64)
    (hn : limbsToNat a.toNat b.toNat c.toNat d.toNat + z.toNat < p) :
    let r := compilerRoundBV a b c d z
    limbsToNat r.1.toNat r.2.1.toNat r.2.2.1.toNat r.2.2.2.toNat =
      reduceStep (limbsToNat a.toNat b.toNat c.toNat d.toNat + z.toNat) := by
  have h := congrArg (fun r : Nat × Nat × Nat × Nat => limbsToNat r.1 r.2.1 r.2.2.1 r.2.2.2)
    (compilerRoundBV_toNat a b c d z)
  exact h.trans (compilerRound_eq_reduceStep a.toNat b.toNat c.toNat d.toNat z.toNat
    a.isLt b.isLt c.isLt d.isLt z.isLt hn)

end P256.Proofs.Sec1Serialize.Conversion.Montgomery
