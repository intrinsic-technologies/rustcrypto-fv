import P256.Proofs.Sec1Serialize.Conversion.Arithmetic.Canonical
import P256.Proofs.Field.Representation

set_option autoImplicit false
open P256.Proofs.Sec1Serialize.Conversion.Montgomery (compilerInitialBV_eq_reduceStep compilerRoundBV compilerRoundBV_eq_reduceStep limbsToNat p p_lt_radix p_pos reduceFour_montgomery reduceStep)
open P256.Proofs.Common.Instructions (mulHigh64)
open P256.Proofs.Field (MontgomeryAt)

namespace P256.Proofs.Sec1Serialize.Conversion
open X86Proofs

theorem compilerConversionBV_eq_canonical (a0 a1 a2 a3 : BitVec 64)
    {x : Nat} (hx : x < p)
    (ha : limbsToNat a0.toNat a1.toNat a2.toNat a3.toNat = x * 2^256 % p) :
    compilerConversionBV a0 a1 a2 a3 =
      (canonicalLimb x 0, canonicalLimb x 1, canonicalLimb x 2, canonicalLimb x 3) := by
  let r1 := compilerRoundBV (a0 <<< 32) (a0 >>> 32)
    (a0 * 0xffffffff00000001) (mulHigh64 a0 0xffffffff00000001) a1
  let r2 := compilerRoundBV r1.1 r1.2.1 r1.2.2.1 r1.2.2.2 a2
  let r3 := compilerRoundBV r2.1 r2.2.1 r2.2.2.1 r2.2.2.2 a3
  have hb := reduceStep_delayed_bounds (ha ▸ Nat.mod_lt _ p_pos)
  have h0 := compilerInitialBV_eq_reduceStep a0
  have h1 : limbsToNat r1.1.toNat r1.2.1.toNat r1.2.2.1.toNat r1.2.2.2.toNat =
      reduceStep (reduceStep a0.toNat + a1.toNat) := by
    have h := compilerRoundBV_eq_reduceStep (a0 <<< 32) (a0 >>> 32)
      (a0 * 0xffffffff00000001) (mulHigh64 a0 0xffffffff00000001) a1 (by rw [h0]; exact hb.1)
    rw [h0] at h
    exact h
  have h2 : limbsToNat r2.1.toNat r2.2.1.toNat r2.2.2.1.toNat r2.2.2.2.toNat =
      reduceStep (reduceStep (reduceStep a0.toNat + a1.toNat) + a2.toNat) := by
    have h := compilerRoundBV_eq_reduceStep r1.1 r1.2.1 r1.2.2.1 r1.2.2.2 a2 (by rw [h1]; exact hb.2.1)
    rw [h1] at h
    exact h
  have h3 : limbsToNat r3.1.toNat r3.2.1.toNat r3.2.2.1.toNat r3.2.2.2.toNat = x := by
    have h := compilerRoundBV_eq_reduceStep r2.1 r2.2.1 r2.2.2.1 r2.2.2.2 a3 (by rw [h2]; exact hb.2.2)
    rw [h2, ← reduceFour_delayed, ha, reduceFour_montgomery x hx] at h
    exact h
  obtain ⟨h0, h1, h2, h3⟩ := canonicalLimbs_of_limbsToNat h3
  change r3 = _
  exact Prod.ext h0 (Prod.ext h1 (Prod.ext h2 h3))

theorem compilerConversionBV_of_montgomeryAt {t : X86.Machine.RamState}
    {address : BitVec 64} {x : Nat} (input : MontgomeryAt t address x) :
    compilerConversionBV ((Operand.mem address : Operand 64).read t)
      ((Operand.mem (address + 8) : Operand 64).read t)
      ((Operand.mem (address + 16) : Operand 64).read t)
      ((Operand.mem (address + 24) : Operand 64).read t) =
        (canonicalLimb x 0, canonicalLimb x 1, canonicalLimb x 2, canonicalLimb x 3) := by
  apply compilerConversionBV_eq_canonical _ _ _ _ input.1
  have h0 := P256.Proofs.Field.MontgomeryAt.memLoad_limb input 0 (by decide)
  have h1 := P256.Proofs.Field.MontgomeryAt.memLoad_limb input 1 (by decide)
  have h2 := P256.Proofs.Field.MontgomeryAt.memLoad_limb input 2 (by decide)
  have h3 := P256.Proofs.Field.MontgomeryAt.memLoad_limb input 3 (by decide)
  simp only [Nat.mul_zero, Nat.mul_one, Nat.reduceMul] at h0 h1 h2 h3
  have hzero : address + BitVec.ofNat 64 0 = address := BitVec.add_zero address
  rw [hzero] at h0
  change (Operand.mem address : Operand 64).read t = _ at h0
  change (Operand.mem (address + 8) : Operand 64).read t = _ at h1
  change (Operand.mem (address + 16) : Operand 64).read t = _ at h2
  change (Operand.mem (address + 24) : Operand 64).read t = _ at h3
  rw [h0, h1, h2, h3]
  exact limbsToNat_canonicalLimb _ (Nat.lt_trans (Nat.mod_lt _ p_pos) p_lt_radix)

end P256.Proofs.Sec1Serialize.Conversion
