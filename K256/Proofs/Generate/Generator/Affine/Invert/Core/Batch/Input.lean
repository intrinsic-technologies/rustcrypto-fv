import K256.Proofs.Generate.Generator.Affine.Invert.Core.Batch.Arithmetic

namespace K256.Proofs.Generate.Generator.Affine.Invert.Core.Batch

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Generate.LIR
open SafeGcd.Batch (Words)

def lowWord (w : Word) (sign : BitVec 8) : Word :=
  let mag := w &&& 0x7fffffffffffffff
  ((-sign.setWidth 64) &&& ((-mag) ^^^ mag)) ^^^ mag

theorem lowWord_congruent {p : Ram} {addr : Word} {x : Int} (h : signedAt p addr x) :
    (2 : Int)^63 ∣ (lowWord (memLoad p addr 64) (memLoad p (addr+32) 8)).toInt - x := by
  obtain ⟨w, b, words, sign, rfl⟩ := h
  have l := words 0 (by decide)
  simp only [wordAddr, Nat.mul_zero, BitVec.add_zero] at l
  rw [l, sign]
  let mag := w[0] &&& 0x7fffffffffffffff
  have hm : mag.toNat = w[0].toNat % 2^63 :=
    (BitVec.toNat_and ..).trans (Nat.and_two_pow_sub_one_eq_mod _ 63)
  have hv : (value w) % (2^63) = w[0].toNat % 2^63 := by unfold value; omega
  have hb : mag.msb = false := by
    apply BitVec.msb_eq_false_iff_two_mul_lt.mpr
    rw [hm]
    have := Nat.mod_lt w[0].toNat (by decide : 0 < 2^63)
    omega
  have hp := BitVec.toInt_eq_toNat_of_msb hb
  have hn := BitVec.toInt_neg_eq_of_msb hb
  rw [hm, ← hv] at hp
  have sel : lowWord w[0] (if b then 1 else 0) = (if b then -mag else mag) := by
    cases b
    · simp [lowWord, mag]
    · change (BitVec.allOnes 64 &&& ((-mag) ^^^ mag)) ^^^ mag = -mag
      simp only [BitVec.allOnes_and, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  rw [sel]
  have hlow := SafeGcd.signedLow_congruent (value w) b
  cases b <;> simpa [SafeGcd.signedLow, hp, hn] using hlow

def initialWords (b : Registers) (p : Ram) (sp : Word) : Words where
  delta := b[5].get 64
  f := lowWord (memLoad p (base sp + 120) 64) (memLoad p (base sp + 152) 8)
  g := lowWord (memLoad p (base sp + 168) 64) (memLoad p (base sp + 200) 8)
  u := 1
  v := 0
  q := 0
  r := 1

theorem initialWords_low {entry b : Registers} {m p : Ram} {sp : Word} {z : Fin modulus}
    {n : Nat} {d e : Int} (state : LoopState entry m sp z n b p d e) (hn : n ≤ 591) :
    SafeGcd.LowBitsEq 63 (SafeGcd.Batch.state (initialWords b p sp)) (Core.model z n) := by
  refine ⟨?_, ?_, ?_⟩
  · change (b[5].get 64).toInt = _
    rw [state.delta]
    change (BitVec.ofInt 64 (Core.model z n).delta).toInt = _
    have h := deltaBound n ⟨1, modulus, z.val⟩
    change (Core.model z n).delta.natAbs ≤ 1+2*n at h
    apply BitVec.toInt_ofInt_eq_self (by decide) <;> omega
  · simpa only [SafeGcd.Batch.state, initialWords, BitVec.add_assoc,
      show (120 : Word) + 32 = 152 from by decide +kernel] using
      lowWord_congruent state.fValue
  · simpa only [SafeGcd.Batch.state, initialWords, BitVec.add_assoc,
      show (168 : Word) + 32 = 200 from by decide +kernel] using
      lowWord_congruent state.gValue

end K256.Proofs.Generate.Generator.Affine.Invert.Core.Batch
