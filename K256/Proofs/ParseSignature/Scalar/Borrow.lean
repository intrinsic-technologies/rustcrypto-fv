import Standards.SECG.DomainParameters.Secp256k1

namespace K256.Proofs.ParseSignature.Scalar

open Standards.SECG.DomainParameters

def borrowChain (a0 a1 a2 a3 : BitVec 64) : BitVec 64 :=
  let c0 := (~~~a0 ||| (0x402da1732fc9bebf#64 + a0)) >>> 63
  let m0 := (0#64 - c0).sshiftRight 63
  let s1 := 0x4551231950b75fc5#64 + a1 + m0
  let c1 := (~~~a1 ||| s1) >>> 63
  let m1 := (0#64 - c1).sshiftRight 63
  let s2 := m1 + a2 + 2#64
  let c2 := (s2 ||| ~~~a2) >>> 63
  let t := (c2 - 1#64) >>> 63
  let s3 := t + a3
  (~~~a3 ||| s3) >>> 63

private def borrowBit (p : Prop) [Decidable p] : Nat := if p then 1 else 0

private theorem borrowBit_le (p : Prop) [Decidable p] : borrowBit p ≤ 1 := by
  unfold borrowBit; split <;> omega

private theorem borrow_step (a r : BitVec 64) (n c : Nat) (hn : 2^63 ≤ n) (hc : n + c ≤ 2^64)
    (hr : r.toNat = (a.toNat + 2^64 - n - c) % 2^64) :
    (~~~a ||| r) >>> 63 = BitVec.ofNat 64 (borrowBit (a.toNat < n + c)) := by
  apply BitVec.eq_of_toNat_eq
  have ha := a.isLt
  have hrl := r.isLt
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_or, BitVec.toNat_not, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_ofNat, borrowBit]
  have hx : (2 ^ 64 - 1 - a.toNat) / 2 ^ 63 = if a.toNat < 2 ^ 63 then 1 else 0 := by
    split <;> omega
  have hy : r.toNat / 2 ^ 63 = if 2 ^ 63 ≤ r.toNat then 1 else 0 := by
    split <;> omega
  rw [← Nat.shiftRight_eq_div_pow, Nat.shiftRight_or_distrib, Nat.shiftRight_eq_div_pow,
    Nat.shiftRight_eq_div_pow, hx, hy]
  by_cases h1 : a.toNat < 2 ^ 63 <;> by_cases h2 : 2 ^ 63 ≤ r.toNat <;>
    by_cases h3 : a.toNat < n + c <;> simp only [h1, h2, h3, ite_true, ite_false] <;>
    first | rfl | omega

private theorem borrow_step_comm (a r : BitVec 64) (n c : Nat) (hn : 2^63 ≤ n) (hc : n + c ≤ 2^64)
    (hr : r.toNat = (a.toNat + 2^64 - n - c) % 2^64) :
    (r ||| ~~~a) >>> 63 = BitVec.ofNat 64 (borrowBit (a.toNat < n + c)) := by
  rw [BitVec.or_comm]
  exact borrow_step a r n c hn hc hr

private theorem sar_borrow (p : Prop) [Decidable p] :
    (0#64 - BitVec.ofNat 64 (borrowBit p)).sshiftRight 63 = 0#64 - BitVec.ofNat 64 (borrowBit p) := by
  unfold borrowBit; split <;> decide

private theorem flip_borrow (p : Prop) [Decidable p] :
    (BitVec.ofNat 64 (borrowBit p) - 1#64) >>> 63 = BitVec.ofNat 64 (1 - borrowBit p) := by
  unfold borrowBit; split <;> decide

private theorem toNat_step0 (a : BitVec 64) (K n : Nat) (hK : K + n = 2^64) :
    (BitVec.ofNat 64 K + a).toNat = (a.toNat + 2^64 - n - 0) % 2^64 := by
  have := a.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

private theorem toNat_step1 (a : BitVec 64) (K n c : Nat) (hK : K + n = 2^64)
    (hnc : n + c ≤ 2^64) :
    (BitVec.ofNat 64 K + a + (0#64 - BitVec.ofNat 64 c)).toNat = (a.toNat + 2^64 - n - c) % 2^64 := by
  have := a.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

private theorem toNat_step2 (a : BitVec 64) (K n c : Nat) (hK : K + n = 2^64)
    (hnc : n + c ≤ 2^64) :
    (0#64 - BitVec.ofNat 64 c + a + BitVec.ofNat 64 K).toNat = (a.toNat + 2^64 - n - c) % 2^64 := by
  have := a.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

private theorem toNat_step3 (a : BitVec 64) (c : Nat) (hc : c ≤ 1) :
    (BitVec.ofNat 64 (1 - c) + a).toNat = (a.toNat + 2^64 - (2^64 - 1) - c) % 2^64 := by
  have := a.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

private theorem borrow_carry (a n L N M c : Nat) (hL : L < M) (hN : N < M) (hc : c = borrowBit (L < N)) :
    borrowBit (a < n + c) = borrowBit (a * M + L < n * M + N) := by
  subst hc
  have k1 : a < n → a * M + M ≤ n * M := fun h => by
    have := Nat.mul_le_mul_right M h
    rwa [Nat.succ_mul] at this
  have k2 : n < a → n * M + M ≤ a * M := fun h => by
    have := Nat.mul_le_mul_right M h
    rwa [Nat.succ_mul] at this
  have k3 : a = n → a * M = n * M := fun h => by rw [h]
  unfold borrowBit
  by_cases hLN : L < N <;> simp only [hLN, ite_true, ite_false] <;> split <;> split <;> omega

theorem borrowChain_eq (a0 a1 a2 a3 : BitVec 64) :
    borrowChain a0 a1 a2 a3 =
      if ((a3.toNat * 2^64 + a2.toNat) * 2^128 + a1.toNat * 2^64 + a0.toNat) <
          Secp256k1.domain.n then 1 else 0 := by
  have h0 := a0.isLt
  have h1 := a1.isLt
  have h2 := a2.isLt
  have h3 := a3.isLt
  simp only [borrowChain]
  rw [borrow_step a0 _ 0xbfd25e8cd0364141 0 (by decide) (by decide)
    (toNat_step0 a0 0x402da1732fc9bebf _ (by decide))]
  rw [sar_borrow]
  generalize hc0 : borrowBit (a0.toNat < 0xbfd25e8cd0364141 + 0) = c0
  have hc0le : c0 ≤ 1 := hc0 ▸ borrowBit_le _
  rw [borrow_step a1 _ 0xbaaedce6af48a03b c0 (by decide) (by omega)
    (toNat_step1 a1 0x4551231950b75fc5 _ c0 (by decide) (by omega))]
  rw [sar_borrow]
  generalize hc1 : borrowBit (a1.toNat < 0xbaaedce6af48a03b + c0) = c1
  have hc1le : c1 ≤ 1 := hc1 ▸ borrowBit_le _
  rw [borrow_step_comm a2 _ 0xfffffffffffffffe c1 (by decide) (by omega)
    (toNat_step2 a2 2 _ c1 (by decide) (by omega))]
  rw [flip_borrow]
  generalize hc2 : borrowBit (a2.toNat < 0xfffffffffffffffe + c1) = c2
  have hc2le : c2 ≤ 1 := hc2 ▸ borrowBit_le _
  rw [borrow_step a3 _ (2^64 - 1) c2 (by decide) (by omega) (toNat_step3 a3 c2 hc2le)]
  rw [Nat.add_zero] at hc0
  rw [borrow_carry a1.toNat _ a0.toNat 0xbfd25e8cd0364141 (2^64) c0 h0 (by decide) hc0.symm] at hc1
  rw [borrow_carry a2.toNat _ _ (0xbaaedce6af48a03b * 2^64 + 0xbfd25e8cd0364141) (2^128) c1
    (by omega) (by decide) hc1.symm] at hc2
  rw [borrow_carry a3.toNat _ _
    ((0xfffffffffffffffe * 2^128 + (0xbaaedce6af48a03b * 2^64 + 0xbfd25e8cd0364141))) (2^192) c2
    (by omega) (by decide) hc2.symm]
  have hord : (2^64 - 1) * 2^192 +
      (0xfffffffffffffffe * 2^128 + (0xbaaedce6af48a03b * 2^64 + 0xbfd25e8cd0364141)) = Secp256k1.domain.n := by
    decide +kernel
  rw [hord, show a3.toNat * 2 ^ 192 + (a2.toNat * 2 ^ 128 + (a1.toNat * 2 ^ 64 + a0.toNat)) =
      (a3.toNat * 2^64 + a2.toNat) * 2^128 + a1.toNat * 2^64 + a0.toNat by
        rw [Nat.add_mul, Nat.mul_assoc, show 2^64 * 2^128 = (2 : Nat)^192 by decide +kernel]
        ac_rfl]
  unfold borrowBit
  split <;> rfl

end K256.Proofs.ParseSignature.Scalar
