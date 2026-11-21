import Standards.NIST.SHA1.Computation

namespace Sha1.Proofs.Compress.Rounds

open Standards.NIST.SHA1 Standards.NIST.SHA2.SHA256

theorem sha1Ch_eq (x y z : BitVec 32) :
    Ch x y z = z ^^^ (x &&& (y ^^^ z)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Ch, BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_not, hi,
    decide_true]
  cases x.getLsbD i <;> cases y.getLsbD i <;> cases z.getLsbD i <;> decide

theorem sha1Maj_eq_or (x y z : BitVec 32) :
    Maj x y z = (x &&& y) ||| ((x ||| y) &&& z) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Maj, BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_or]
  cases x.getLsbD i <;> cases y.getLsbD i <;> cases z.getLsbD i <;> decide

theorem sha1Maj_eq_xor (x y z : BitVec 32) :
    Maj x y z = (x &&& y) ^^^ ((x ^^^ y) &&& z) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Maj, BitVec.getLsbD_xor, BitVec.getLsbD_and]
  cases x.getLsbD i <;> cases y.getLsbD i <;> cases z.getLsbD i <;> decide

theorem sha1Rotl_eq_rotateLeft (n : Nat) (x : BitVec 32) (h : n < 32) :
    ROTL n x = x.rotateLeft n := by
  rw [ROTL]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_rotateLeft_of_le h]
  by_cases hn : i < n
  · simp [hn, hi]
  · have hidx : 32 ≤ 32 - n + i := by omega
    rw [BitVec.getLsbD_of_ge x _ hidx]
    simp [hn, hi]

theorem sha1_f_choice {t : Fin 80} {x y z : BitVec 32} (h : t.val ≤ 19) :
    f t x y z = Ch x y z := by
  simp [f, h]

theorem sha1_f_parity_first {t : Fin 80} {x y z : BitVec 32}
    (h₁ : 19 < t.val) (h₂ : t.val ≤ 39) :
    f t x y z = Parity x y z := by
  have hnot : ¬ t.val ≤ 19 := by omega
  simp [f, hnot, h₂]

theorem sha1_f_majority {t : Fin 80} {x y z : BitVec 32}
    (h₁ : 39 < t.val) (h₂ : t.val ≤ 59) :
    f t x y z = Maj x y z := by
  have hnot : ¬ t.val ≤ 19 := by omega
  simp [f, hnot, Nat.not_le_of_gt h₁, h₂]

theorem sha1_f_parity_last {t : Fin 80} {x y z : BitVec 32} (h : 59 < t.val) :
    f t x y z = Parity x y z := by
  have hnot : ¬ t.val ≤ 19 := by omega
  have hnot39 : ¬ t.val ≤ 39 := by omega
  have hnot59 : ¬ t.val ≤ 59 := by omega
  simp [f, hnot, hnot39, hnot59]

theorem sha1_step_a_compiler_order (t : Fin 80) (Wt : BitVec 32)
    (v : WorkingVariables) :
    (step t Wt v).a =
      ROTL 5 v.a + f t v.b v.c v.d + K t + Wt + v.e := by
  simp only [step]
  ac_rfl

theorem sha1_step_a_choice (t : Fin 80) (Wt : BitVec 32) (v : WorkingVariables)
    (h : t.val ≤ 19) :
    (step t Wt v).a = ROTL 5 v.a + Ch v.b v.c v.d + K t + Wt + v.e := by
  rw [sha1_step_a_compiler_order, sha1_f_choice h]

theorem sha1_step_a_parity_first (t : Fin 80) (Wt : BitVec 32) (v : WorkingVariables)
    (h₁ : 19 < t.val) (h₂ : t.val ≤ 39) :
    (step t Wt v).a = ROTL 5 v.a + Parity v.b v.c v.d + K t + Wt + v.e := by
  rw [sha1_step_a_compiler_order, sha1_f_parity_first h₁ h₂]

theorem sha1_step_a_majority (t : Fin 80) (Wt : BitVec 32) (v : WorkingVariables)
    (h₁ : 39 < t.val) (h₂ : t.val ≤ 59) :
    (step t Wt v).a = ROTL 5 v.a + Maj v.b v.c v.d + K t + Wt + v.e := by
  rw [sha1_step_a_compiler_order, sha1_f_majority h₁ h₂]

theorem sha1_step_a_parity_last (t : Fin 80) (Wt : BitVec 32) (v : WorkingVariables)
    (h : 59 < t.val) :
    (step t Wt v).a = ROTL 5 v.a + Parity v.b v.c v.d + K t + Wt + v.e := by
  rw [sha1_step_a_compiler_order, sha1_f_parity_last h]

theorem sha1_K_choice {t : Fin 80} (h : t.val ≤ 19) :
    K t = 0x5a827999 := by
  simp only [K, ite_eq_left h]

theorem sha1_K_parity_first {t : Fin 80} (h₁ : 19 < t.val) (h₂ : t.val ≤ 39) :
    K t = 0x6ed9eba1 := by
  simp only [K, ite_eq_right (Nat.not_le_of_gt h₁), ite_eq_left h₂]

theorem sha1_K_majority {t : Fin 80} (h₁ : 39 < t.val) (h₂ : t.val ≤ 59) :
    K t = 0x8f1bbcdc := by
  have hnot : ¬ t.val ≤ 19 := by omega
  simp only [K, ite_eq_right hnot, ite_eq_right (Nat.not_le_of_gt h₁), ite_eq_left h₂]

theorem sha1_K_parity_last {t : Fin 80} (h : 59 < t.val) :
    K t = 0xca62c1d6 := by
  have hnot19 : ¬ t.val ≤ 19 := by omega
  have hnot39 : ¬ t.val ≤ 39 := by omega
  simp only [K, ite_eq_right hnot19, ite_eq_right hnot39, ite_eq_right (Nat.not_le_of_gt h)]

theorem sha1Rotl30_eq_rotateRight (x : BitVec 32) :
    ROTL 30 x = x.rotateRight 2 := by
  change (x <<< 30 ||| x >>> 2) = (x >>> 2 ||| x <<< 30)
  exact BitVec.or_comm _ _

theorem sha1_step_eq_rotateLeft (t : Fin 80) (Wt : BitVec 32) (v : WorkingVariables) :
    step t Wt v =
      { a := v.a.rotateLeft 5 + f t v.b v.c v.d + K t + Wt + v.e,
        b := v.a, c := v.b.rotateLeft 30, d := v.c, e := v.d } := by
  simp only [step, sha1Rotl_eq_rotateLeft 5 _ (by decide),
    sha1Rotl_eq_rotateLeft 30 _ (by decide), WorkingVariables.mk.injEq, and_true]
  ac_rfl

end Sha1.Proofs.Compress.Rounds
