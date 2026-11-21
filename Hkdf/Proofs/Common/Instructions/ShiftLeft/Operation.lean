import X86Proofs.Core.Shift
import Hkdf.Proofs.Common.Instructions.ShiftLeft.Spec

namespace Hkdf.Proofs.Common.Instructions.ShiftLeft

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

def shlLoopStep {n : Nat} (acc : BitVec n × BitVec 1) : BitVec n × BitVec 1 :=
  (acc.1 <<< 1, acc.1.extractLsb' (n - 1) 1)

theorem shl_fold {n : Nat} (x : BitVec n) (cf : BitVec 1) (k : Nat) (hk : 0 < k) :
    (Runtime.intRange 0 ((k : Int) - 1)).foldl
        (fun acc (_ : Int) => shlLoopStep acc) (x, cf) =
      (x <<< k, (x <<< (k - 1)).extractLsb' (n - 1) 1) := by
  have hr : Runtime.intRange 0 ((k : Int) - 1) = (List.range k).map (fun i : Nat => (0 : Int) + i) := by
    simp only [x86_runtime]
    congr 2
    omega
  rw [hr, List.foldl_map]
  clear hr
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  clear hk
  induction k with
  | zero => simp [shlLoopStep]
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil, Nat.add_sub_cancel, shlLoopStep, Prod.mk.injEq]
    constructor
    · exact BitVec.shiftLeft_add _ _ _ |>.symm
    · trivial

theorem shl_operation {σ : Type} (s : X86.State σ) (n : Nat)
    (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (x : BitVec n) (count : BitVec 8) :
    (X86.Instructions.Operations.SHL n x count).run s =
      let c := shiftCount n count
      let (r, flags) := shlSpec (StatusFlags.ofRFLAGS s.RFLAGS) (oracleBit s.oracle)
        (shlOracleAF s.oracle c) c x
      (.ok r, setFlags { s with oracle := oracleSkip s.oracle (shlOracleBits c) } flags) := by
  have hlt := shiftCount_lt_64 n count
  obtain ⟨c, hc⟩ : ∃ c, shiftCount n count = c := ⟨_, rfl⟩
  have hc32 : n ≠ 64 → count.toNat % 32 = c := fun h => by simp [← hc, shiftCount, h]
  have hc64 : n = 64 → count.toNat % 64 = c := fun h => by simp [← hc, shiftCount, h]
  rw [hc] at hlt ⊢
  simp only [shlSpec, shlOracleBits, shlOracleAF]
  rcases hn with rfl | rfl | rfl | rfl
  all_goals
    unfold X86.Instructions.Operations.SHL
    simp only [isParityEven8_run]
    repeat spec_bind_rfl
    simp only [Int.cast_ofNat_Int, Int.reduceBEq, Bool.false_eq_true, ↓reduceIte, Int.reduceToNat,
      unsigned_extractLsb', Nat.reducePow]
    first | rw [hc32 (by decide)] | rw [hc64 rfl]
    by_cases h0 : c = 0
    · subst h0
      simp
    have e0 : ((c : Int) != 0) = true := by simp; omega
    simp only [e0, h0, ↓reduceIte]
    spec_bind_rfl

    refine (specM_bind_run _ _ (specM_forIn_run _ _
      (fun _ => shlLoopStep) _ _ ?_)).trans ?_
    · intro _ _ _
      rfl
    rw [shl_fold _ _ _ (by omega)]
    generalize x <<< c = r
    by_cases h1 : c = 1
    · subst h1
      simp only [↓reduceIte]
      rw [setFlags_eq_of_store]
      · rfl
      · rflags_ext
    · have e1 : ((c : Int) == 1) = false := by simp; omega
      simp only [e1, h1, Bool.false_eq_true, ↓reduceIte]
      rw [setFlags_eq_of_store]
      · rfl
      · rflags_ext

end Hkdf.Proofs.Common.Instructions.ShiftLeft
