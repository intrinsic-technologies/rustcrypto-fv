import X86Proofs.Core.Shift

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Conversions.Bsr

open X86 X86.Helpers X86Proofs

def leadingZeroCount64 (x : BitVec 64) : Int :=
  (((Runtime.intRangeDown 63 0).find? (fun i => x.getLsbD i.toNat)).map
    (fun i => 63 - i)).getD 64

theorem sliceBit64_run (x : BitVec 64) (i : Int) (hi : 0 ≤ i) (hi64 : i < 64) :
    (Runtime.CheckedSlice.read x i 1 : Except (Runtime.Error Empty) (BitVec 1)) =
      .ok (BitVec.ofBool (x.getLsbD i.toNat)) := by
  have hbit : x.extractLsb' i.toNat 1 = BitVec.ofBool (x.getLsbD i.toNat) := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have hj0 : j = 0 := by omega
    subst j
    simp
  simp [Runtime.CheckedSlice.read, x86_runtime, hi, show i + 1 ≤ 64 by omega,
    hbit, pure, Except.pure]

theorem leadingZeroScan64_run (x : BitVec 64) (indices : List Int)
    (hindices : ∀ i ∈ indices, 0 ≤ i ∧ i < 64) :
    (forIn indices (none, ()) (fun i (_ : Option Int × Unit) => do
      let b ← (Runtime.CheckedSlice.read x i 1 : Except (Runtime.Error Empty) (BitVec 1))
      if b == 1 then pure (ForInStep.done (some (64 - i - 1), ()))
      else pure (ForInStep.yield (none, ())))) =
      .ok (((indices.find? (fun i => x.getLsbD i.toNat)).map (fun i => 63 - i)), ()) := by
  induction indices with
  | nil => rfl
  | cons i is ih =>
    have hi := hindices i (by simp)
    have hrest : ∀ j ∈ is, 0 ≤ j ∧ j < 64 := fun j hj => hindices j (by simp [hj])
    simp only [List.forIn_cons, sliceBit64_run x i hi.1 hi.2]
    cases hb : x.getLsbD i.toNat
    · simpa [hb, bind, pure, Except.bind, Except.pure] using ih hrest
    · simp [hb, show 64 - i - 1 = 63 - i by omega, bind, pure, Except.bind, Except.pure]

theorem countLeadingZeroBits64_run (x : BitVec 64) :
    Std.Bits.Count_Leading_Zero_Bits (size := 64) x = .ok (leadingZeroCount64 x) := by
  have h := leadingZeroScan64_run x (Runtime.intRangeDown 63 0) (by
    intro i hi
    simp only [Runtime.intRangeDown, List.mem_map, List.mem_range] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    omega)
  unfold Std.Bits.Count_Leading_Zero_Bits
  simp only [show (64 : Int) - 1 = 63 from rfl, show decide (0 ≤ (64 : Int)) = true from rfl,
    assert_of_true, pure_bind]
  rw [h]
  cases he : (Runtime.intRangeDown 63 0).find? (fun i => x.getLsbD i.toNat) <;>
    simp [leadingZeroCount64, he, bind, pure, Except.bind, Except.pure]

end P256.Proofs.Nonce.Initialize.Conversions.Bsr
