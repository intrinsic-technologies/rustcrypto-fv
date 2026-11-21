import P256.Proofs.Nonce.Initialize.Conversions.Bsr.LeadingZeros

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Conversions.Bsr

open X86 X86.Helpers X86Proofs

def oddParity64 (x : BitVec 64) : Bool :=
  (List.range 64).foldl (fun acc i => acc ^^ x.getLsbD i) false

theorem parityScan64_run (x : BitVec 64) (indices : List Int) (acc : Bool)
    (hindices : ∀ i ∈ indices, 0 ≤ i ∧ i < 64) :
    (forIn indices (BitVec.ofBool acc) (fun i r => do
      let b ← (Runtime.CheckedSlice.read x i 1 : Except (Runtime.Error Empty) (BitVec 1))
      pure (ForInStep.yield (BitVec.xor r b)))) =
      .ok (BitVec.ofBool (indices.foldl (fun (a : Bool) (i : Int) => a ^^ x.getLsbD i.toNat) acc)) := by
  induction indices generalizing acc with
  | nil => rfl
  | cons i is ih =>
    have hi := hindices i (by simp)
    have hrest : ∀ j ∈ is, 0 ≤ j ∧ j < 64 := fun j hj => hindices j (by simp [hj])
    have hxor (a b : Bool) : BitVec.xor (BitVec.ofBool a) (BitVec.ofBool b) =
        BitVec.ofBool (a ^^ b) := BitVec.ofBool_xor_ofBool
    simp only [List.forIn_cons, sliceBit64_run x i hi.1 hi.2]
    simpa [bind, pure, Except.bind, Except.pure, hxor] using ih
      (acc ^^ x.getLsbD i.toNat) hrest

theorem isParityOdd64_run (x : BitVec 64) :
    Std.Bits.Is_Parity_Odd (size := 64) x = .ok (oddParity64 x) := by
  have h := parityScan64_run x (Runtime.intRange 0 63) false (by
    intro i hi
    simp only [Runtime.intRange, List.mem_map, List.mem_range] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    omega)
  unfold Std.Bits.Is_Parity_Odd
  simp only [show decide (0 ≤ (64 : Int)) = true from rfl, assert_of_true, pure_bind]
  change (do
    let r ← forIn (Runtime.intRange 0 63) (BitVec.ofBool false) (fun i r => do
      let b ← (Runtime.CheckedSlice.read x i 1 : Except (Runtime.Error Empty) (BitVec 1))
      pure (ForInStep.yield (BitVec.xor r b)))
    pure (r == 1#1)) = .ok (oddParity64 x)
  rw [h]
  have hbeq (b : Bool) : (BitVec.ofBool b == 1#1) = b := by cases b <;> rfl
  simp [oddParity64, Runtime.intRange, List.foldl_map, bind, pure, Except.bind, Except.pure, hbeq]

end P256.Proofs.Nonce.Initialize.Conversions.Bsr
