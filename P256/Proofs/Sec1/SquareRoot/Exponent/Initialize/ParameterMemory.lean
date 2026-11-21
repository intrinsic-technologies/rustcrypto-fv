import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.ParameterSlots
import P256.Proofs.Common.Field.Montgomery.Schoolbook.Compose

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.ExponentInitialize

open P256.Proofs.Common.Field.Montgomery.Schoolbook (memLoad_memStore_rangeApart)

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

def parameterCopiedWord (s : RamState) (pairs : List (Nat × Nat)) (offset : Nat)
    (value : BitVec 64) : BitVec 64 :=
  pairs.foldl (fun v pair => if pair.2 = offset then
    memLoad s.external (s.regValue .rsi + BitVec.ofNat 64 (32 + pair.1)) 64 else v) value

theorem parameterCopiesMemory_word (s : RamState) (pairs : List (Nat × Nat)) (memory : Ram)
    (offset : Nat) (ho : offset ≤ 1416) (halign : offset%8 = 0)
    (hvalid : ∀ pair ∈ pairs, pair.2 ≤ 1360 ∧ pair.2%8 = 0) :
    memLoad (parameterCopiesMemory s pairs memory) (exponentFrameBase s + BitVec.ofNat 64 offset) 64 =
      parameterCopiedWord s pairs offset
        (memLoad memory (exponentFrameBase s + BitVec.ofNat 64 offset) 64) := by
  induction pairs generalizing memory with
  | nil => rfl
  | cons pair pairs ih =>
    have hp := hvalid pair (by simp)
    have ht := fun p h => hvalid p (List.mem_cons_of_mem pair h)
    change memLoad (parameterCopiesMemory s pairs
      (memStore memory (exponentFrameBase s + BitVec.ofNat 64 pair.2)
        (memLoad s.external (s.regValue .rsi + BitVec.ofNat 64 (32 + pair.1)) 64))) _ 64 = _
    rw [ih _ ht]
    change parameterCopiedWord s pairs offset (memLoad (memStore memory _ _) _ 64) =
      parameterCopiedWord s pairs offset (if pair.2 = offset then _ else _)
    congr 1
    by_cases he : pair.2 = offset
    · rw [ite_eq_left he, he]
      exact memLoad_memStore _ _ (by decide) (by decide) _
    · rw [ite_eq_right he]
      apply memLoad_memStore_rangeApart
      exact RangeApart.offsets (exponentFrameBase s) (by omega) (by omega) (by omega)

theorem parameterCopiedWord_unchanged (s : RamState) (pairs : List (Nat × Nat))
    (offset : Nat) (value : BitVec 64) (h : ∀ pair ∈ pairs, pair.2 ≠ offset) :
    parameterCopiedWord s pairs offset value = value := by
  induction pairs generalizing value with
  | nil => rfl
  | cons pair pairs ih =>
    change parameterCopiedWord s pairs offset (if pair.2 = offset then _ else value) = value
    rw [ite_eq_right (h pair (by simp))]
    exact ih value (fun p hp => h p (List.mem_cons_of_mem pair hp))

set_option maxRecDepth 4096 in
theorem initialParameterCopies_ranges :
    ∀ pair ∈ initialParameterCopies, 0xa0 ≤ pair.2 ∧ pair.2 ≤ 0x298 := by
  decide +kernel

theorem initialParameterCopies_preserves_word (s : RamState) (memory : Ram) (offset : Nat)
    (ho : offset ≤ 1416) (halign : offset % 8 = 0)
    (apart : offset + 8 ≤ 0xa0 ∨ 0x2a0 ≤ offset) :
    memLoad (parameterCopiesMemory s initialParameterCopies memory)
      (exponentFrameBase s + BitVec.ofNat 64 offset) 64 =
      memLoad memory (exponentFrameBase s + BitVec.ofNat 64 offset) 64 := by
  rw [parameterCopiesMemory_word s initialParameterCopies memory offset ho halign (by
    have h : ∀ pair ∈ initialParameterCopies, pair.2 ≤ 1360 ∧ pair.2 % 8 = 0 := by decide +kernel
    exact h)]
  apply parameterCopiedWord_unchanged
  intro pair hp
  have hr := initialParameterCopies_ranges pair hp
  omega

end P256.Proofs.Sec1.SquareRoot.ExponentInitialize
