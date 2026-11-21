import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.ExponentSaveCopy
import P256.Proofs.Common.Field.Montgomery.Schoolbook.Compose

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.ExponentInitialize

open P256.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field.Montgomery.Schoolbook (memLoad_memStore_rangeApart)

set_option maxRecDepth 2048 in
theorem exponentSaveCopyMemory_word (s : RamState) (memory : Ram) (j : Nat) (hj : j < 4) :
    memLoad (exponentSaveCopyMemory s memory)
      (exponentFrameBase s + 0x538 + BitVec.ofNat 64 (8*j)) 64 =
      BitVec.ofNat 64 (sqrtExponent / 2^(64*j)) := by
  have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  all_goals
    simp only [exponentSaveCopyMemory, List.foldl_cons, List.foldl_nil, BitVec.ofNat_eq_ofNat,
      Nat.reduceMul, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero]
    repeat first
      | rw [memLoad_memStore_apart _ (exponentFrameBase s) _ _ _ 64
          (by unfold OffsetsApart; decide +kernel) (by decide) (by decide)]
      | exact memLoad_memStore _ _ (by decide) (by decide) _

set_option maxRecDepth 2048 in
theorem exponentSaveCopyMemory_preserves_word (s : RamState) (memory : Ram)
    (offset : Nat) (bound : offset + 8 ≤ 0x538) :
    memLoad (exponentSaveCopyMemory s memory)
      (exponentFrameBase s + BitVec.ofNat 64 offset) 64 =
      memLoad memory (exponentFrameBase s + BitVec.ofNat 64 offset) 64 := by
  simp only [exponentSaveCopyMemory, List.foldl_cons, List.foldl_nil]
  repeat rw [memLoad_memStore_rangeApart _ _ _ _ 64
    (RangeApart.offsets (exponentFrameBase s) (by omega) (by omega) (by omega))]

end P256.Proofs.Sec1.SquareRoot.ExponentInitialize
