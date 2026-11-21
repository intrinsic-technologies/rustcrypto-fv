import P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Correction.Arithmetic
import P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Correction.Borrow
import P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Correction.Select

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body

open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem correction_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary} {v : Nat}
    (pre : ReductionPre s boundary) (state : Fourth s t v)
    (bound : v < P256.Spec.Operations.domain.p * 2^256) :
    ∃ u, (∃ fuel, Advances boundary fuel t u) ∧
      ScalarFrame.FrameState s u 32 112 112 ∧ u.RIP = 0x1137a3 ∧
      Nat256At u (s.regValue .rdi)
        (Field.Montgomery.subtractP (Field.Montgomery.reduceFour v)) := by
  have value : (Correction.inputLimbs t).toNat + 2^256 * (t.regValue .r12).toNat =
      Field.Montgomery.reduceFour v := by
    have h := state.value
    simp only [Correction.inputLimbs, Limbs.toNat]
    omega
  have reduced := Correction.reduce_toNat (Correction.inputLimbs t) (t.regValue .r12)
    (by rw [value]; exact Field.Montgomery.reduceFour_lt_two_mul_p v bound)
  rw [value] at reduced
  obtain ⟨u, ⟨fuel1, run1⟩, difference⟩ := Correction.borrow_correct pre state
  obtain ⟨w, ⟨fuel2, run2⟩, frame, rip, output⟩ := Correction.select_correct pre difference
    (Correction.subRaw_toNat (Correction.inputLimbs t) Correction.modulus).1
  rw [reduced] at output
  exact ⟨w, ⟨fuel1 + fuel2, run1.trans run2⟩, frame, rip, output⟩

end P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body
