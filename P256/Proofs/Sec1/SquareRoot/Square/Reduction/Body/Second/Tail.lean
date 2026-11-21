import P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Second.Tail.Machine
import P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Second.Arithmetic

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Second

open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem tail_correct [Bindings] {s t u : RamState} {boundary : ReturnBoundary} {v : Nat}
    (pre : ReductionPre s boundary) (state : First s t v)
    (hpref : (prefixEffect t).Holds t u)
    (frame : ScalarFrame.FrameState s u 32 112 112)
    (input : Bytes s.external (s.regValue .rsi) 64
      (fun i => UInt8.ofNat (v / 256^i % 256)))
    (_bound : v < P256.Spec.Operations.domain.p * 2^256) :
    ∃ w, (∃ fuel, Advances boundary fuel u w) ∧ Body.Second s w v := by
  obtain ⟨w, run, fw, rip, slots, inverse, pointer, rdi, r10, words, carry⟩ :=
    Tail.machine pre state hpref frame input
  refine ⟨w, run, ⟨fw, rip, slots, inverse, pointer, rdi, r10, carry, ?_⟩⟩
  have value := round_value_lift (t.regValue .r14) (t.regValue .r15)
    (t.regValue .r11) (t.regValue .rbx) v state.value
  dsimp only at value
  rw [← words] at value
  have hc : (carryByte s w != 0).toNat = (carryByte s w).toNat := by
    have casesByte : carryByte s w = 0 ∨ carryByte s w = 1 := by
      have h := carry
      by_cases hz : (carryByte s w).toNat = 0
      · exact Or.inl (BitVec.eq_of_toNat_eq hz)
      · exact Or.inr (BitVec.eq_of_toNat_eq (by change (carryByte s w).toNat = 1; omega))
    rcases casesByte with h | h <;> rw [h] <;> decide
  simpa only [hc] using value

end P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Second
