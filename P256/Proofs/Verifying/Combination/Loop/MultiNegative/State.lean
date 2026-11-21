import P256.Proofs.Verifying.Combination.Loop.MultiDigitState

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Loop.Multi

open P256.Spec P256.Spec.Program P256.Proofs.Projective P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem DigitData.after_registers [Bindings] {s t w : RamState}
    {tables digits : BitVec 64} {p q point : Projective} {u v k : Nat} {left : Bool}
    {cs : List Component}
    (state : DigitData s t tables digits p q u v k point left) (ready : ReadyToStep w)
    (agrees : AgreesExcept cs t w) (memory : ∀ c ∈ cs, ∀ a, ¬c.Covers a)
    (kept : ∀ r ∈ [3, 4, 5, 12, 13, 15], Component.reg r ∉ cs)
    (hdf : Component.df ∉ cs := by component_not_mem)
    (hmxcsr : Component.mxcsr ∉ cs := by component_not_mem)
    (hfcw : Component.fcw ∉ cs := by component_not_mem) :
    DigitData s w tables digits p q u v k point left := by
  refine ⟨state.toRoundData.after_registers ready agrees memory
      (fun r hr => kept r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp)),
    (agrees.read (n := 64) (r := 13) (kept 13 (by simp))).trans state.cursor,
    (agrees.read (n := 64) (r := 5) (kept 5 (by simp))).trans state.tableCursor,
    (agrees.read (n := 64) (r := 12) (kept 12 (by simp))).trans state.remaining, ?_⟩
  rw [agrees.external memory]
  exact state.savedCursor

end P256.Proofs.Verifying.Combination.Loop.Multi
