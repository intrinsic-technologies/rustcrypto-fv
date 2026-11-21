import P256.Proofs.Verifying.Combination.Loop.MultiNegative.State

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Loop.Multi.Selection

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem state_after_registers [Bindings] {s t w : RamState}
    {tables digits : BitVec 64} {p q point : Projective} {u v k : Nat} {left : Bool}
    {address next : BitVec 64} {cs : List Component}
    (state : DigitState s t tables digits p q u v k point left address)
    (ready : ReadyToStep w) (agrees : AgreesExcept cs t w)
    (memory : ∀ c ∈ cs, ∀ a, ¬c.Covers a)
    (kept : ∀ r ∈ [3, 4, 5, 12, 13, 14, 15], Component.reg r ∉ cs)
    (rip : w.RIP = next)
    (hdf : Component.df ∉ cs := by component_not_mem)
    (hmxcsr : Component.mxcsr ∉ cs := by component_not_mem)
    (hfcw : Component.fcw ∉ cs := by component_not_mem) :
    DigitState s w tables digits p q u v k point left next := by
  refine ⟨state.toDigitData.after_registers ready agrees memory
    (fun r hr => kept r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp)), rip, ?_⟩
  intro h
  have eq : w.regValue .r14 = t.regValue .r14 := agrees.read (n := 64) (r := 14) (kept 14 (by simp))
  exact state.identity (by rwa [eq] at h)

end P256.Proofs.Verifying.Combination.Loop.Multi.Selection
