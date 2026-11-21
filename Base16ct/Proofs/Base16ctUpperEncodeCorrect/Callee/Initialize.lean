import Base16ct.Proofs.Base16ctUpperEncodeCorrect.Callee.Initialize.Prefix
import Base16ct.Proofs.Base16ctUpperEncodeCorrect.Callee.Initialize.Success

namespace Base16ct.Proofs.Base16ctUpperEncodeCorrect

open Base16ct.Spec.Program Prelude X86 X86.Machine X86Proofs

theorem callee_initialize [Bindings] (c : CallContext) {s : RamState}
    (hs : RunInvariant c s) (he : CalleeEntry c s) :
    ∃ fuel t, Advances (returnBoundary c.initial) fuel s t ∧
      if 2 * c.input.length ≤ c.capacity then
        if c.input.length = 0 then SuccessState c t else LoopState c 0 t
      else ErrorState c t := by
  obtain ⟨u, hu, hi, hip⟩ := callee_initialize_prefix c hs he
  by_cases hc : 2 * c.input.length ≤ c.capacity
  · rw [ite_eq_left hc] at hip
    obtain ⟨fuel, t, ht, hout⟩ := callee_initialize_success c hi hip
    exact ⟨4 + fuel, t, hu.trans ht, by simpa only [ite_eq_left hc] using hout⟩
  · refine ⟨4, u, hu, ?_⟩
    rw [ite_eq_right hc]
    exact ⟨hi.toCalleeState, by simpa only [ite_eq_right hc] using hip⟩

end Base16ct.Proofs.Base16ctUpperEncodeCorrect
