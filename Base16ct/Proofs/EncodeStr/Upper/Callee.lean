import Base16ct.Proofs.EncodeStr.Upper.Callee.Initialize
import Base16ct.Proofs.EncodeStr.Upper.Callee.Run
import Base16ct.Proofs.EncodeStr.Upper.Callee.Tail

namespace Base16ct.Proofs.EncodeStr.Upper

open Base16ct.Spec.Program Prelude X86 X86.Machine X86Proofs

theorem callee_run [Bindings] (c : CallContext) {s : RamState}
    (hs : RunInvariant c s) (he : CalleeEntry c s) :
    ∃ fuel t, Advances (returnBoundary c.initial) fuel s t ∧
      RunInvariant c t ∧ CalleeExit c t := by
  obtain ⟨initFuel, t, ht, hstate⟩ := callee_initialize c hs he
  by_cases hc : 2 * c.input.length ≤ c.capacity
  · simp only [ite_eq_left hc] at hstate
    by_cases hz : c.input.length = 0
    · simp only [ite_eq_left hz] at hstate
      obtain ⟨u, hu, hinv, hout⟩ := callee_success_tail c hc hstate
      exact ⟨initFuel + 3, u, ht.trans hu, hinv, hout⟩
    · simp only [ite_eq_right hz] at hstate
      obtain ⟨loopFuel, u, hu, hsuccess⟩ := callee_loop_run c hc hstate
      obtain ⟨v, hv, hinv, hout⟩ := callee_success_tail c hc hsuccess
      exact ⟨initFuel + loopFuel + 3, v, (ht.trans hu).trans hv, hinv, hout⟩
  · simp only [ite_eq_right hc] at hstate
    obtain ⟨u, hu, hinv, hout⟩ := callee_error_tail c hc hstate
    exact ⟨initFuel + 3, u, ht.trans hu, hinv, hout⟩

end Base16ct.Proofs.EncodeStr.Upper
