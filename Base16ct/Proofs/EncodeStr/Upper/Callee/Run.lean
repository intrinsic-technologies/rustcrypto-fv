import Base16ct.Proofs.EncodeStr.Upper.Callee.Loop

namespace Base16ct.Proofs.EncodeStr.Upper

open Base16ct.Spec.Program Prelude X86 X86.Machine X86Proofs

theorem LoopState.success [Bindings] (c : CallContext) {s : RamState}
    (hs : LoopState c c.input.length s) : SuccessState c s := by
  exact ⟨hs.toCalleeState, by simpa only [Nat.lt_irrefl, ite_false] using hs.rip,
    hs.dst, hs.resultLength, hs.output⟩

theorem callee_loop_run [Bindings] (c : CallContext) {i : Nat} {s : RamState}
    (hc : 2 * c.input.length ≤ c.capacity) (hs : LoopState c i s) :
    ∃ fuel t, Advances (returnBoundary c.initial) fuel s t ∧ SuccessState c t := by
  generalize hn : c.input.length - i = n
  induction n generalizing i s with
  | zero =>
    have hi : i = c.input.length := by have := hs.bound; omega
    subst i
    exact ⟨0, s, (advances_zero _ _ _).mpr rfl, hs.success c⟩
  | succ n ih =>
    have hi : i < c.input.length := by omega
    obtain ⟨t, ht, hs'⟩ := callee_loop_step c hc hs hi
    obtain ⟨fuel, u, hu, hout⟩ := ih hs' (by omega)
    exact ⟨21 + fuel, u, ht.trans hu, hout⟩

end Base16ct.Proofs.EncodeStr.Upper
