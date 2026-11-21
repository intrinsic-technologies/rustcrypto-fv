import Base16ct.Proofs.EncodeStr.Lower.Machine.Prepare
import Base16ct.Proofs.EncodeStr.Lower.Machine.Loop.Iteration
import Base16ct.Proofs.EncodeStr.Lower.Machine.Result.Exit

namespace Base16ct.Proofs.EncodeStr.Lower

open Base16ct.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem subroutine [Bindings] {initial s : RamState} {input : List UInt8} {capacity : Nat}
    (hCall : ValidCall base16ctLowerEncodeStr initial input.toByteArray capacity (2 * input.length) (2 * input.length ≤ capacity))
    (hOutside : ¬ InProgram (returnBoundary initial).rip)
    (h : SubroutinePre initial input capacity s) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧
      SubroutinePost initial input capacity t := by
  obtain ⟨fuel, u, ha, hu⟩ := subroutine_prepare hCall hOutside h
  rcases hu with hExit | ⟨hFits, hLoop⟩
  · obtain ⟨steps, t, hb, ht⟩ := callee_exit hCall hOutside hExit
    exact ⟨fuel + steps, t, ha.trans hb, ht⟩
  · obtain ⟨steps, v, hb, hv⟩ := loop_complete hCall hOutside hFits hLoop (Nat.zero_le _)
    obtain ⟨last, t, hc, ht⟩ := callee_exit hCall hOutside (loop_finished hFits hv)
    exact ⟨fuel + steps + last, t, (ha.trans hb).trans hc, ht⟩

end Base16ct.Proofs.EncodeStr.Lower
