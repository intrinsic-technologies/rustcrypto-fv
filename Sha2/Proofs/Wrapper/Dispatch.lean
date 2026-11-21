import Sha2.Proofs.Wrapper.Variant
import Sha2.Proofs.Wrapper.Initialize
import Sha2.Proofs.Wrapper.Dispatch.Branch
import Sha2.Proofs.Wrapper.Dispatch.Loop
import Sha2.Proofs.Wrapper.Buffered

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper.Dispatch

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

 theorem run [Bindings] {v : Variant} {initial : RamState} {inputs : Array Input}
    (ctx : Context initial inputs v) : ∃ t,
      (Buffered initial t (message inputs) v ∧ t.RIP = (v.pc 0x1bb)) ∨
      LoopState initial t inputs 0 v := by
  obtain ⟨s, initialized, rip, count⟩ := Initialize.run ctx
  obtain ⟨t, execution, ready, target, frame⟩ := branch
    (supportedMachine_readyToStep initialized.machine) initialized.loaded rip
    (validCall_returnBoundary ctx.machine ctx.call).2.2
  have buffered := buffered_of_agrees ctx initialized execution ready frame
    (by simp [Component.Covers]) (by simp)
  have countNat : (s.regValue .rsi).toNat = inputs.size := by
    rw [count]
    exact ctx.call.countArgumentMatchesInputs
  by_cases empty : inputs.size = 0
  · have zero : s.regValue .rsi = 0 := BitVec.eq_of_toNat_eq (countNat.trans empty)
    have arrayEmpty : inputs = #[] := Array.eq_empty_of_size_eq_zero empty
    refine ⟨t, .inl ⟨?_, ?_⟩⟩
    · simpa only [arrayEmpty, message, Array.foldl_empty] using buffered
    · exact target.trans (ite_eq_left zero)
  · have nonzero : s.regValue .rsi ≠ 0 := by
      intro h
      apply empty
      rw [h] at countNat
      exact countNat.symm
    have ip : t.RIP = (v.pc 0x8e) := target.trans (ite_eq_right nonzero)
    obtain ⟨fuel, u, run, readyU, _, effect⟩ := Loop.run (returnBoundary initial)
      (validCall_returnBoundary ctx.machine ctx.call).2.2 t
      (supportedMachine_readyToStep buffered.machine) (Loop.code buffered.loaded) ip
    have frameU : AgreesExcept [.reg 15, .reg 14, .flags, .rip] t u := effect.agrees
    have bufferedU := buffered_of_agrees ctx buffered run readyU frameU
      (by simp [Component.Covers]) (by simp)
    have writes : u.regValue .r15 = t.regValue .rsi ∧ u.regValue .r14 = 0 := effect.writes
    refine ⟨u, .inr ⟨?_, effect.rip, writes.2, ?_, by omega⟩⟩
    · simpa only [prefixMessage_zero] using bufferedU
    · have kept : t.regValue .rsi = s.regValue .rsi := frame.read (n := 64) (r := 6) (by simp)
      rw [writes.1, kept]
      rw [← countNat]
      simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]

end Sha2.Proofs.Wrapper.Dispatch
