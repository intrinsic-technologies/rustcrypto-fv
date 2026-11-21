import P256.Proofs.Projective.Multiply.Machine.Loop.Round.Copy
import P256.Proofs.Projective.Multiply.Machine.Loop.Round.AddArguments
import P256.Proofs.Projective.Multiply.Machine.Loop.Round.OutputArguments
import P256.Proofs.Projective.Multiply.Machine.Loop.Call.Add

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Loop.Round

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

theorem add_round [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {n : Nat} {point selected : Projective} (pre : Pre s boundary)
    (state : RoundState s t n 0x1033a2 144 point)
    (selectedAt : ProjectiveAt t (stackPtr s-240) selected) :
    ∃ fuel u, Advances boundary fuel t u ∧
      RoundState s u n 0x1033be 336 (point.add selected) ∧
      u.regValue .rax = stackPtr s-144 := by
  obtain ⟨a, v, runV, readyV, _, effectV⟩ := addArguments_correct boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x33a2 addArgumentsBytes
      (by decide) (by decide +kernel)) state.rip
  have agrV : AgreesExcept [.reg 7, .reg 6, .rip] t v := effectV.agrees
  have memoryV := agrV.external (by simp [Component.Covers])
  have sv := state.after_registers readyV agrV effectV.rip
    (by simp [Component.Covers]) (by simp) (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have hwV : v.regValue .rdi = t.regValue .rbp ∧ v.regValue .rsi = t.regValue .r12 := effectV.writes
  obtain ⟨w, addition⟩ := add_call pre sv.toFrameState roundAdd sv.rip
    (hwV.1.trans state.rbp) (hwV.2.trans state.r12) sv.value
    (selectedAt.of_bytes_eq (by intro i hi; rw [memoryV]))
  have sw := sv.after_point_call addition (by decide) addition.value
  obtain ⟨b, x, runX, readyX, _, effectX⟩ := outputArguments_correct boundary pre.outerBoundary w
    (readyToStep sw.machine sw.bindingsSupported)
    (programText_slice (programLoaded_codeIn sw.loaded) 0x33ad outputArgumentsBytes
      (by decide) (by decide +kernel)) sw.rip
  have agrX : AgreesExcept [.reg 0, .reg 1, .reg 7, .reg 6, .rip] w x := effectX.agrees
  have sx := sw.after_registers readyX agrX effectX.rip
    (by simp [Component.Covers]) (by simp) (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have hwX : x.regValue .rax = w.regValue .rbp ∧ x.regValue .rcx = 12 ∧
      x.regValue .rdi = w.regValue .r13 ∧ x.regValue .rsi = w.regValue .rbp := effectX.writes
  have src : x.regValue .rsi = stackPtr s-144 := hwX.2.2.2.trans sw.rbp
  have dst : x.regValue .rdi = stackPtr s-336 := hwX.2.2.1.trans sw.r13
  have input : ProjectiveAt x (x.regValue .rsi) (point.add selected) := by
    rw [src]
    exact sx.value
  have readable : MemReadable x (x.regValue .rsi) 96 := by
    rw [src]
    exact readable_of_grow (stack_sub_readable pre.stack (offset := 144)
      (by decide) (by decide)) sx.allocated
  obtain ⟨u, copied, su, ripU, value, frame⟩ := Copy.copy_to_stack pre.toCalleePre sx.toFrameState
    0x33bb (by decide) (by decide +kernel) sx.rip 336 (by decide) (by decide)
    dst hwX.2.1 readable (stack_sources_disjoint pre (by decide) (by decide) src dst (by decide)) input
  obtain ⟨c, runW⟩ := addition.execution
  exact ⟨a+c+b+12, u, ((runV.trans runW).trans runX).trans copied,
    sx.after_copy pre su ripU value frame (by decide) (by decide),
    (frame.read (n := 64) (r := 0) (by simp)).trans (hwX.1.trans sw.rbp)⟩

end P256.Proofs.Projective.Multiply.Machine.Loop.Round
