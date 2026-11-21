import P256.Proofs.Field.Inverse.Setup.Frame
import P256.Proofs.Field.Inverse.Setup.Arguments

set_option autoImplicit false

namespace P256.Proofs.Field.Inverse

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program

abbrev wordEffect (i : Fin 8) (s : RamState) : Effect :=
  RipCopy.effect (Extracted.textAddress + BitVec.ofNat 64 parameterWords[i].1)
    parameterWords[i].2.1 parameterWords[i].2.2 s

theorem parameter_word_run [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (ready : ReadyToStep t) (sp : stackPtr t = stackPtr s-168)
    (agrees : AgreesExcept (setupComponents s) s t) (i : Fin 8)
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 parameterWords[i].1) :
    ∃ n u, Advances boundary n t u ∧ ReadyToStep u ∧ stackPtr u = stackPtr s-168 ∧
      AgreesExcept (setupComponents s) s u ∧
      u.RIP = Extracted.textAddress + BitVec.ofNat 64 parameterWords[i].1 + (12 : BitVec 64) ∧
      (wordEffect i t).Holds t u := by
  have loaded := setup_loaded pre agrees
  obtain ⟨n,u,run,readyU,_,effect⟩ := parameter_word_copy i ready loaded pre.outerBoundary
    (parameter_word_pre pre loaded sp agrees.grow i rip)
  refine ⟨n,u,run,readyU,?_,setup_trans agrees (parameter_effect_agrees sp i effect),effect.rip,effect⟩
  exact (effect.agrees.read (n := 64) (r := 4)
    (by simp [RipCopy.effect, Effect.components])).trans sp

theorem parameter_middle_run [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (ready : ReadyToStep t) (sp : stackPtr t = stackPtr s-168)
    (agrees : AgreesExcept (setupComponents s) s t) (rip : t.RIP = 0x1140cc) :
    ∃ n u, Advances boundary n t u ∧ ReadyToStep u ∧ stackPtr u = stackPtr s-168 ∧
      AgreesExcept (setupComponents s) s u ∧ u.RIP = 0x1140da ∧
      (parameterMiddleEffect t).Holds t u := by
  have args : ParameterMiddlePre t :=
    ⟨rip, parameter_stack_writable pre sp agrees.grow (offset := 104) (by decide) (by decide),
      parameter_stack_code pre sp (offset := 104) (codeOffset := 0x140cc) (len := 14)
        (by decide) (by decide)⟩
  obtain ⟨n,u,run,readyU,_,effect⟩ := parameter_middle boundary pre.outerBoundary
    t ready (parameter_middle_loaded (setup_loaded pre agrees)) args
  have ag : AgreesExcept [.mem (stackPtr t+104) 8, .reg 8, .rip] t u := by
    simpa [parameterMiddleEffect, Effect.components, stackPtr, gprIndex] using effect.agrees
  have wide : AgreesExcept (setupComponents s) t u := by
    apply ag.widen
    · intro c hc hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;> simp [Component.isMem, setupComponents] at hm ⊢
    · intro a c hc ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact ⟨.mem (stackPtr s-128) 72, by simp [setupComponents],
          setup_parameter_covers sp (offset := 104) (by decide) (by decide) ha⟩
      all_goals exact ha.elim
  exact ⟨n,u,run,readyU,(ag.read (n := 64) (r := 4) (by simp)).trans sp,
    setup_trans agrees wide,effect.rip,effect⟩

theorem parameter_arguments_run [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (ready : ReadyToStep t) (sp : stackPtr t = stackPtr s-168)
    (agrees : AgreesExcept (setupComponents s) s t) (rip : t.RIP = 0x11410a) :
    ∃ n u, Advances boundary n t u ∧ ReadyToStep u ∧ stackPtr u = stackPtr s-168 ∧
      AgreesExcept (setupComponents s) s u ∧ u.RIP = 0x114119 ∧
      (parameterArgumentEffect t).Holds t u := by
  obtain ⟨n,u,run,readyU,_,effect⟩ := parameter_arguments boundary pre.outerBoundary
    t ready (parameter_arguments_loaded (setup_loaded pre agrees)) rip
  have ag : AgreesExcept [.reg 7, .reg 2, .reg 1, .rip] t u := by
    simpa [parameterArgumentEffect, Effect.components] using effect.agrees
  exact ⟨n,u,run,readyU,(ag.read (n := 64) (r := 4) (by simp)).trans sp,
    setup_trans agrees (ag.mono (by simp [setupComponents])),effect.rip,effect⟩

end P256.Proofs.Field.Inverse
