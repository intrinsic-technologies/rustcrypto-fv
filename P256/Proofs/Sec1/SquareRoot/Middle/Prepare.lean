import P256.Proofs.Sec1.SquareRoot.Middle.Setup
import P256.Proofs.Sec1.SquareRoot.Middle.ParameterCopy
import P256.Proofs.Sec1.SquareRoot.Middle.CandidateFrame
import P256.Proofs.Sec1.SquareRoot.Middle.Memory

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Middle

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open P256.Proofs.Field (MontgomeryAt)
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure ParameterState [Bindings] (s t : RamState) (x beta : Nat) : Prop where
  frame : FrameState s t
  rip : t.RIP = 0x1144a9
  r14 : t.regValue .r14 = stackPtr s - 248
  r15 : t.regValue .r15 = stackPtr s - 216
  input : MontgomeryAt t (stackPtr s - 392) x
  candidate : MontgomeryAt t (stackPtr s - 248) beta
  parameters : ParametersAt t (stackPtr s - 216)

theorem prepare_parameters [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x beta : Nat}
    (pre : Pre s boundary) (state : FrameState s t)
    (rip : t.RIP = 0x11448f) (r14 : t.regValue .r14 = stackPtr s - 248)
    (input : MontgomeryAt t (stackPtr s - 392) x)
    (candidate : MontgomeryAt t (stackPtr s - 248) beta) :
    ∃ n u, Advances boundary n t u ∧ ParameterState s u x beta := by
  obtain ⟨n1,t1,run1,ready1,_,effect1⟩ := parameterSetup_run boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported) (parameterSetup_code state.loaded) rip
  have state1 := state.of_registers pre ready1 effect1.agrees (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [parameterSetupEffect, Effect.components])
    (by simp [parameterSetupEffect, Effect.components, Component.Covers])
  have mem1 := effect1.agrees.external (by simp [parameterSetupEffect, Effect.components, Component.Covers])
  have dst : t1.regValue .rdi = stackPtr s - 216 :=
    effect1.writes.2.2.1.trans (state.stack_address 368)
  have r151 : t1.regValue .r15 = stackPtr s - 216 :=
    effect1.writes.1.trans (state.stack_address 368)
  obtain ⟨u,run2,ready2,rip2,params,agrees⟩ := parameter_copy pre ready1 state1.loaded
    state1.directionFlag.df effect1.rip effect1.writes.2.2.2 dst effect1.writes.2.1 state1.allocated
  have state2 := frame_after pre state1 ready2 agrees (by simp) (by
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> try exact ha.elim
    exact ⟨workRegion s, by simp, ScalarFrame.Work.contains pre (by decide) (by decide) ha⟩)
  refine ⟨n1+14,u,run1.trans run2,state2,rip2,?_,?_,?_,?_,params⟩
  · exact (agrees.read (r := 14) (n := 64) (by simp)).trans
      ((effect1.agrees.read (r := 14) (n := 64) (by simp [parameterSetupEffect, Effect.components])).trans r14)
  · exact (agrees.read (r := 15) (n := 64) (by simp)).trans r151
  · apply input.of_bytes_eq
    intro i hi
    exact (parameter_copy_byte pre agrees (by decide) (by decide) (by decide) hi).trans
      (congrArg (fun m : Ram => m[_]?) mem1)
  · apply candidate.of_bytes_eq
    intro i hi
    exact (parameter_copy_byte pre agrees (by decide) (by decide) (by decide) hi).trans
      (congrArg (fun m : Ram => m[_]?) mem1)

structure WideCallState [Bindings] (s t : RamState) (x beta : Nat) : Prop where
  frame : FrameState s t
  rip : t.RIP = 0x1144f0
  rsi : t.regValue .rsi = stackPtr s - 248
  rdi : t.regValue .rdi = stackPtr s - 104
  rdx : t.regValue .rdx = 4
  r12 : t.regValue .r12 = stackPtr s - 104
  r15 : t.regValue .r15 = stackPtr s - 216
  input : MontgomeryAt t (stackPtr s - 392) x
  candidate : MontgomeryAt t (stackPtr s - 248) beta
  copy : MontgomeryAt t (stackPtr s - 576) beta
  modulus : Nat256At t (stackPtr s - 216) P256.Spec.Operations.domain.p

theorem prepare_wide [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x beta : Nat}
    (pre : Pre s boundary) (state : ParameterState s t x beta) :
    ∃ n u, Advances boundary n t u ∧ WideCallState s u x beta := by
  have copyPre := candidateCopyPre_of_frame pre state.frame state.rip
  obtain ⟨n1,t1,run1,ready1,_,effect1⟩ := candidate_copy boundary pre.outerBoundary t
    (readyToStep state.frame.machine state.frame.bindingsSupported)
    (candidate_copy_code state.frame.loaded) copyPre
  have state1 := candidate_copy_state pre state.frame ready1 effect1
  have candidate1 := state.candidate.of_bytes_eq
    (candidate_copy_bytes pre state.frame effect1 (by decide) (by decide))
  have input1 := state.input.of_bytes_eq
    (candidate_copy_bytes pre state.frame effect1 (by decide) (by decide))
  have copy1 : MontgomeryAt t1 (stackPtr s - 576) beta := by
    have hc := candidateCopyEffect_montgomery copyPre effect1 (by
      change MontgomeryAt t ((Operand.reg 4 : Operand 64).read t + 336) beta
      rw [state.frame.stack_address]
      exact state.candidate)
    change MontgomeryAt t1 ((Operand.reg 4 : Operand 64).read t + 8) beta at hc
    rw [state.frame.stack_address] at hc
    exact hc
  have modulus1 : Nat256At t1 (stackPtr s - 216) P256.Spec.Operations.domain.p := by
    have hm := parameters_modulus state.parameters
    exact ⟨hm.1, fun i hi => (candidate_copy_bytes pre state.frame effect1
      (by decide) (by decide) i hi).trans (hm.2 i hi)⟩
  obtain ⟨n2,u,run2,ready2,_,effect2⟩ := wideSetup_run boundary pre.outerBoundary t1 ready1
    (wideSetup_code state1.loaded) effect1.rip
  have state2 := state1.of_registers pre ready2 effect2.agrees (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [wideSetupEffect, Effect.components])
    (by simp [wideSetupEffect, Effect.components, Component.Covers])
  have mem2 := effect2.agrees.external (by simp [wideSetupEffect, Effect.components, Component.Covers])
  have r141 : t1.regValue .r14 = stackPtr s - 248 :=
    (effect1.agrees.read (r := 14) (n := 64) (by simp [candidateCopyEffect, Effect.components])).trans state.r14
  refine ⟨n1+n2,u,run1.trans run2,state2,effect2.rip,effect2.writes.2.2.2.trans r141,
    effect2.writes.2.2.1.trans (state1.stack_address 480),effect2.writes.2.1,
    effect2.writes.1.trans (state1.stack_address 480),?_,?_,?_,?_,?_⟩
  · exact (effect2.agrees.read (r := 15) (n := 64) (by simp [wideSetupEffect, Effect.components])).trans
      ((effect1.agrees.read (r := 15) (n := 64) (by simp [candidateCopyEffect, Effect.components])).trans state.r15)
  · exact input1.of_bytes_eq (fun i hi => congrArg (fun m : Ram => m[_]?) mem2)
  · exact candidate1.of_bytes_eq (fun i hi => congrArg (fun m : Ram => m[_]?) mem2)
  · exact copy1.of_bytes_eq (fun i hi => congrArg (fun m : Ram => m[_]?) mem2)
  · exact ⟨modulus1.1, fun i hi => by rw [mem2]; exact modulus1.2 i hi⟩

end P256.Proofs.Sec1.SquareRoot.Middle
