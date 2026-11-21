import P256.Proofs.Sec1.SquareRoot.Prepare.Prefix
import P256.Proofs.Sec1.SquareRoot.Prepare.ParameterCopy
import P256.Proofs.Sec1.SquareRoot.Prepare.Setup

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open P256.Proofs.Field Prepare

theorem field_sqrt_prepare [Bindings] {s : RamState} {boundary : ReturnBoundary} {x : Nat}
    (pre : Pre s boundary) (input : MontgomeryAt s (s.regValue .rsi) x) :
    ∃ fuel t, Advances boundary fuel s t ∧ ExponentCallState s t x := by
  obtain ⟨n0,t0,run0,state0,rip0,input0⟩ := input_copy pre input
  obtain ⟨n1,t1,run1,ready1,_,effect1⟩ := parameter_setup boundary pre.outerBoundary
    t0 (readyToStep state0.machine state0.bindingsSupported)
    (programText_slice (programLoaded_codeIn state0.loaded) 0x14451 parameterSetupBytes
      (by decide +kernel) (by decide +kernel)) rip0
  have state1 : FrameState s t1 := state0.of_registers pre ready1 effect1.agrees
    (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp [parameterSetupEffect, Effect.components])
    (by simp [parameterSetupEffect, Effect.components, Component.Covers])
    (by simp [parameterSetupEffect, Effect.components])
    (by simp [parameterSetupEffect, Effect.components])
    (by simp [parameterSetupEffect, Effect.components])
  have values1 : t1.regValue .r8 = stackPtr s - 360 ∧
      t1.regValue .rdi = stackPtr s - 360 ∧ t1.regValue .rcx = 14 ∧
      t1.regValue .rsi = 0x202f28 := by
    have h : t1.regValue .r8 = (Operand.reg 4 : Operand 64).read t0 + 224 ∧
        t1.regValue .rdi = (Operand.reg 4 : Operand 64).read t0 + 224 ∧ t1.regValue .rcx = 14 ∧
        t1.regValue .rsi = 0x202f28 := effect1.writes
    rw [state0.stack_address 224] at h
    exact h
  obtain ⟨t2,run2,ready2,rip2,parameters2,agrees2⟩ := parameter_copy pre ready1 state1.loaded
    state1.directionFlag.df effect1.rip values1.2.2.2 values1.2.1 values1.2.2.1 state1.allocated
  have state2 : FrameState s t2 := frame_after pre state1 ready2 agrees2
    (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp) (by
      intro c hc a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl <;> try exact ha.elim
      exact ⟨workRegion s, by simp, ScalarFrame.Work.contains pre (by decide) (by decide) ha⟩)
  have mem1 : t1.external = t0.external := effect1.agrees.external
    (by simp [parameterSetupEffect, Effect.components, Component.Covers])
  have input2 : MontgomeryAt t2 (stackPtr s - 392) x := by
    refine ⟨input0.1, input0.2.1, ?_⟩
    intro i hi
    have same := agrees2.byte (x := stackPtr s - 392 + BitVec.ofNat 64 i) (by
      intro c hc ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl <;> try exact ha.elim
      obtain ⟨j,hj,he⟩ := ha
      exact stack_sub_apart pre.stack (a := 360) (b := 392)
        (by decide) (by decide) (by decide) (by decide) (by decide) j hj i hi he.symm)
    rw [same, mem1]
    exact input0.2.2 i hi
  obtain ⟨n3,t3,run3,ready3,_,effect3⟩ := exponent_setup boundary pre.outerBoundary
    t2 ready2 (programText_slice (programLoaded_codeIn state2.loaded)
      0x1446b exponentSetupBytes (by decide +kernel) (by decide +kernel)) rip2
  have state3 : FrameState s t3 := state2.of_registers pre ready3 effect3.agrees
    (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp [exponentSetupEffect, Effect.components])
    (by simp [exponentSetupEffect, Effect.components, Component.Covers])
    (by simp [exponentSetupEffect, Effect.components])
    (by simp [exponentSetupEffect, Effect.components])
    (by simp [exponentSetupEffect, Effect.components])
  have values3 : t3.regValue .r14 = stackPtr s - 248 ∧
      t3.regValue .rsi = stackPtr s - 392 ∧ t3.regValue .rdi = stackPtr s - 248 ∧
      t3.regValue .rdx = 0x202fb8 ∧ t3.regValue .rcx = 254 := by
    have h : t3.regValue .r14 = (Operand.reg 4 : Operand 64).read t2 + 336 ∧
        t3.regValue .rsi = (Operand.reg 4 : Operand 64).read t2 + 192 ∧ t3.regValue .rdi = (Operand.reg 4 : Operand 64).read t2 + 336 ∧
        t3.regValue .rdx = 0x202fb8 ∧ t3.regValue .rcx = 254 := effect3.writes
    rw [state2.stack_address 336, state2.stack_address 192] at h
    exact h
  have mem3 : t3.external = t2.external := effect3.agrees.external
    (by simp [exponentSetupEffect, Effect.components, Component.Covers])
  refine ⟨n0+n1+14+n3,t3,((run0.trans run1).trans run2).trans run3,
    state3,effect3.rip,values3.1,values3.2.1,values3.2.2.1,
    values3.2.2.2.1,values3.2.2.2.2,?_,?_,?_⟩
  · exact ((effect3.agrees.read (r := 8) (n := 64)
      (by simp [exponentSetupEffect, Effect.components])).trans
      (agrees2.read (r := 8) (n := 64) (by simp))).trans values1.1
  · exact ⟨input2.1,input2.2.1,fun i hi => by rw [mem3]; exact input2.2.2 i hi⟩
  · have address : stackPtr s - 392 + 32 = stackPtr s - 360 := by
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
    rw [address]
    intro i hi
    rw [mem3]
    exact parameters2 i hi

end P256.Proofs.Sec1.SquareRoot
