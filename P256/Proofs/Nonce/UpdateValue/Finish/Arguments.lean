import P256.Proofs.Nonce.UpdateValue.Finish.State
import P256.Proofs.Nonce.UpdateValue.Finish.Setup
import P256.Proofs.Nonce.UpdateValue.Prepare.Memory

set_option autoImplicit false

namespace P256.Proofs.Nonce.UpdateValue.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

variable [Bindings] {initial s t : RamState} {boundary : ReturnBoundary} {state : State}

theorem arguments (pre : UpdateValuePre initial boundary state)
    (input : Absorbed initial s state) :
    ∃ fuel t, Advances boundary fuel s t ∧ CallReady initial t state := by
  have writable (offset : Nat) (bound : offset ≤ 32) (aligned : offset % 8 = 0) :
      MemWritable s (stackPtr s + BitVec.ofNat 64 offset) 8 := by
    rw [ScalarFrame.scalar_stack_address (frameOffset := 488) input.rsp (by decide) (by omega)]
    apply writable_of_grow _ input.allocated
    exact stack_sub_writable8 pre.stack
      (fun a ha hp => pre.avoids _ (by simp) a ha (.inr hp)) (by omega) (by omega)
  have setupPre : Setup.Pre s := by
    refine ⟨input.rip, ?_, ?_⟩
    · intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      · exact writable 8 (by decide) (by decide)
      · exact writable 16 (by decide) (by decide)
      · exact writable 24 (by decide) (by decide)
      · exact writable 32 (by decide) (by decide)
    · intro i hi pc len bound
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl <;>
        exact ScalarFrame.stack_code pre.callee input.toFrameState (by decide) (by decide) (by omega)
  obtain ⟨fuel, t, run, ready, _, effect⟩ := Setup.run boundary pre.outerBoundary s
    (readyToStep input.machine input.bindingsSupported)
    (programText_slice (programLoaded_codeIn input.loaded) 0xabb1 Setup.bytes
      (by decide) (by decide +kernel)) setupPre
  have rsp : stackPtr s = scratch initial := input.rsp
  have agrees : AgreesExcept [.reg 6, .reg 7,
      .mem (scratch initial + 8) 8, .mem (scratch initial + 16) 8,
      .mem (scratch initial + 24) 8, .mem (scratch initial + 32) 8, .rip] s t := by
    simpa only [Setup.effect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.cons_append, List.nil_append,
      List.append_nil, Nat.reduceDiv, show (Operand.reg 4 : Operand 64).read s = scratch initial from rsp] using effect.agrees
  have writes : WritesWithin [.reg 6, .reg 7,
      .mem (scratch initial + 8) 8, .mem (scratch initial + 16) 8,
      .mem (scratch initial + 24) 8, .mem (scratch initial + 32) 8, .rip]
      #v[ScalarFrame.workRegion initial 1168] := by
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    all_goals exact ⟨_, by simp, Prepare.work_contains_scratch pre (by decide) ha⟩
  have memory := agrees.memoryWriteFrame writes
  have frame := input.toFrameState.after_effect pre.callee (by decide) ready agrees
    (by intro c hc a ha
        obtain ⟨r, hr, hin⟩ := writes c hc a ha
        exact ⟨r, by simpa using Or.inr hr, hin⟩) (by simp)
  have values := effect.writes
  change t.regValue .rsi = stackPtr s + 8 ∧ t.regValue .rdi = s.regValue .r14 ∧ _ at values
  refine ⟨fuel, t, run, frame, effect.rip,
    (agrees.read (n := 64) (r := 3) (by simp)).trans input.valuePointer,
    values.2.1.trans input.hmacPointer, values.1.trans (congrArg (· + 8) rsp), ?_, ?_⟩
  · apply input.drbg.of_frame pre.stateBounded memory
    intro r hr a ha hb
    have eq : r = ScalarFrame.workRegion initial 1168 := by simpa using hr
    subst r
    exact pre.separation a ha (work_substack pre hb)
  · apply input.hmac.copy
    intro i hi
    apply agrees.byte
    intro c hc ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    all_goals obtain ⟨j, hj, eq⟩ := ha
    all_goals
      exact OffsetsApart.ne (len₂ := 168)
        (by unfold OffsetsApart; decide +kernel) (scratch initial) hj hi (by decide) eq.symm

end P256.Proofs.Nonce.UpdateValue.Finish
