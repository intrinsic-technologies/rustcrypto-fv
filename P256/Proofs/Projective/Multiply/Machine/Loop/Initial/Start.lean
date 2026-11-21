import P256.Proofs.Projective.Multiply.Machine.Loop.Prologue
import P256.Proofs.Projective.Multiply.Machine.Loop.Initial.Setup

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Loop.Initial

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

theorem setup_entry [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x103250 768 96 1400) :
    ∃ fuel t, Advances boundary fuel s t ∧ FrameState s t 96 1400 376 ∧
      t.RIP = 0x10327d ∧ t.regValue .rbx = s.regValue .rsi ∧
      t.regValue .r9 = s.regValue .rcx ∧ t.regValue .rdi = stackPtr s - 336 ∧
      t.regValue .rcx = 12 ∧ t.regValue .rsi = 0x202490 ∧
      t.regValue .rdx = s.regValue .rdx ∧ t.regValue .r8 = s.regValue .r8 ∧
      memLoad t.external (stackPtr s - 360) 64 = s.regValue .rdi := by
  obtain ⟨u, run, state, rip, _, frame⟩ := loop_prologue pre
  obtain ⟨n, t, step, ready, _, effect⟩ := setup_correct boundary pre.outerBoundary u
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x3261 setupBytes
      (by decide) (by decide +kernel))
    ⟨rip, stack_writable pre state (offset := 16) (by decide) (by decide) (by decide),
      stack_code pre state (offset := 16) (len := 8) (codeOffset := 0x3261)
        (by decide) (by decide) (by decide)⟩
  have address : stackPtr u + 16 = stackPtr s - 360 :=
    scalar_stack_address (frameOffset := 376) state.rsp (by decide) (by decide)
  have acc : stackPtr u + 40 = stackPtr s - 336 :=
    scalar_stack_address (frameOffset := 376) state.rsp (by decide) (by decide)
  have agrees : AgreesExcept [.reg 9, .reg 3, .mem (stackPtr s - 360) 8,
      .reg 7, .reg 1, .reg 6, .rip] u t := by
    have h := effect.agrees
    simp only [setupEffect, Effect.components, List.map_cons, List.map_nil, Write.component,
      Operand.component, List.append_nil, List.cons_append, List.nil_append, Nat.reduceDiv] at h
    rwa [address] at h
  have writes : WritesWithin [.reg 9, .reg 3, .mem (stackPtr s - 360) 8,
      .reg 7, .reg 1, .reg 6, .rip] #v[registerRegion s .rdi 96, workRegion s 1400] := by
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    exact ⟨workRegion s 1400, by simp,
      work_contains pre (offset := 360) (by decide) (by decide) ha⟩
  have result := state.after_effect pre (by decide) ready agrees writes (by simp)
  have values := effect.writes
  change t.regValue .r9 = u.regValue .rcx ∧ t.regValue .rbx = u.regValue .rsi ∧
    memLoad t.external (stackPtr u + 16) 64 = u.regValue .rdi ∧
    t.regValue .rdi = stackPtr u + 40 ∧ t.regValue .rcx = 12 ∧
    t.regValue .rsi = 0x202490 at values
  refine ⟨7+n, t, run.trans step, result, effect.rip, ?_, ?_,
    values.2.2.2.1.trans acc, values.2.2.2.2.1, values.2.2.2.2.2, ?_, ?_, ?_⟩
  · exact values.2.1.trans (frame.read (n := 64) (r := 6) (by simp [saveFrame]))
  · exact values.1.trans (frame.read (n := 64) (r := 1) (by simp [saveFrame]))
  · exact (agrees.read (n := 64) (r := 2) (by simp)).trans
      (frame.read (n := 64) (r := 2) (by simp [saveFrame]))
  · exact (agrees.read (n := 64) (r := 8) (by simp)).trans
      (frame.read (n := 64) (r := 8) (by simp [saveFrame]))
  · rw [← address]
    exact values.2.2.1.trans (frame.read (n := 64) (r := 7) (by simp [saveFrame]))

end P256.Proofs.Projective.Multiply.Machine.Loop.Initial
