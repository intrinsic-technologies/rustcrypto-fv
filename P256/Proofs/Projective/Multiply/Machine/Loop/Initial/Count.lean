import P256.Proofs.Projective.Multiply.Machine.Loop.Initial.Ready
import P256.Proofs.Projective.Multiply.Machine.Loop.Initial.Counter

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Loop.Initial

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

theorem initialize_count [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x103250 768 96 1400)
    (tableCount : s.regValue .rdx = 1) (digitCount : s.regValue .r8 = 1) :
    ∃ fuel t, Advances boundary fuel s t ∧ FrameState s t 96 1400 376 ∧
      t.RIP = 0x1032b0 ∧ ProjectiveAt t (stackPtr s - 336) Projective.identity ∧
      t.regValue .rbx = s.regValue .rsi ∧ t.regValue .r9 = s.regValue .rcx ∧
      t.regValue .r15 = s.regValue .rsi ∧ t.regValue .r13 = 0 ∧
      t.regValue .rax = 65 ∧ memLoad t.external (stackPtr s - 376) 64 = 65 ∧
      memLoad t.external (stackPtr s - 360) 64 = s.regValue .rdi := by
  obtain ⟨n, u, run, state, rip, point, bx, r9, dx, _, output⟩ :=
    initialize_one pre tableCount digitCount
  obtain ⟨m, t, step, ready, _, effect⟩ := counter_correct boundary pre.outerBoundary u
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x3290 counterBytes
      (by decide) (by decide +kernel))
    ⟨rip, by simpa using (stack_writable pre state (offset := 0)
        (len := 8) (by decide) (by decide) (by decide)),
      by simpa [Extracted.textAddress] using (stack_code pre state (offset := 0) (len := 8) (codeOffset := 0x3290)
        (codeLen := 32) (by decide) (by decide) (by decide))⟩
  have agrees : AgreesExcept [.reg 0, .mem (stackPtr s - 376) 8,
      .reg 13, .reg 15, .flags, .rip] u t := by
    have h := effect.agrees
    simp only [counterEffect, Effect.components, List.map_cons, List.map_nil, Write.component,
      Operand.component, List.cons_append, List.nil_append, Nat.reduceDiv] at h
    rwa [state.rsp] at h
  have writes : WritesWithin [.reg 0, .mem (stackPtr s - 376) 8,
      .reg 13, .reg 15, .flags, .rip] #v[registerRegion s .rdi 96, workRegion s 1400] := by
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    exact ⟨workRegion s 1400, by simp, work_contains pre (by decide) (by decide) ha⟩
  have frame := state.after_effect pre (by decide) ready agrees writes (by simp)
  have values := effect.writes
  change t.regValue .rax = (u.regValue .rdx <<< 6) + u.regValue .rdx ∧
    memLoad t.external (stackPtr u) 64 = (u.regValue .rdx <<< 6) + u.regValue .rdx ∧
    t.regValue .r13 = 0 ∧ t.regValue .r15 = u.regValue .rbx at values
  have value : (u.regValue .rdx <<< 6) + u.regValue .rdx = 65 := by rw [dx]; decide
  rw [value, state.rsp] at values
  have apart : RangeApart (stackPtr s - 376) 8 (stackPtr s - 336) 96 :=
    stack_sub_apart pre.stack (by decide) (by decide) (by decide) (by decide)
      (Or.inl (by decide))
  refine ⟨n+m, t, run.trans step, frame, effect.rip, ?_, ?_, ?_,
    values.2.2.2.trans bx, values.2.2.1, values.1, values.2.1, ?_⟩
  · apply point.of_bytes_eq
    intro i hi
    apply agrees.byte
    intro c hc covers
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact covers.elim
    obtain ⟨j, hj, eq⟩ := covers
    exact apart j hj i hi eq.symm
  · exact (agrees.read (n := 64) (r := 3) (by simp)).trans bx
  · exact (agrees.read (n := 64) (r := 9) (by simp)).trans r9
  · rw [memLoad_agrees_apart agrees]
    · exact output
    · intro a len member
      simp only [List.mem_cons, List.not_mem_nil, or_false, Component.mem.injEq,
        reduceCtorEq, false_or, or_false] at member
      obtain ⟨rfl, rfl⟩ := member
      exact stack_sub_apart pre.stack (by decide) (by decide)
        (by decide) (by decide) (Or.inl (by decide))

end P256.Proofs.Projective.Multiply.Machine.Loop.Initial
