import P256.Proofs.Projective.Multiply.Machine.Loop.Initial.Count
import P256.Proofs.Projective.Multiply.Machine.Loop.Initial.CopyArguments

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Loop.Initial

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

theorem initialize_copy [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x103250 768 96 1400)
    (tableCount : s.regValue .rdx = 1) (digitCount : s.regValue .r8 = 1) :
    ∃ fuel t, Advances boundary fuel s t ∧ FrameState s t 96 1400 376 ∧
      t.RIP = 0x1032c8 ∧ ProjectiveAt t (stackPtr s - 336) Projective.identity ∧
      ProjectiveAt t (stackPtr s - 144) Projective.identity ∧
      t.regValue .rbx = s.regValue .rsi ∧ t.regValue .r9 = s.regValue .rcx ∧
      t.regValue .r15 = s.regValue .rsi ∧ t.regValue .r13 = 0 ∧
      t.regValue .r14 = stackPtr s - 144 ∧
      memLoad t.external (stackPtr s - 376) 64 = 65 ∧
      memLoad t.external (stackPtr s - 360) 64 = s.regValue .rdi := by
  obtain ⟨n, u, run, state, rip, point, bx, r9, r15, r13, _, counter, output⟩ :=
    initialize_count pre tableCount digitCount
  obtain ⟨m, v, step, ready, _, effect⟩ := copyArguments_correct boundary pre.outerBoundary u
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x32b0 copyArgumentsBytes
      (by decide) (by decide +kernel)) rip
  have agrees : AgreesExcept [.reg 1, .reg 14, .reg 7, .reg 6, .rip] u v := effect.agrees
  have memory := agrees.external (by simp [Component.Covers])
  have frame := state.after_registers ready agrees (by simp [Component.Covers]) (by simp)
  have dest : stackPtr u + 232 = stackPtr s - 144 :=
    scalar_stack_address (frameOffset := 376) state.rsp (by decide) (by decide)
  have src : stackPtr u + 40 = stackPtr s - 336 :=
    scalar_stack_address (frameOffset := 376) state.rsp (by decide) (by decide)
  have values := effect.writes
  change v.regValue .rcx = 12 ∧ v.regValue .r14 = stackPtr u + 232 ∧
    v.regValue .rdi = stackPtr u + 232 ∧ v.regValue .rsi = stackPtr u + 40 at values
  rw [dest, src] at values
  have readable : MemReadable v (v.regValue .rsi) 96 := by
    rw [values.2.2.2]
    exact readable_of_grow (stack_sub_readable pre.stack (offset := 336)
      (by decide) (by decide)) frame.allocated
  have disjoint : (v.regValue .rsi).toNat + 96 ≤ (v.regValue .rdi).toNat ∨
      (v.regValue .rdi).toNat + 96 ≤ (v.regValue .rsi).toNat := by
    rw [values.2.2.2, values.2.2.1]
    have hsrc : (stackPtr s - (336 : BitVec 64)).toNat = (stackPtr s).toNat - 336 :=
      stack_sub_toNat pre.stack (offset := 336) (by decide)
    have hdst : (stackPtr s - (144 : BitVec 64)).toNat = (stackPtr s).toNat - 144 :=
      stack_sub_toNat pre.stack (offset := 144) (by decide)
    have := stack_bounds pre.stack
    omega
  have input : ProjectiveAt v (v.regValue .rsi) Projective.identity := by
    rw [values.2.2.2]
    exact point.of_bytes_eq (by intro i hi; rw [memory])
  obtain ⟨t, copied, final, finalRip, copy, h⟩ := Copy.copy_to_stack pre frame
    0x32c5 (by decide) (by decide +kernel) effect.rip 144 (by decide) (by decide)
    values.2.2.1 values.1 readable disjoint input
  have apart : RangeApart (stackPtr s - 144) 96 (stackPtr s - 336) 96 :=
    stack_sub_apart pre.stack (by decide) (by decide) (by decide) (by decide)
      (Or.inr (by decide))
  refine ⟨n+m+12, t, (run.trans step).trans copied, final, finalRip, ?_, copy,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply input.of_bytes_eq
    intro i hi
    rw [values.2.2.2]
    apply h.byte
    intro c hc covers
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact covers.elim
    obtain ⟨j, hj, eq⟩ := covers
    exact apart j hj i hi eq.symm
  · exact (h.read (n := 64) (r := 3) (by simp)).trans
      ((agrees.read (n := 64) (r := 3) (by simp)).trans bx)
  · exact (h.read (n := 64) (r := 9) (by simp)).trans
      ((agrees.read (n := 64) (r := 9) (by simp)).trans r9)
  · exact (h.read (n := 64) (r := 15) (by simp)).trans
      ((agrees.read (n := 64) (r := 15) (by simp)).trans r15)
  · exact (h.read (n := 64) (r := 13) (by simp)).trans
      ((agrees.read (n := 64) (r := 13) (by simp)).trans r13)
  · exact (h.read (n := 64) (r := 14) (by simp)).trans values.2.1
  · rw [memLoad_agrees_apart h]
    · rw [memory]; exact counter
    · intro a len member
      simp only [List.mem_cons, List.not_mem_nil, or_false, Component.mem.injEq,
        reduceCtorEq, false_or, or_false] at member
      obtain ⟨rfl, rfl⟩ := member
      exact stack_sub_apart pre.stack (by decide) (by decide)
        (by decide) (by decide) (Or.inr (by decide))
  · rw [memLoad_agrees_apart h]
    · rw [memory]; exact output
    · intro a len member
      simp only [List.mem_cons, List.not_mem_nil, or_false, Component.mem.injEq,
        reduceCtorEq, false_or, or_false] at member
      obtain ⟨rfl, rfl⟩ := member
      exact stack_sub_apart pre.stack (by decide) (by decide)
        (by decide) (by decide) (Or.inr (by decide))

end P256.Proofs.Projective.Multiply.Machine.Loop.Initial
