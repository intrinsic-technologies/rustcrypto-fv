import P256.Proofs.Projective.Multiply.Machine.Loop.Initial.FirstAdd
import P256.Proofs.Projective.Multiply.Machine.Loop.Initial.OutputArguments
import P256.Proofs.Projective.Multiply.Machine.Loop.Round.State
import P256.Proofs.Projective.Copy

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Loop.Initial

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

theorem initialize_output [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {table : Fin 8 → Projective} (pre : Pre s boundary)
    (input : Lookup.TableAt s (s.regValue .rsi) table) :
    ∃ fuel t, Advances boundary fuel s t ∧ FrameState s t 96 1400 376 ∧
      t.RIP = 0x103302 ∧
      ProjectiveAt t (stackPtr s - 336) (ProjectiveLoop.accumulator table (Round.digits s) 0) ∧
      t.regValue .rbx = s.regValue .rsi ∧ t.regValue .r9 = s.regValue .rcx ∧
      t.regValue .r13 = 0 ∧
      memLoad t.external (stackPtr s - 376) 64 = 65 ∧
      memLoad t.external (stackPtr s - 360) 64 = s.regValue .rdi := by
  obtain ⟨n, u, run, state, rip, _, point, bx, bp, _, r13, r14, _, counter, output⟩ :=
    initialize_first_add pre input
  obtain ⟨m, v, prepare, ready, _, effect⟩ := outputArguments_correct boundary pre.outerBoundary u
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x32ef outputArgumentsBytes
      (by decide) (by decide +kernel)) rip
  have agrees : AgreesExcept [.reg 9, .reg 1, .reg 7, .reg 6, .rip] u v := effect.agrees
  have memory := agrees.external (by simp [Component.Covers])
  have frame := state.after_registers ready agrees (by simp [Component.Covers]) (by simp)
  have dest : stackPtr u + 40 = stackPtr s - 336 :=
    scalar_stack_address (frameOffset := 376) state.rsp (by decide) (by decide)
  have values := effect.writes
  change v.regValue .r9 = u.regValue .rbp ∧ v.regValue .rcx = 12 ∧
    v.regValue .rdi = stackPtr u + 40 ∧ v.regValue .rsi = u.regValue .r14 at values
  rw [dest, r14, bp] at values
  have readable : MemReadable v (v.regValue .rsi) 96 := by
    rw [values.2.2.2]
    exact readable_of_grow (stack_sub_readable pre.stack (offset := 144)
      (by decide) (by decide)) frame.allocated
  have disjoint : (v.regValue .rsi).toNat + 96 ≤ (v.regValue .rdi).toNat ∨
      (v.regValue .rdi).toNat + 96 ≤ (v.regValue .rsi).toNat := by
    rw [values.2.2.2, values.2.2.1]
    have hsrc : (stackPtr s - (144 : BitVec 64)).toNat = (stackPtr s).toNat - 144 :=
      stack_sub_toNat pre.stack (offset := 144) (by decide)
    have hdst : (stackPtr s - (336 : BitVec 64)).toNat = (stackPtr s).toNat - 336 :=
      stack_sub_toNat pre.stack (offset := 336) (by decide)
    have := stack_bounds pre.stack
    omega
  have pointV : ProjectiveAt v (v.regValue .rsi)
      (ProjectiveLoop.accumulator table (Round.digits s) 0) := by
    rw [values.2.2.2]
    exact point.of_bytes_eq (by intro i hi; rw [memory])
  obtain ⟨t, copied, final, finalRip, value, h⟩ := Copy.copy_to_stack pre.toCalleePre frame
    0x32ff (by decide) (by decide +kernel) effect.rip 336 (by decide) (by decide)
    values.2.2.1 values.2.1 readable disjoint pointV
  have word (offset : Nat) (ho : offset ≤ 1400) (ha : 336 + 8 ≤ offset) :
      memLoad t.external (stackPtr s - BitVec.ofNat 64 offset) 64 =
        memLoad u.external (stackPtr s - BitVec.ofNat 64 offset) 64 := by
    rw [memLoad_agrees_apart h, memory]
    intro a len member
    simp only [List.mem_cons, List.not_mem_nil, or_false, Component.mem.injEq,
      reduceCtorEq, false_or, or_false] at member
    obtain ⟨rfl, rfl⟩ := member
    exact stack_sub_apart pre.stack (by decide) ho (by decide) (by omega) (Or.inr ha)
  refine ⟨n+m+12, t, (run.trans prepare).trans copied, final, finalRip, value, ?_, ?_, ?_,
    (word 376 (by decide) (by decide)).trans counter,
    (word 360 (by decide) (by decide)).trans output⟩
  · exact (h.read (n := 64) (r := 3) (by simp)).trans
      ((agrees.read (n := 64) (r := 3) (by simp)).trans bx)
  · exact (h.read (n := 64) (r := 9) (by simp)).trans values.1
  · exact (h.read (n := 64) (r := 13) (by simp)).trans
      ((agrees.read (n := 64) (r := 13) (by simp)).trans r13)

end P256.Proofs.Projective.Multiply.Machine.Loop.Initial
