import P256.Proofs.Projective.Multiply.Machine.Loop.Initial.Output
import P256.Proofs.Projective.Multiply.Machine.Loop.Initial.Exit
import P256.Proofs.Projective.Multiply.Machine.Loop.Initial.TailArguments
import P256.Proofs.Projective.Multiply.Machine.Loop.Initial.TailMemory

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Loop.Initial

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

theorem initialize_loop [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {table : Fin 8 → Projective} (pre : Pre s boundary)
    (input : Lookup.TableAt s (s.regValue .rsi) table) :
    ∃ fuel t, Advances boundary fuel s t ∧ Round.LoopState s t table 0 := by
  obtain ⟨n, u, run, state, rip, point, bx, r9, r13, counter, output⟩ :=
    initialize_output pre input
  obtain ⟨v, branch, frameV, ripV, agrV⟩ := initial_branch pre state rip r13 counter
  obtain ⟨m, w, args, ready, _, effect⟩ := tailArguments_correct boundary pre.outerBoundary v
    (readyToStep frameV.machine frameV.bindingsSupported)
    (programText_slice (programLoaded_codeIn frameV.loaded) 0x3313 tailArgumentsBytes
      (by decide) (by decide +kernel)) ripV
  have agrW : AgreesExcept [.reg 9, .reg 15, .reg 13, .reg 0, .flags, .rip] v w := effect.agrees
  have frameW := frameV.after_registers ready agrW (by simp [Component.Covers]) (by simp)
  have memory : w.external = u.external :=
    (agrV.trans agrW).external (by simp [Component.Covers])
  have countW : (Operand.mem (stackPtr s - 376) : Operand 64).read w = 65 := by
    change memLoad w.external _ 64 = _
    rw [memory]
    exact counter
  obtain ⟨t, install, final, finalRip, finalR14, tableWord, agrT⟩ :=
    tail_install pre frameW effect.rip countW
  have values := effect.writes
  change w.regValue .r9 = v.regValue .r9 + 63 ∧ w.regValue .r15 = 64 ∧
    w.regValue .r13 = stackPtr v + 40 ∧ w.regValue .rax = stackPtr v + 232 at values
  have memoryWord (offset : Nat) (ho : offset ≤ 1400) (ha : 352+8 ≤ offset) :
      memLoad t.external (stackPtr s - BitVec.ofNat 64 offset) 64 =
        memLoad u.external (stackPtr s - BitVec.ofNat 64 offset) 64 := by
    rw [memLoad_agrees_apart agrT, memory]
    intro a len member
    simp only [List.mem_cons, List.not_mem_nil, or_false, Component.mem.injEq,
      reduceCtorEq, or_false] at member
    obtain ⟨rfl, rfl⟩ := member
    exact stack_sub_apart pre.stack (by decide) ho (by decide) (by omega) (Or.inr ha)
  have bxW : w.regValue .rbx = s.regValue .rsi :=
    ((agrV.trans agrW).read (n := 64) (r := 3) (by simp)).trans bx
  refine ⟨n+4+m+3, t, ((run.trans branch).trans args).trans install,
    final, by decide, finalRip, ?_, ?_, finalR14, ?_,
    (agrT.read (n := 64) (r := 3) (by simp)).trans bxW, ?_, ?_,
    (memoryWord 376 (by decide) (by decide)).trans counter,
    (memoryWord 360 (by decide) (by decide)).trans output, tableWord.trans bxW⟩
  · apply point.of_bytes_eq
    intro i hi
    have h : t.external[stackPtr s - 336 + BitVec.ofNat 64 i]? =
        w.external[stackPtr s - 336 + BitVec.ofNat 64 i]? := by
      apply agrT.byte
      intro c hc covered
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      all_goals try exact covered.elim
      obtain ⟨j, hj, eq⟩ := covered
      exact stack_sub_apart pre.stack (a := 352) (b := 336)
        (by decide) (by decide) (by decide) (by decide) (Or.inl (by decide)) j hj i hi eq.symm
    rw [memory] at h
    exact h
  · exact (agrT.read (n := 64) (r := 13) (by simp)).trans
      (values.2.2.1.trans (scalar_stack_address frameV.rsp (by decide) (by decide)))
  · exact (agrT.read (n := 64) (r := 15) (by simp)).trans values.2.1
  · have vr9 : v.regValue .r9 = s.regValue .rcx := (agrV.read (n := 64) (r := 9) (by simp)).trans r9
    have tr9 : t.regValue .r9 = v.regValue .r9 + 63 := (agrT.read (n := 64) (r := 9) (by simp)).trans values.1
    rw [tr9, vr9]
    change _ = s.regValue .rcx + 64 - 1
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  · exact (agrT.read (n := 64) (r := 0) (by simp)).trans
      (values.2.2.2.trans (scalar_stack_address frameV.rsp (by decide) (by decide)))

end P256.Proofs.Projective.Multiply.Machine.Loop.Initial
