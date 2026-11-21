import P256.Proofs.Projective.Multiply.Machine.Loop.Initial.Start
import P256.Proofs.Projective.Copy
import P256.Proofs.Projective.Constants
import P256.Proofs.Program.WrapperMemory

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Loop.Initial

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

theorem initialize_identity [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x103250 768 96 1400) :
    ∃ fuel t, Advances boundary fuel s t ∧ FrameState s t 96 1400 376 ∧
      t.RIP = 0x103280 ∧ ProjectiveAt t (stackPtr s - 336) Projective.identity ∧
      t.regValue .rbx = s.regValue .rsi ∧ t.regValue .r9 = s.regValue .rcx ∧
      t.regValue .rdx = s.regValue .rdx ∧ t.regValue .r8 = s.regValue .r8 ∧
      memLoad t.external (stackPtr s - 360) 64 = s.regValue .rdi := by
  obtain ⟨n, u, run, state, rip, bx, r9, dst, count, src, dx, r8, output⟩ := setup_entry pre
  have source : MemReadable u (u.regValue .rsi) 96 := by
    rw [src]
    exact Constants.identity_readable state.loaded
  have value : ProjectiveAt u (u.regValue .rsi) Projective.identity := by
    rw [src]
    exact Constants.identity_at state.loaded
  have disjoint : (u.regValue .rsi).toNat + 96 ≤ (u.regValue .rdi).toNat ∨
      (u.regValue .rdi).toNat + 96 ≤ (u.regValue .rsi).toNat := by
    rw [src, dst]
    exact Constants.identity_stack_disjoint pre (by decide) (by decide)
  obtain ⟨t, copied, frame, finalRip, point, agrees⟩ := Copy.copy_to_stack pre state
    0x327d (by decide) (by decide +kernel) rip 336 (by decide) (by decide)
    dst count source disjoint value
  refine ⟨n + 12, t, run.trans copied, frame, finalRip, point, ?_, ?_, ?_, ?_, ?_⟩
  · exact (agrees.read (n := 64) (r := 3) (by simp)).trans bx
  · exact (agrees.read (n := 64) (r := 9) (by simp)).trans r9
  · exact (agrees.read (n := 64) (r := 2) (by simp)).trans dx
  · exact (agrees.read (n := 64) (r := 8) (by simp)).trans r8
  · rw [memLoad_agrees_apart agrees]
    · exact output
    · intro a len member
      simp only [List.mem_cons, List.not_mem_nil, or_false, Component.mem.injEq,
        reduceCtorEq, false_or, or_false] at member
      obtain ⟨rfl, rfl⟩ := member
      exact stack_sub_apart pre.stack (by decide) (by decide)
        (by decide) (by decide) (Or.inr (by decide))

end P256.Proofs.Projective.Multiply.Machine.Loop.Initial
