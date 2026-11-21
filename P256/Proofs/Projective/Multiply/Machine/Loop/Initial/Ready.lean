import P256.Proofs.Projective.Multiply.Machine.Loop.Initial.Identity
import P256.Proofs.Projective.Multiply.Machine.Loop.Initial.Branch

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Loop.Initial

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

theorem initialize_one [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x103250 768 96 1400)
    (tableCount : s.regValue .rdx = 1) (digitCount : s.regValue .r8 = 1) :
    ∃ fuel t, Advances boundary fuel s t ∧ FrameState s t 96 1400 376 ∧
      t.RIP = 0x103290 ∧ ProjectiveAt t (stackPtr s - 336) Projective.identity ∧
      t.regValue .rbx = s.regValue .rsi ∧ t.regValue .r9 = s.regValue .rcx ∧
      t.regValue .rdx = 1 ∧ t.regValue .r8 = 1 ∧
      memLoad t.external (stackPtr s - 360) 64 = s.regValue .rdi := by
  obtain ⟨n, u, run, state, rip, point, bx, r9, dx, r8, output⟩ := initialize_identity pre
  obtain ⟨m, t, branch, finalState, finalRip, finalDx, agrees⟩ :=
    count_branch pre state rip (dx.trans tableCount) (r8.trans digitCount)
  have memory := agrees.external (by simp [Component.Covers])
  refine ⟨n+m, t, run.trans branch, finalState, finalRip, ?_, ?_, ?_, finalDx, ?_, ?_⟩
  · exact point.of_bytes_eq (by intro i hi; rw [memory])
  · exact (agrees.read (n := 64) (r := 3) (by simp)).trans bx
  · exact (agrees.read (n := 64) (r := 9) (by simp)).trans r9
  · exact (agrees.read (n := 64) (r := 8) (by simp)).trans (r8.trans digitCount)
  · rw [memory]
    exact output

end P256.Proofs.Projective.Multiply.Machine.Loop.Initial
