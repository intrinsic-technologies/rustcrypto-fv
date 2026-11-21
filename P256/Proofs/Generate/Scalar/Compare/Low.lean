import P256.Proofs.Generate.Scalar.Compare.LowWord
import P256.Proofs.Generate.Scalar.Compare.Setup

set_option autoImplicit false

namespace P256.Proofs.Generate.Scalar

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess
  X86Proofs

theorem low_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (hout : ¬ InProgram boundary.rip) (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (pre : ComparePre 0x112efb s) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      ComparePre 0x112f2c t ∧ AgreesExcept (compareFrame s) s t ∧
      t.regValue .rcx = 0 ∧
      t.regValue .rdx = (-((~~~(s.regValue .r13) |||
        (0x0c46353d039cdaaf + s.regValue .r13)) >>> 63)).sshiftRight 63 := by
  obtain ⟨n0, t0, run0, rd0, ld0, p0, h0, f0⟩ :=
    compare_run (s := s) (q := 0x112f15) (offset := 0x12efb)
      (low_word_correct boundary hout) (by decide +kernel) (by decide +kernel)
      ready loaded pre pre.rip rfl
      (by simp [lowWordEffect, Effect.components, compareFrame])
  obtain ⟨n1, t1, run1, rd1, ld1, p1, h1, f1⟩ :=
    compare_run (s := t0) (q := 0x112f2c) (offset := 0x12f15)
      (setup_correct boundary hout) (by decide +kernel) (by decide +kernel)
      rd0 ld0 p0 p0 rfl
      (by simp [setupEffect, Effect.components, compareFrame])
  refine ⟨n0+n1, t1, run0.trans run1, rd1, ld1, p1, compare_trans f0 f1,
    h1.writes.2.2.1, ?_⟩
  have h := h1.writes.2.2.2
  change t1.regValue .rdx = (-t0.regValue .rcx).sshiftRight 63 at h
  exact h.trans (congrArg (fun x : BitVec 64 => (-x).sshiftRight 63) h0.writes.2)

end P256.Proofs.Generate.Scalar
