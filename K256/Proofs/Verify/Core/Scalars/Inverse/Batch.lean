import K256.Proofs.Verify.Core.Scalars.Inverse.Batch.Initialize
import K256.Proofs.Verify.Core.Scalars.Inverse.Batch.Step
import K256.Proofs.Verify.Core.Scalars.Inverse.Batch.Finish

namespace K256.Proofs.Verify.Core.Scalars.Inverse.Batch

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Verify.LIR

private theorem loop (shift : ModularShift) {a : Registers} {m : Ram} {sp : Word} {s : Nat}
    (h : Entry a m sp s) (n : Nat) (more : n < 591) (b : Registers) (p : Ram) (d e : Int)
    (st : LoopState a m sp s n b p d e) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l1097fe, b, p⟩, []⟩ out ∧
      Result a m sp s out := by
  rcases step shift h st more with ⟨c, path, last, zero⟩ | ⟨c, q, d', e', path, last⟩
  · obtain ⟨o, he, res⟩ := finish h last (Or.inr zero)
    exact ⟨o, Program.Exec.of_sem (path.exec he.sem), res⟩
  · by_cases done : n + count n = 591
    · rw [ite_eq_left done] at path
      obtain ⟨o, he, res⟩ := finish h last (Or.inl done)
      exact ⟨o, Program.Exec.of_sem (path.exec he.sem), res⟩
    · rw [ite_eq_right done] at path
      obtain ⟨o, he, res⟩ := loop shift h _ (by
        change n + min 62 (591 - n) ≠ 591 at done
        change n + min 62 (591 - n) < 591
        omega) c q d' e' last
      exact ⟨o, Program.Exec.of_sem (path.exec he.sem), res⟩
termination_by 591 - n
decreasing_by
  change 591 - (n + min 62 (591 - n)) < 591 - n
  omega

theorem execute (shift : ModularShift) {a : Registers} {m : Ram} {sp : Word} {s : Nat}
    (h : Entry a m sp s) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l109490, a, m⟩, []⟩ out ∧
      Result a m sp s out := by
  obtain ⟨b, p, path, st⟩ := initializeLoop h
  obtain ⟨o, he, res⟩ := loop shift h 0 (by decide) b p 0 1 st
  exact ⟨o, Program.Exec.of_sem (path.exec he.sem), res⟩

end K256.Proofs.Verify.Core.Scalars.Inverse.Batch
