import P256.Proofs.Verifying.Combination.Loop.Accumulator
import P256.Proofs.Verifying.Combination.Loop.MultiRound
import P256.Proofs.Verifying.Combination.Loop.MultiInitialize
import P256.Proofs.Verifying.Combination.Output.MultiReturn

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Loop.Multi

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem run_rounds [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {tables digits : BitVec 64} {p q : Projective} {u v : Nat}
    (doubleCorrect : DoubleCorrect) (selectCorrect : SelectionCorrect)
    (pre : MultiPre s boundary tables digits) (hu : u < 2^256) (hv : v < 2^256)
    (k : Nat) (t : RamState)
    (state : RoundState s t tables digits p q u v k (remainingAccumulator p q u v k)) :
    ∃ fuel w, Advances boundary fuel t w ∧ Memory s w tables digits p q u v ∧
      w.RIP = 0x10f301 ∧
      ProjectiveAt w (stackPtr s - 336) (Algebra.linearCombination p q u v) ∧
      memLoad w.external (stackPtr s - 392) 64 = s.regValue .rdi := by
  induction k generalizing t with
  | zero => exact (Nat.not_lt_zero _ state.positive).elim
  | succ k ih =>
    obtain ⟨fa, a, runA, stateA⟩ := round_body doubleCorrect selectCorrect pre state hu hv
    have stateA' : DigitState s a tables digits p q u v (k+1)
        (remainingAccumulator p q u v k) false 0x10f2b8 := by
      rw [remainingAccumulator_step p q u v k (by have h := state.bounded; omega)]
      exact stateA
    have bound : k < 257 := by
      have h := state.bounded
      have hlu := Naf.digits_length u hu
      have hlv := Naf.digits_length v hv
      omega
    obtain ⟨fb, b, runB, zero | next⟩ := next_right pre stateA' bound
    · obtain ⟨zero, memoryB, ripB, valueB, outputB⟩ := zero
      subst k
      exact ⟨fa+fb, b, runA.trans runB, memoryB, ripB, valueB, outputB⟩
    · obtain ⟨fw, w, runW, memoryW, ripW, valueW, outputW⟩ := ih b next
      exact ⟨fa+fb+fw, w, (runA.trans runB).trans runW, memoryW, ripW, valueW, outputW⟩

theorem multi_of_stages (doubleCorrect : DoubleCorrect) (selectCorrect : SelectionCorrect) :
    MultiCorrect := by
  intro inst s boundary tables digits p q u v pre leftTable rightTable leftDigits rightDigits hu hv hp hq
  have represents : RepresentsSum (Algebra.linearCombination p q u v) p q u v :=
    ⟨Algebra.linearCombination_valid p q hp hq u v hu hv,
      Algebra.linearCombination_toAffine p q hp hq u v hu hv⟩
  obtain ⟨fa, a, runA, zero | round⟩ := initialize_correct pre leftTable rightTable leftDigits rightDigits hu hv
  · obtain ⟨zero, memoryA, ripA, valueA, outputA⟩ := zero
    have pointEq : Algebra.linearCombination p q u v = Projective.identity := by
      rw [← remainingAccumulator_zero, ← zero]
      exact remainingAccumulator_initial p q u v
    have valueA' : ProjectiveAt a (stackPtr s - 336) (Algebra.linearCombination p q u v) := by
      rw [pointEq]
      exact valueA
    obtain ⟨w, result, valueW⟩ := Return.finish pre.toCalleePre memoryA.toFrameState ripA valueA' outputA ⟨fa, runA⟩
    exact ⟨w, Algebra.linearCombination p q u v, result, valueW, represents⟩
  · have stateA : RoundState s a tables digits p q u v
        (max (Naf.digits u).length (Naf.digits v).length)
        (remainingAccumulator p q u v (max (Naf.digits u).length (Naf.digits v).length)) := by
      rw [remainingAccumulator_initial]
      exact round
    obtain ⟨fb, b, runB, memoryB, ripB, valueB, outputB⟩ :=
      run_rounds doubleCorrect selectCorrect pre hu hv _ a stateA
    obtain ⟨w, result, valueW⟩ := Return.finish pre.toCalleePre memoryB.toFrameState ripB valueB outputB
      ⟨fa+fb, runA.trans runB⟩
    exact ⟨w, Algebra.linearCombination p q u v, result, valueW, represents⟩

end P256.Proofs.Verifying.Combination.Loop.Multi
