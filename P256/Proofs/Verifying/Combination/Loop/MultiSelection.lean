import P256.Proofs.Verifying.Combination.Loop.MultiSelection.Read
import P256.Proofs.Verifying.Combination.Loop.MultiSelection.Branch
import P256.Proofs.Verifying.Combination.Loop.MultiSelection.Sign
import P256.Proofs.Verifying.Combination.Loop.MultiSelection.PositiveIndex
import P256.Proofs.Verifying.Combination.Loop.MultiSelection.Positive

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Loop.Multi

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem selection_correct (negative : NegativeCorrect) : SelectionCorrect := by
  intro bindings s t boundary tables digits p q point u v k left pre state hu hv
  let d : Int := ((Naf.digits (if left then u else v))[k]?).getD 0
  have bound : k < 257 := by
    have h := state.bounded
    have hlu := Naf.digits_length u hu
    have hlv := Naf.digits_length v hv
    omega
  have hn : (if left then u else v) < 2^256 := by cases left <;> assumption
  have hd : Naf.ValidDigit d := Naf.digits_getD_valid hn k
  obtain ⟨a, runA, stateA, digitA⟩ := Selection.read_digit pre state bound
  obtain ⟨b, runB, stateB, digitB⟩ := Selection.digit_branch pre stateA hd digitA
  by_cases hz : d = 0
  · refine ⟨3, b, runA.trans runB, Or.inl ⟨hz, ?_⟩⟩
    simpa only [hz, ↓reduceIte] using stateB
  · have stateB' : DigitState s b tables digits p q u v (k+1) point left 0x10f2d9 := by
      simpa only [hz, ↓reduceIte] using stateB
    obtain ⟨c, runC, stateC, rdiC, raxC⟩ :=
      Selection.select_sign_branch pre stateB' d hd hz (digitB.trans digitA)
    by_cases hneg : d < 0
    · have ripC : c.RIP = 0x10f1d0 := by simpa only [hneg, ↓reduceIte] using stateC.rip
      have lowC : (c.regValue .rax).setWidth 8 = BitVec.ofInt 8 d := by
        rw [raxC, BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]
      obtain ⟨fuel, w, run, result⟩ := negative s c boundary tables digits p q point u v (k+1) left d
        pre stateC.toDigitData ripC rdiC lowC hd hneg
      exact ⟨1+2+3+fuel, w, ((runA.trans runB).trans runC).trans run, Or.inr ⟨hz, result⟩⟩
    · have positive : 0 < d := by omega
      have stateC' : DigitState s c tables digits p q u v (k+1) point left 0x10f2e4 := by
        simpa only [hneg, ↓reduceIte] using stateC
      obtain ⟨e, runE, stateE, indexE⟩ := Selection.select_positive_index pre stateC' d hd positive rdiC raxC
      obtain ⟨fuel, w, run, result⟩ := Selection.select_positive pre stateE
        ⟨d.natAbs / 2, Selection.digit_index_lt hd⟩ indexE
      have lookup := Selection.signedLookup_nonzero (Table.oddTable (if left then p else q)) hd hz
      simp only [hneg, ↓reduceIte] at lookup
      refine ⟨1+2+3+3+fuel, w, (((runA.trans runB).trans runC).trans runE).trans run,
        Or.inr ⟨hz, ?_⟩⟩
      rw [lookup]
      exact result

end P256.Proofs.Verifying.Combination.Loop.Multi
