import P256.Proofs.Verifying.Combination.Loop.MultiDigitEntryLoads
import P256.Proofs.Verifying.Combination.Loop.MultiDigitEntryState
import P256.Proofs.Verifying.Combination.Loop.MultiDigitEntryBound
import P256.Proofs.Verifying.Combination.Loop.MultiAdd
import P256.Proofs.Verifying.Combination.Loop.MultiNext

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Loop.Multi

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem apply_digit [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {tables digits : BitVec 64} {p q point : Projective} {u v k : Nat} {left : Bool}
    (selectCorrect : SelectionCorrect) (pre : MultiPre s boundary tables digits)
    (state : DigitState s t tables digits p q u v (k+1) point left)
    (hu : u < 2^256) (hv : v < 2^256) :
    ∃ fuel w, Advances boundary fuel t w ∧
      DigitState s w tables digits p q u v (k+1)
        (Algebra.addDigit (Table.oddTable (if left then p else q)) point
          (((Naf.digits (if left then u else v))[k]?).getD 0)) left 0x10f2b8 := by
  obtain ⟨fa, a, runA, zero | nonzero⟩ :=
    selectCorrect s t boundary tables digits p q point u v k left pre state hu hv
  · obtain ⟨zero, stateA⟩ := zero
    refine ⟨fa, a, runA, ?_⟩
    simpa only [Algebra.addDigit, ite_eq_left zero] using stateA
  · obtain ⟨nonzero, stateA⟩ := nonzero
    obtain ⟨fb, b, runB, stateB⟩ := add_selected pre stateA
    refine ⟨fa+fb, b, runA.trans runB, ?_⟩
    simpa only [Algebra.addDigit, ite_eq_right nonzero] using stateB

theorem round_body [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {tables digits : BitVec 64} {p q point : Projective} {u v k : Nat}
    (doubleCorrect : DoubleCorrect) (selectCorrect : SelectionCorrect)
    (pre : MultiPre s boundary tables digits)
    (state : RoundState s t tables digits p q u v (k+1) point)
    (hu : u < 2^256) (hv : v < 2^256) :
    ∃ fuel w, Advances boundary fuel t w ∧
      DigitState s w tables digits p q u v (k+1)
        (Algebra.addDigit (Table.oddTable q)
          (Algebra.addDigit (Table.oddTable p) point.double (((Naf.digits u)[k]?).getD 0))
          (((Naf.digits v)[k]?).getD 0)) false 0x10f2b8 := by
  obtain ⟨fa, a, runA, stateA⟩ :=
    doubleCorrect s t boundary tables digits p q point u v (k+1) pre state
  obtain ⟨b, runB, stateB, remainingB, tableB⟩ := load_inner_pointers pre stateA
  obtain ⟨c, runC, stateC⟩ := save_inner_cursor pre stateB remainingB tableB
  have bound : k+1 ≤ 257 := by
    have h := state.bounded
    have hlu := Naf.digits_length u hu
    have hlv := Naf.digits_length v hv
    omega
  obtain ⟨d, runD, stateD⟩ := enter_digits pre stateC bound
  obtain ⟨fe, e, runE, stateE⟩ := apply_digit selectCorrect pre stateD hu hv
  obtain ⟨ff, f, runF, stateF⟩ := next_left pre stateE
  obtain ⟨fw, w, runW, stateW⟩ := apply_digit selectCorrect pre stateF hu hv
  exact ⟨fa+2+1+2+fe+ff+fw, w,
    (((((runA.trans runB).trans runC).trans runD).trans runE).trans runF).trans runW, stateW⟩

end P256.Proofs.Verifying.Combination.Loop.Multi
