import P256.Proofs.Projective.Multiply.Machine.Loop.Round.State
import P256.Proofs.Projective.Multiply.Correct

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply

open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem ProjectiveLoop.accumulator_congr (table : Fin 8 → Projective)
    {left right : Nat → BitVec 8} (same : ∀ i < 65, left i = right i) (n : Nat) :
    ProjectiveLoop.accumulator table left n = ProjectiveLoop.accumulator table right n := by
  induction n with
  | zero => simp only [ProjectiveLoop.accumulator, same 64 (by decide)]
  | succ n ih => simp only [ProjectiveLoop.accumulator, ih, same (63-n) (by omega)]

theorem Machine.Loop.linearCombination_eq_model {s : RamState} {d : Nat} {point : Projective}
    (bytes : Bytes s.external (s.regValue .rcx) 65
      (fun i => UInt8.ofBitVec (ProjectiveRadix.digitByte d i))) :
    ProjectiveLoop.linearCombination (Projective.table point) (Machine.Loop.Round.digits s) =
      model point d := by
  apply ProjectiveLoop.accumulator_congr
  intro i hi
  have hb := bytes i hi
  change memLoad s.external (s.regValue .rcx + BitVec.ofNat 64 i) 8 = _
  have one : Bytes s.external (s.regValue .rcx + BitVec.ofNat 64 i) 1
      (storedByte (ProjectiveRadix.digitByte d i)) := by
    intro j hj
    have eq : j = 0 := by omega
    subst j
    simpa [storedByte] using hb
  exact one.memLoad (by decide) (by decide)

end P256.Proofs.Projective.Multiply
