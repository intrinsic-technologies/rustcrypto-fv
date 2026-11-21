import P256.Proofs.Projective.Multiply.Machine.Loop.Initial.Correct
import P256.Proofs.Projective.Multiply.Machine.Loop.Round.Correct
import P256.Proofs.Projective.Multiply.Machine.Loop.Finish
import P256.Proofs.Projective.Multiply.Machine.Loop.Iterate
import P256.Proofs.Projective.Multiply.Machine.Loop.Value

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Loop

open P256.Spec P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program

theorem loop_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {table : Fin 8 → Projective} (pre : Pre s boundary)
    (input : Lookup.TableAt s (s.regValue .rsi) table) :
    ∃ t, CalleeResult s t boundary 96 1400 ∧
      ProjectiveAt t (s.regValue .rdi) (ProjectiveLoop.linearCombination table (Round.digits s)) := by
  obtain ⟨a, t, runT, stateT⟩ := Initial.initialize_loop pre input
  obtain ⟨b, u, runU, stateU⟩ := iterate_rounds (Round.round_correct pre input) stateT
    (show 64 ≤ 64 by decide)
  exact finish pre stateU ⟨a+b, runT.trans runU⟩

theorem multiply_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {point : Projective} {d : Nat} (pre : Pre s boundary)
    (input : Lookup.TableAt s (s.regValue .rsi) (Projective.table point))
    (bytes : Bytes s.external (s.regValue .rcx) 65
      (fun i => UInt8.ofBitVec (ProjectiveRadix.digitByte d i)))
    (valid : point.valid) (bound : d < 2^256) :
    ∃ t result, CalleeResult s t boundary 96 1400 ∧
      ProjectiveAt t (s.regValue .rdi) result ∧ result.valid ∧
      result.toAffine = Points.mul d point.toAffine := by
  obtain ⟨t, output, represented⟩ := loop_correct pre input
  rw [linearCombination_eq_model bytes] at represented
  exact ⟨t, model point d, output, represented, model_correct point valid d bound⟩

end P256.Proofs.Projective.Multiply.Machine.Loop
