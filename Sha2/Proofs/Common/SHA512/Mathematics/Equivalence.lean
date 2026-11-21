import Sha2.Proofs.Common.SHA512.Mathematics.Model

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512

open Sha2.Proofs.NIST

private abbrev StateTuple := UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64

private def State.toTuple (s : State) : StateTuple := (s.a, s.b, s.c, s.d, s.e, s.f, s.g, s.h)

private def State.ofTuple (s : StateTuple) : State :=
  ⟨s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, s.2.2.2.2.2.1,
    s.2.2.2.2.2.2.1, s.2.2.2.2.2.2.2⟩

private def tupleRound (words : Array UInt64) (s : StateTuple) (i : Nat) : StateTuple :=
  (round (State.ofTuple s) SHA512.roundConstants[i]! words[i]!).toTuple

private theorem rounds_eq_tupleFold (initial : StateTuple) (words : Array UInt64) (n : Nat) :
    rounds (State.ofTuple initial) words n =
      State.ofTuple ((List.range n).foldl (tupleRound words) initial) := by
  unfold rounds
  apply List.foldl_hom State.ofTuple
  intro s i
  rfl

theorem compressModel_eq_compress (hash : Array UInt64) (block : Array Bool) :
    compressModel hash block = SHA512.compress hash block := by
  unfold SHA512.compress
  change compressModel hash block = Id.run (do
    let words ← forIn [16:80] (initialSchedule block)
      (fun i words => pure (ForInStep.yield (scheduleStep words i)))
    let result ← forIn [:80] (State.toTuple (State.ofArray hash))
      (fun i s => pure (ForInStep.yield (tupleRound words s i)))
    pure (State.addHash hash (State.ofTuple result)))
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Id.run,
    List.forIn_pure_yield_eq_foldl]
  have h1 : (Std.Legacy.Range.mk 16 80 1 (by decide)).size = 64 := rfl
  have h2 : (Std.Legacy.Range.mk 0 80 1 (by decide)).size = 80 := rfl
  simp only [h1, h2, ← List.range_eq_range', pure_bind]
  change State.addHash hash (rounds (State.ofArray hash) (schedule block) 80) =
    State.addHash hash (State.ofTuple ((List.range 80).foldl (tupleRound (schedule block))
      (State.toTuple (State.ofArray hash))))
  exact congrArg (State.addHash hash)
    (rounds_eq_tupleFold (State.toTuple (State.ofArray hash)) (schedule block) 80)

theorem compress_size (hash : Array UInt64) (block : Array Bool) :
    (SHA512.compress hash block).size = 8 := by
  rw [← compressModel_eq_compress]
  rfl

end Sha2.Proofs.Common.SHA512
