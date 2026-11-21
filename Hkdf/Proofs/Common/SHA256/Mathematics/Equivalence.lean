import Hkdf.Proofs.Common.SHA256.Mathematics.Model

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256

open Hkdf.Proofs.NIST

private abbrev StateTuple := UInt32 × UInt32 × UInt32 × UInt32 × UInt32 × UInt32 × UInt32 × UInt32

private def State.toTuple (s : State) : StateTuple := (s.a, s.b, s.c, s.d, s.e, s.f, s.g, s.h)

private def State.ofTuple (s : StateTuple) : State :=
  ⟨s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, s.2.2.2.2.2.1,
    s.2.2.2.2.2.2.1, s.2.2.2.2.2.2.2⟩

private def tupleRound (words : Array UInt32) (s : StateTuple) (i : Nat) : StateTuple :=
  (round (State.ofTuple s) SHA256.roundConstants[i]! words[i]!).toTuple

private theorem rounds_eq_tupleFold (initial : StateTuple) (words : Array UInt32) (n : Nat) :
    rounds (State.ofTuple initial) words n =
      State.ofTuple ((List.range n).foldl (tupleRound words) initial) := by
  unfold rounds
  apply List.foldl_hom State.ofTuple
  intro s i
  rfl

theorem compressModel_eq_compress (hash : Array UInt32) (block : Array Bool) :
    compressModel hash block = SHA256.compress hash block := by
  unfold SHA256.compress
  change compressModel hash block = Id.run (do
    let words ← forIn [16:64] (initialSchedule block)
      (fun i words => pure (ForInStep.yield (scheduleStep words i)))
    let result ← forIn [:64] (State.toTuple (State.ofArray hash))
      (fun i s => pure (ForInStep.yield (tupleRound words s i)))
    pure (State.addHash hash (State.ofTuple result)))
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Id.run,
    List.forIn_pure_yield_eq_foldl]
  have h1 : (Std.Legacy.Range.mk 16 64 1 (by decide)).size = 48 := rfl
  have h2 : (Std.Legacy.Range.mk 0 64 1 (by decide)).size = 64 := rfl
  simp only [h1, h2, ← List.range_eq_range', pure_bind]
  change State.addHash hash (rounds (State.ofArray hash) (schedule block) 64) =
    State.addHash hash (State.ofTuple ((List.range 64).foldl (tupleRound (schedule block))
      (State.toTuple (State.ofArray hash))))
  exact congrArg (State.addHash hash)
    (rounds_eq_tupleFold (State.toTuple (State.ofArray hash)) (schedule block) 64)

theorem compress_size (hash : Array UInt32) (block : Array Bool) :
    (SHA256.compress hash block).size = 8 := by
  rw [← compressModel_eq_compress]
  rfl

end Hkdf.Proofs.Common.SHA256
