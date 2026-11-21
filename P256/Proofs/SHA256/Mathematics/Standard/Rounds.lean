import P256.Proofs.SHA256.Mathematics.Model

set_option autoImplicit false

namespace P256.Proofs.SHA256

private abbrev StandardTuple :=
  BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32

private def toStandardTuple (s : State) : StandardTuple :=
  (s.a.toBitVec, s.b.toBitVec, s.c.toBitVec, s.d.toBitVec,
    s.e.toBitVec, s.f.toBitVec, s.g.toBitVec, s.h.toBitVec)

private def ofStandardTuple (s : StandardTuple) : State :=
  ⟨UInt32.ofBitVec s.1, UInt32.ofBitVec s.2.1, UInt32.ofBitVec s.2.2.1,
    UInt32.ofBitVec s.2.2.2.1, UInt32.ofBitVec s.2.2.2.2.1,
    UInt32.ofBitVec s.2.2.2.2.2.1, UInt32.ofBitVec s.2.2.2.2.2.2.1,
    UInt32.ofBitVec s.2.2.2.2.2.2.2⟩

private def standardTupleRound (s : StandardTuple) (k w : BitVec 32) : StandardTuple :=
  let first := s.2.2.2.2.2.2.2 + Standards.NIST.SHA2.SHA256.«Σ₁» s.2.2.2.2.1 +
    Standards.NIST.SHA2.SHA256.Ch s.2.2.2.2.1 s.2.2.2.2.2.1 s.2.2.2.2.2.2.1 + k + w
  let second := Standards.NIST.SHA2.SHA256.«Σ₀» s.1 +
    Standards.NIST.SHA2.SHA256.Maj s.1 s.2.1 s.2.2.1
  (first + second, s.1, s.2.1, s.2.2.1, s.2.2.2.1 + first,
    s.2.2.2.2.1, s.2.2.2.2.2.1, s.2.2.2.2.2.2.1)

private theorem round_toStandardTuple (s : State) (k w : UInt32) :
    toStandardTuple (round s k w) = standardTupleRound (toStandardTuple s) k.toBitVec w.toBitVec := by
  rfl

private theorem roundConstants_toStandard (i : Nat) (hi : i < 64) :
    Reference.roundConstants[i]!.toBitVec = Standards.NIST.SHA2.SHA256.K[i] := by
  simp only [Reference.roundConstants, getElem!_pos (Standards.NIST.SHA2.SHA256.K.toArray.map UInt32.ofBitVec) i
      (by simpa only [Array.size_map, Vector.size_toArray] using hi), Array.getElem_map,
    UInt32.toBitVec_ofBitVec, Vector.getElem_toArray]

private def tupleRound (words : Array UInt32) (s : StandardTuple) (i : Nat) : StandardTuple :=
  toStandardTuple (round (ofStandardTuple s) Reference.roundConstants[i]! words[i]!)

private theorem toStandardTuple_rounds (initial : State) (words : Array UInt32) (n : Nat) :
    (List.range n).foldl (tupleRound words) (toStandardTuple initial) =
      toStandardTuple (rounds initial words n) := by
  apply List.foldl_hom toStandardTuple
  intro s i
  rfl

private def tupleAddHash (H : Vector (BitVec 32) 8) (s : StandardTuple) : Vector (BitVec 32) 8 :=
  #v[s.1 + H[0], s.2.1 + H[1], s.2.2.1 + H[2], s.2.2.2.1 + H[3],
    s.2.2.2.2.1 + H[4], s.2.2.2.2.2.1 + H[5],
    s.2.2.2.2.2.2.1 + H[6], s.2.2.2.2.2.2.2 + H[7]]

private theorem tupleRound_toStandard (words : Array UInt32) (M : Vector (BitVec 32) 16)
    (hw : ∀ i : Fin 64, words[i.val]!.toBitVec = (Standards.NIST.SHA2.SHA256.W M)[i.val])
    (i : Nat) (hi : i < 64) (s : StandardTuple) :
    standardTupleRound s Standards.NIST.SHA2.SHA256.K[i]
      (Standards.NIST.SHA2.SHA256.W M)[i] = tupleRound words s i := by
  simp only [tupleRound, round_toStandardTuple, roundConstants_toStandard i hi, hw ⟨i, hi⟩]
  rfl

private theorem hashBlock_eq_tupleFold (hash : Array UInt32) (words : Array UInt32)
    (M : Vector (BitVec 32) 16)
    (hw : ∀ i : Fin 64, words[i.val]!.toBitVec = (Standards.NIST.SHA2.SHA256.W M)[i.val]) :
    Standards.NIST.SHA2.SHA256.hashBlock
      (Vector.ofFn fun i : Fin 8 => hash[i.val]!.toBitVec) M =
    tupleAddHash (Vector.ofFn fun i : Fin 8 => hash[i.val]!.toBitVec)
      ((List.range 64).foldl (tupleRound words) (toStandardTuple (State.ofArray hash))) := by
  unfold Standards.NIST.SHA2.SHA256.hashBlock
  change Id.run (do
    let s ← forIn' (m := Id) [:64] (toStandardTuple (State.ofArray hash))
      (fun i hi s => pure (ForInStep.yield (standardTupleRound s
        Standards.NIST.SHA2.SHA256.K[i] (Standards.NIST.SHA2.SHA256.W M)[i])))
    pure (tupleAddHash (Vector.ofFn fun i : Fin 8 => hash[i.val]!.toBitVec) s)) = _
  rw [forIn'_eq_forIn _ _ _
    (fun i s => pure (ForInStep.yield (tupleRound words s i))) ?_]
  · simp only [Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl]
    rfl
  · intro i hi s
    exact congrArg (fun s => pure (ForInStep.yield s)) (tupleRound_toStandard words M hw i hi.2.1 s)

theorem rounds_toStandard (hash : Array UInt32) (words : Array UInt32)
    (M : Vector (BitVec 32) 16)
    (hw : ∀ i : Fin 64, words[i.val]!.toBitVec = (Standards.NIST.SHA2.SHA256.W M)[i.val]) :
    State.addHash hash (rounds (State.ofArray hash) words 64) =
      (Standards.NIST.SHA2.SHA256.hashBlock
        (Vector.ofFn fun i : Fin 8 => hash[i.val]!.toBitVec) M).toArray.map UInt32.ofBitVec := by
  rw [hashBlock_eq_tupleFold hash words M hw, toStandardTuple_rounds]
  simp [State.addHash, tupleAddHash, toStandardTuple, UInt32.ofBitVec_add, UInt32.add_comm]

end P256.Proofs.SHA256
