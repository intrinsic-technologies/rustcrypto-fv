import Sha2.Proofs.FIPS180.Schedule512

namespace Sha2.Proofs.FIPS180
namespace SHA512Bridge
open Standards.NIST.SHA2
open Sha2.Proofs.Common.SHA512

theorem bitVecBigSigma0_eq (x : BitVec 64) : bitVecBigSigma0 x = SHA512.«Σ₀» x := by
  exact (bigSigma0_toBitVec_rotateLeft (UInt64.ofBitVec x)).symm.trans
    (bigSigma0_toBitVec (UInt64.ofBitVec x))

theorem bitVecBigSigma1_eq (x : BitVec 64) : bitVecBigSigma1 x = SHA512.«Σ₁» x := by
  exact (bigSigma1_toBitVec_rotateLeft (UInt64.ofBitVec x)).symm.trans
    (bigSigma1_toBitVec (UInt64.ofBitVec x))

theorem K_eq_roundConstants : SHA512.K.toArray = NIST.SHA512.roundConstants.map UInt64.toBitVec := by
  decide +kernel

theorem K_getElem (i : Nat) (hi : i < 80) :
    SHA512.K[i] = NIST.SHA512.roundConstants[i]!.toBitVec := by
  have h := congrArg (fun a : Array (BitVec 64) => a[i]!) K_eq_roundConstants
  simpa only [map_toBitVec_getElem!, getElem!_pos SHA512.K.toArray i (by simpa using hi), Vector.getElem_toArray] using h

abbrev StateTuple := BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 ×
  BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64

def stateToTuple (s : BitVecState) : StateTuple := (s.a, s.b, s.c, s.d, s.e, s.f, s.g, s.h)

def stateOfTuple (s : StateTuple) : BitVecState :=
  ⟨s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, s.2.2.2.2.2.1,
    s.2.2.2.2.2.2.1, s.2.2.2.2.2.2.2⟩

def tupleRound (words : Array (BitVec 64)) (s : StateTuple) (i : Nat) : StateTuple :=
  stateToTuple (bitVecRound (stateOfTuple s) NIST.SHA512.roundConstants[i]!.toBitVec words[i]!)

theorem bitVecRounds_eq_tupleFold (initial : StateTuple) (words : Array (BitVec 64)) (n : Nat) :
    bitVecRounds (stateOfTuple initial) words n =
      stateOfTuple ((List.range n).foldl (tupleRound words) initial) := by
  unfold bitVecRounds
  apply List.foldl_hom stateOfTuple
  intro s i
  rfl

def hashState (H : Vector (BitVec 64) 8) : BitVecState :=
  ⟨H[0], H[1], H[2], H[3], H[4], H[5], H[6], H[7]⟩

def addHash (H : Vector (BitVec 64) 8) (s : BitVecState) : Vector (BitVec 64) 8 :=
  #v[s.a + H[0], s.b + H[1], s.c + H[2], s.d + H[3],
    s.e + H[4], s.f + H[5], s.g + H[6], s.h + H[7]]

theorem hashBlock_eq_rounds (H : Vector (BitVec 64) 8) (M : Vector (BitVec 64) 16) :
    SHA512.hashBlock H M = addHash H (bitVecRounds (hashState H) (SHA512.W M).toArray 80) := by
  unfold SHA512.hashBlock
  let words := SHA512.W M
  have hbody : (fun t (ht : t ∈ ([:80] : Std.Legacy.Range)) (s : StateTuple) =>
      (do
        have ht80 : t < 80 := ht.2.1
        let first := s.2.2.2.2.2.2.2 + SHA512.«Σ₁» s.2.2.2.2.1 +
          SHA512.Ch s.2.2.2.2.1 s.2.2.2.2.2.1 s.2.2.2.2.2.2.1 + SHA512.K[t] + words[t]
        let second := SHA512.«Σ₀» s.1 + SHA512.Maj s.1 s.2.1 s.2.2.1
        pure (ForInStep.yield (first + second, s.1, s.2.1, s.2.2.1,
          s.2.2.2.1 + first, s.2.2.2.2.1, s.2.2.2.2.2.1, s.2.2.2.2.2.2.1)) :
        Id (ForInStep StateTuple))) =
      (fun t _ s => pure (ForInStep.yield (tupleRound words.toArray s t))) := by
    funext t ht s
    have ht80 : t < 80 := ht.2.1
    simp only [tupleRound, stateToTuple, stateOfTuple, bitVecRound, bitVecBigSigma0_eq,
      bitVecBigSigma1_eq, bitVecChoice, bitVecMajority, SHA512.Ch, SHA512.Maj,
      K_getElem t ht80, getElem!_pos words.toArray t (by simpa using ht80), Vector.getElem_toArray]
  change Id.run (do
    let result ← forIn' ([:80] : Std.Legacy.Range) (stateToTuple (hashState H)) _
    pure (addHash H (stateOfTuple result))) = _
  rw [hbody]
  change Id.run (do
    let result ← forIn ([:80] : Std.Legacy.Range) (stateToTuple (hashState H))
      (fun t s => pure (ForInStep.yield (tupleRound words.toArray s t)))
    pure (addHash H (stateOfTuple result))) = _
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl, Id.run,
    pure_bind]
  exact congrArg (addHash H)
    (bitVecRounds_eq_tupleFold (stateToTuple (hashState H)) words.toArray 80).symm

theorem hashState_eq (H : Vector (BitVec 64) 8) :
    hashState H = BitVecState.ofState (State.ofArray (H.toArray.map UInt64.ofBitVec)) := by
  simp [hashState, BitVecState.ofState, State.ofArray]

theorem addHash_toArray (H : Vector (BitVec 64) 8) (s : BitVecState) :
    (addHash H s).toArray = BitVecState.addHash (H.toArray.map UInt64.ofBitVec) s := by
  simp [addHash, BitVecState.addHash, BitVec.add_comm]

theorem compress_eq_hashBlock (H : Vector (BitVec 64) 8) (block : Array Bool)
    (M : Vector (BitVec 64) 16)
    (hM : ∀ i (hi : i < 16), (initialSchedule block)[i]!.toBitVec = M[i]) :
    (NIST.SHA512.compress (H.toArray.map UInt64.ofBitVec) block).map UInt64.toBitVec =
      (SHA512.hashBlock H M).toArray := by
  rw [hashBlock_eq_rounds, addHash_toArray, hashState_eq, W_eq_schedule block M hM,
    bitVecRounds_addHash_eq_compress]

theorem compress_eq_hashBlock_words (H : Vector (BitVec 64) 8) (block : Array Bool)
    (M : Vector (BitVec 64) 16)
    (hM : ∀ i (hi : i < 16), (initialSchedule block)[i]!.toBitVec = M[i]) :
    NIST.SHA512.compress (H.toArray.map UInt64.ofBitVec) block =
      (SHA512.hashBlock H M).toArray.map UInt64.ofBitVec := by
  have h := congrArg (fun a : Array (BitVec 64) => a.map UInt64.ofBitVec)
    (compress_eq_hashBlock H block M hM)
  simpa only [Array.map_map, Function.comp_def, UInt64.ofBitVec_toBitVec, Array.map_id'] using h

end SHA512Bridge
end Sha2.Proofs.FIPS180
