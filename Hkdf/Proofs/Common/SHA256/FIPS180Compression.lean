import Hkdf.Proofs.Common.SHA256.FIPS180Schedule

namespace Hkdf.Proofs.FIPS180
open Standards.NIST.SHA2
open Hkdf.Proofs.Common.SHA256

theorem bitVecBigSigma0_eq (x : BitVec 32) : bitVecBigSigma0 x = SHA256.«Σ₀» x := by
  exact (bigSigma0_toBitVec_rotateLeft (UInt32.ofBitVec x)).symm.trans
    (bigSigma0_toBitVec (UInt32.ofBitVec x))

theorem bitVecBigSigma1_eq (x : BitVec 32) : bitVecBigSigma1 x = SHA256.«Σ₁» x := by
  exact (bigSigma1_toBitVec_rotateLeft (UInt32.ofBitVec x)).symm.trans
    (bigSigma1_toBitVec (UInt32.ofBitVec x))

theorem K_eq_roundConstants : SHA256.K.toArray = NIST.SHA256.roundConstants.map UInt32.toBitVec := by
  decide +kernel

theorem K_getElem (i : Nat) (hi : i < 64) :
    SHA256.K[i] = NIST.SHA256.roundConstants[i]!.toBitVec := by
  have h := congrArg (fun a : Array (BitVec 32) => a[i]!) K_eq_roundConstants
  simpa only [map_toBitVec_getElem!, getElem!_pos SHA256.K.toArray i (by simpa using hi), Vector.getElem_toArray] using h

abbrev StateTuple := BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 ×
  BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32

def stateToTuple (s : BitVecState) : StateTuple := (s.a, s.b, s.c, s.d, s.e, s.f, s.g, s.h)

def stateOfTuple (s : StateTuple) : BitVecState :=
  ⟨s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, s.2.2.2.2.2.1,
    s.2.2.2.2.2.2.1, s.2.2.2.2.2.2.2⟩

def tupleRound (words : Array (BitVec 32)) (s : StateTuple) (i : Nat) : StateTuple :=
  stateToTuple (bitVecRound (stateOfTuple s) NIST.SHA256.roundConstants[i]!.toBitVec words[i]!)

theorem bitVecRounds_eq_tupleFold (initial : StateTuple) (words : Array (BitVec 32)) (n : Nat) :
    bitVecRounds (stateOfTuple initial) words n =
      stateOfTuple ((List.range n).foldl (tupleRound words) initial) := by
  unfold bitVecRounds
  apply List.foldl_hom stateOfTuple
  intro s i
  rfl

def hashState (H : Vector (BitVec 32) 8) : BitVecState :=
  ⟨H[0], H[1], H[2], H[3], H[4], H[5], H[6], H[7]⟩

def addHash (H : Vector (BitVec 32) 8) (s : BitVecState) : Vector (BitVec 32) 8 :=
  #v[s.a + H[0], s.b + H[1], s.c + H[2], s.d + H[3],
    s.e + H[4], s.f + H[5], s.g + H[6], s.h + H[7]]

theorem hashBlock_eq_rounds (H : Vector (BitVec 32) 8) (M : Vector (BitVec 32) 16) :
    SHA256.hashBlock H M = addHash H (bitVecRounds (hashState H) (SHA256.W M).toArray 64) := by
  unfold SHA256.hashBlock
  let words := SHA256.W M
  have hbody : (fun t (ht : t ∈ ([:64] : Std.Legacy.Range)) (s : StateTuple) =>
      (do
        have ht64 : t < 64 := ht.2.1
        let first := s.2.2.2.2.2.2.2 + SHA256.«Σ₁» s.2.2.2.2.1 +
          SHA256.Ch s.2.2.2.2.1 s.2.2.2.2.2.1 s.2.2.2.2.2.2.1 + SHA256.K[t] + words[t]
        let second := SHA256.«Σ₀» s.1 + SHA256.Maj s.1 s.2.1 s.2.2.1
        pure (ForInStep.yield (first + second, s.1, s.2.1, s.2.2.1,
          s.2.2.2.1 + first, s.2.2.2.2.1, s.2.2.2.2.2.1, s.2.2.2.2.2.2.1)) :
        Id (ForInStep StateTuple))) =
      (fun t _ s => pure (ForInStep.yield (tupleRound words.toArray s t))) := by
    funext t ht s
    have ht64 : t < 64 := ht.2.1
    simp only [tupleRound, stateToTuple, stateOfTuple, bitVecRound, bitVecBigSigma0_eq,
      bitVecBigSigma1_eq, bitVecChoice, bitVecMajority, SHA256.Ch, SHA256.Maj,
      K_getElem t ht64, getElem!_pos words.toArray t (by simpa using ht64), Vector.getElem_toArray]
  change Id.run (do
    let result ← forIn' ([:64] : Std.Legacy.Range) (stateToTuple (hashState H)) _
    pure (addHash H (stateOfTuple result))) = _
  rw [hbody]
  change Id.run (do
    let result ← forIn ([:64] : Std.Legacy.Range) (stateToTuple (hashState H))
      (fun t s => pure (ForInStep.yield (tupleRound words.toArray s t)))
    pure (addHash H (stateOfTuple result))) = _
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl, Id.run,
    pure_bind]
  exact congrArg (addHash H)
    (bitVecRounds_eq_tupleFold (stateToTuple (hashState H)) words.toArray 64).symm

theorem hashState_eq (H : Vector (BitVec 32) 8) :
    hashState H = BitVecState.ofState (State.ofArray (H.toArray.map UInt32.ofBitVec)) := by
  simp [hashState, BitVecState.ofState, State.ofArray]

theorem addHash_toArray (H : Vector (BitVec 32) 8) (s : BitVecState) :
    (addHash H s).toArray = BitVecState.addHash (H.toArray.map UInt32.ofBitVec) s := by
  simp [addHash, BitVecState.addHash, BitVec.add_comm]

theorem compress_eq_hashBlock (H : Vector (BitVec 32) 8) (block : Array Bool)
    (M : Vector (BitVec 32) 16)
    (hM : ∀ i (hi : i < 16), (initialSchedule block)[i]!.toBitVec = M[i]) :
    (NIST.SHA256.compress (H.toArray.map UInt32.ofBitVec) block).map UInt32.toBitVec =
      (SHA256.hashBlock H M).toArray := by
  rw [hashBlock_eq_rounds, addHash_toArray, hashState_eq, W_eq_schedule block M hM,
    bitVecRounds_addHash_eq_compress]

theorem compress_eq_hashBlock_words (H : Vector (BitVec 32) 8) (block : Array Bool)
    (M : Vector (BitVec 32) 16)
    (hM : ∀ i (hi : i < 16), (initialSchedule block)[i]!.toBitVec = M[i]) :
    NIST.SHA256.compress (H.toArray.map UInt32.ofBitVec) block =
      (SHA256.hashBlock H M).toArray.map UInt32.ofBitVec := by
  have h := congrArg (fun a : Array (BitVec 32) => a.map UInt32.ofBitVec)
    (compress_eq_hashBlock H block M hM)
  simpa only [Array.map_map, Function.comp_def, UInt32.ofBitVec_toBitVec, Array.map_id'] using h

end Hkdf.Proofs.FIPS180
