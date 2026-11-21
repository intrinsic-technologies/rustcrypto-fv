import Sha2.Proofs.Common.SHA512.Mathematics.Bitwise
import Sha2.Proofs.Common.SHA512.Mathematics.Equivalence
import Sha2.Proofs.Common.SHA512.Mathematics.Schedule

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512

open Sha2.Proofs.NIST

structure BitVecState where
  a : BitVec 64
  b : BitVec 64
  c : BitVec 64
  d : BitVec 64
  e : BitVec 64
  f : BitVec 64
  g : BitVec 64
  h : BitVec 64
  deriving DecidableEq

def BitVecState.ofState (s : State) : BitVecState :=
  ⟨s.a.toBitVec, s.b.toBitVec, s.c.toBitVec, s.d.toBitVec,
    s.e.toBitVec, s.f.toBitVec, s.g.toBitVec, s.h.toBitVec⟩

def BitVecState.toState (s : BitVecState) : State :=
  ⟨UInt64.ofBitVec s.a, UInt64.ofBitVec s.b, UInt64.ofBitVec s.c, UInt64.ofBitVec s.d,
    UInt64.ofBitVec s.e, UInt64.ofBitVec s.f, UInt64.ofBitVec s.g, UInt64.ofBitVec s.h⟩

def bitVecSmallSigma0 (x : BitVec 64) : BitVec 64 :=
  x.rotateLeft 63 ^^^ x.rotateLeft 56 ^^^ (x >>> 7)

def bitVecSmallSigma1 (x : BitVec 64) : BitVec 64 :=
  x.rotateLeft 45 ^^^ x.rotateLeft 3 ^^^ (x >>> 6)

def bitVecBigSigma0 (x : BitVec 64) : BitVec 64 :=
  x.rotateLeft 36 ^^^ x.rotateLeft 30 ^^^ x.rotateLeft 25

def bitVecBigSigma1 (x : BitVec 64) : BitVec 64 :=
  x.rotateLeft 50 ^^^ x.rotateLeft 46 ^^^ x.rotateLeft 23

def bitVecChoice (x y z : BitVec 64) : BitVec 64 := (x &&& y) ^^^ (~~~x &&& z)

def bitVecMajority (x y z : BitVec 64) : BitVec 64 :=
  (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

def bitVecRound (s : BitVecState) (k w : BitVec 64) : BitVecState :=
  let first := s.h + bitVecBigSigma1 s.e + bitVecChoice s.e s.f s.g + k + w
  let second := bitVecBigSigma0 s.a + bitVecMajority s.a s.b s.c
  ⟨first + second, s.a, s.b, s.c, s.d + first, s.e, s.f, s.g⟩

def bitVecRounds (initial : BitVecState) (words : Array (BitVec 64)) (n : Nat) : BitVecState :=
  (List.range n).foldl (fun s i => bitVecRound s SHA512.roundConstants[i]!.toBitVec words[i]!) initial

def BitVecState.addHash (hash : Array UInt64) (s : BitVecState) : Array (BitVec 64) :=
  #[hash[0]!.toBitVec + s.a, hash[1]!.toBitVec + s.b,
    hash[2]!.toBitVec + s.c, hash[3]!.toBitVec + s.d,
    hash[4]!.toBitVec + s.e, hash[5]!.toBitVec + s.f,
    hash[6]!.toBitVec + s.g, hash[7]!.toBitVec + s.h]

theorem BitVecState.ofState_toState (s : BitVecState) : ofState s.toState = s := by
  cases s
  rfl

theorem BitVecState.toState_ofState (s : State) : toState (ofState s) = s := by
  cases s
  rfl

theorem bitVecRound_ofState (s : State) (k w : UInt64) :
    bitVecRound (BitVecState.ofState s) k.toBitVec w.toBitVec =
      BitVecState.ofState (round s k w) := by
  simp only [bitVecRound, BitVecState.ofState, round, UInt64.toBitVec_add,
    bigSigma0_toBitVec_rotateLeft, bigSigma1_toBitVec_rotateLeft,
    choice_toBitVec, majority_toBitVec, bitVecBigSigma0, bitVecBigSigma1,
    bitVecChoice, bitVecMajority]

theorem map_toBitVec_getElem! (words : Array UInt64) (i : Nat) :
    (words.map UInt64.toBitVec)[i]! = words[i]!.toBitVec := by
  by_cases hi : i < words.size
  · simp only [getElem!_pos (words.map UInt64.toBitVec) i
        (by simpa only [Array.size_map] using hi), Array.getElem_map, getElem!_pos words i hi]
  · simp only [getElem!_neg (words.map UInt64.toBitVec) i
        (by simpa only [Array.size_map] using hi), getElem!_neg words i hi]
    rfl

theorem bitVecRounds_zero (initial : BitVecState) (words : Array (BitVec 64)) :
    bitVecRounds initial words 0 = initial := rfl

theorem bitVecRounds_succ (initial : BitVecState) (words : Array (BitVec 64)) (n : Nat) :
    bitVecRounds initial words (n+1) =
      bitVecRound (bitVecRounds initial words n) SHA512.roundConstants[n]!.toBitVec words[n]! := by
  simp only [bitVecRounds, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem bitVecRounds_ofState (initial : State) (words : Array UInt64) (n : Nat) :
    bitVecRounds (BitVecState.ofState initial) (words.map UInt64.toBitVec) n =
      BitVecState.ofState (rounds initial words n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [bitVecRounds_succ, rounds_succ, ih, map_toBitVec_getElem!, bitVecRound_ofState]

theorem BitVecState.addHash_ofState (hash : Array UInt64) (s : State) :
    addHash hash (ofState s) = (State.addHash hash s).map UInt64.toBitVec := by
  simp only [addHash, ofState, State.addHash, List.map_toArray, List.map_cons, List.map_nil, UInt64.toBitVec_add]

theorem bitVecRounds_addHash_eq_compress (hash : Array UInt64) (block : Array Bool) :
    BitVecState.addHash hash
      (bitVecRounds (BitVecState.ofState (State.ofArray hash))
        ((schedule block).map UInt64.toBitVec) 80) =
      (SHA512.compress hash block).map UInt64.toBitVec := by
  rw [bitVecRounds_ofState, BitVecState.addHash_ofState]
  exact congrArg (fun words => words.map UInt64.toBitVec) (compressModel_eq_compress hash block)

theorem schedule_toBitVec_recurrence (block : Array Bool) (i : Nat)
    (lo : 16 ≤ i) (hi : i < 80) :
    ((schedule block).map UInt64.toBitVec)[i]! =
      ((schedule block).map UInt64.toBitVec)[i-16]! +
      bitVecSmallSigma0 ((schedule block).map UInt64.toBitVec)[i-15]! +
      ((schedule block).map UInt64.toBitVec)[i-7]! +
      bitVecSmallSigma1 ((schedule block).map UInt64.toBitVec)[i-2]! := by
  simp only [map_toBitVec_getElem!]
  rw [schedule_getElem!_recurrence block i lo hi]
  simp only [UInt64.toBitVec_add, smallSigma0_toBitVec_rotateLeft,
    smallSigma1_toBitVec_rotateLeft, bitVecSmallSigma0, bitVecSmallSigma1]

theorem bitVecChoice_eq_add_and (x y z : BitVec 64) :
    bitVecChoice x y z = (x &&& y) + (~~~x &&& z) := by
  exact congrArg UInt64.toBitVec (choice_eq_add_and
    (UInt64.ofBitVec x) (UInt64.ofBitVec y) (UInt64.ofBitVec z))

theorem bitVecChoice_eq_and_xor (x y z : BitVec 64) :
    bitVecChoice x y z = ((y ^^^ z) &&& x) ^^^ z := by
  exact congrArg UInt64.toBitVec (choice_eq_and_xor
    (UInt64.ofBitVec x) (UInt64.ofBitVec y) (UInt64.ofBitVec z))

theorem bitVecMajority_eq_and_xor (x y z : BitVec 64) :
    bitVecMajority x y z = ((y ^^^ z) &&& x) ^^^ (y &&& z) := by
  exact congrArg UInt64.toBitVec (majority_eq_and_xor
    (UInt64.ofBitVec x) (UInt64.ofBitVec y) (UInt64.ofBitVec z))

end Sha2.Proofs.Common.SHA512
