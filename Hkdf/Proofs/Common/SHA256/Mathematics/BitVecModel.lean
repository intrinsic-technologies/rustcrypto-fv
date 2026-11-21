import Hkdf.Proofs.Common.SHA256.Mathematics.Bitwise
import Hkdf.Proofs.Common.SHA256.Mathematics.Equivalence
import Hkdf.Proofs.Common.SHA256.Mathematics.Schedule

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256

open Hkdf.Proofs.NIST

structure BitVecState where
  a : BitVec 32
  b : BitVec 32
  c : BitVec 32
  d : BitVec 32
  e : BitVec 32
  f : BitVec 32
  g : BitVec 32
  h : BitVec 32
  deriving DecidableEq

def BitVecState.ofState (s : State) : BitVecState :=
  ⟨s.a.toBitVec, s.b.toBitVec, s.c.toBitVec, s.d.toBitVec,
    s.e.toBitVec, s.f.toBitVec, s.g.toBitVec, s.h.toBitVec⟩

def BitVecState.toState (s : BitVecState) : State :=
  ⟨UInt32.ofBitVec s.a, UInt32.ofBitVec s.b, UInt32.ofBitVec s.c, UInt32.ofBitVec s.d,
    UInt32.ofBitVec s.e, UInt32.ofBitVec s.f, UInt32.ofBitVec s.g, UInt32.ofBitVec s.h⟩

def bitVecSmallSigma0 (x : BitVec 32) : BitVec 32 :=
  x.rotateLeft 25 ^^^ x.rotateLeft 14 ^^^ (x >>> 3)

def bitVecSmallSigma1 (x : BitVec 32) : BitVec 32 :=
  x.rotateLeft 15 ^^^ x.rotateLeft 13 ^^^ (x >>> 10)

def bitVecBigSigma0 (x : BitVec 32) : BitVec 32 :=
  x.rotateLeft 30 ^^^ x.rotateLeft 19 ^^^ x.rotateLeft 10

def bitVecBigSigma1 (x : BitVec 32) : BitVec 32 :=
  x.rotateLeft 26 ^^^ x.rotateLeft 21 ^^^ x.rotateLeft 7

def bitVecChoice (x y z : BitVec 32) : BitVec 32 := (x &&& y) ^^^ (~~~x &&& z)

def bitVecMajority (x y z : BitVec 32) : BitVec 32 :=
  (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

def bitVecRound (s : BitVecState) (k w : BitVec 32) : BitVecState :=
  let first := s.h + bitVecBigSigma1 s.e + bitVecChoice s.e s.f s.g + k + w
  let second := bitVecBigSigma0 s.a + bitVecMajority s.a s.b s.c
  ⟨first + second, s.a, s.b, s.c, s.d + first, s.e, s.f, s.g⟩

def bitVecRounds (initial : BitVecState) (words : Array (BitVec 32)) (n : Nat) : BitVecState :=
  (List.range n).foldl (fun s i => bitVecRound s SHA256.roundConstants[i]!.toBitVec words[i]!) initial

def BitVecState.addHash (hash : Array UInt32) (s : BitVecState) : Array (BitVec 32) :=
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

theorem bitVecRound_ofState (s : State) (k w : UInt32) :
    bitVecRound (BitVecState.ofState s) k.toBitVec w.toBitVec =
      BitVecState.ofState (round s k w) := by
  simp only [bitVecRound, BitVecState.ofState, round, UInt32.toBitVec_add,
    bigSigma0_toBitVec_rotateLeft, bigSigma1_toBitVec_rotateLeft,
    choice_toBitVec, majority_toBitVec, bitVecBigSigma0, bitVecBigSigma1,
    bitVecChoice, bitVecMajority]

theorem map_toBitVec_getElem! (words : Array UInt32) (i : Nat) :
    (words.map UInt32.toBitVec)[i]! = words[i]!.toBitVec := by
  by_cases hi : i < words.size
  · simp only [getElem!_pos (words.map UInt32.toBitVec) i
        (by simpa only [Array.size_map] using hi), Array.getElem_map, getElem!_pos words i hi]
  · simp only [getElem!_neg (words.map UInt32.toBitVec) i
        (by simpa only [Array.size_map] using hi), getElem!_neg words i hi]
    rfl

theorem bitVecRounds_zero (initial : BitVecState) (words : Array (BitVec 32)) :
    bitVecRounds initial words 0 = initial := rfl

theorem bitVecRounds_succ (initial : BitVecState) (words : Array (BitVec 32)) (n : Nat) :
    bitVecRounds initial words (n+1) =
      bitVecRound (bitVecRounds initial words n) SHA256.roundConstants[n]!.toBitVec words[n]! := by
  simp only [bitVecRounds, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem bitVecRounds_ofState (initial : State) (words : Array UInt32) (n : Nat) :
    bitVecRounds (BitVecState.ofState initial) (words.map UInt32.toBitVec) n =
      BitVecState.ofState (rounds initial words n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [bitVecRounds_succ, rounds_succ, ih, map_toBitVec_getElem!, bitVecRound_ofState]

theorem BitVecState.addHash_ofState (hash : Array UInt32) (s : State) :
    addHash hash (ofState s) = (State.addHash hash s).map UInt32.toBitVec := by
  simp only [addHash, ofState, State.addHash, List.map_toArray, List.map_cons, List.map_nil, UInt32.toBitVec_add]

theorem bitVecRounds_addHash_eq_compress (hash : Array UInt32) (block : Array Bool) :
    BitVecState.addHash hash
      (bitVecRounds (BitVecState.ofState (State.ofArray hash))
        ((schedule block).map UInt32.toBitVec) 64) =
      (SHA256.compress hash block).map UInt32.toBitVec := by
  rw [bitVecRounds_ofState, BitVecState.addHash_ofState]
  exact congrArg (fun words => words.map UInt32.toBitVec) (compressModel_eq_compress hash block)

theorem schedule_toBitVec_recurrence (block : Array Bool) (i : Nat)
    (lo : 16 ≤ i) (hi : i < 64) :
    ((schedule block).map UInt32.toBitVec)[i]! =
      ((schedule block).map UInt32.toBitVec)[i-16]! +
      bitVecSmallSigma0 ((schedule block).map UInt32.toBitVec)[i-15]! +
      ((schedule block).map UInt32.toBitVec)[i-7]! +
      bitVecSmallSigma1 ((schedule block).map UInt32.toBitVec)[i-2]! := by
  simp only [map_toBitVec_getElem!]
  rw [schedule_getElem!_recurrence block i lo hi]
  simp only [UInt32.toBitVec_add, smallSigma0_toBitVec_rotateLeft,
    smallSigma1_toBitVec_rotateLeft, bitVecSmallSigma0, bitVecSmallSigma1]

theorem bitVecChoice_eq_add_and (x y z : BitVec 32) :
    bitVecChoice x y z = (x &&& y) + (~~~x &&& z) := by
  exact congrArg UInt32.toBitVec (choice_eq_add_and
    (UInt32.ofBitVec x) (UInt32.ofBitVec y) (UInt32.ofBitVec z))

theorem bitVecChoice_eq_and_xor (x y z : BitVec 32) :
    bitVecChoice x y z = ((y ^^^ z) &&& x) ^^^ z := by
  exact congrArg UInt32.toBitVec (choice_eq_and_xor
    (UInt32.ofBitVec x) (UInt32.ofBitVec y) (UInt32.ofBitVec z))

theorem bitVecMajority_eq_and_xor (x y z : BitVec 32) :
    bitVecMajority x y z = ((y ^^^ z) &&& x) ^^^ (y &&& z) := by
  exact congrArg UInt32.toBitVec (majority_eq_and_xor
    (UInt32.ofBitVec x) (UInt32.ofBitVec y) (UInt32.ofBitVec z))

end Hkdf.Proofs.Common.SHA256
