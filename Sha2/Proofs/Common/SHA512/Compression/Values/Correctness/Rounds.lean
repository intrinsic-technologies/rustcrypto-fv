import Sha2.Proofs.Common.SHA512.Compression.Values.Correctness.Algebra

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Values.Correctness

open Sha2.Proofs.Common.SHA512
open Sha2.Proofs.NIST

theorem a01 (h : BitVecState) (block : Array Bool) :
    a h block 1 = (h.h + (h.e.rotateLeft 50 ^^^ h.e.rotateLeft 46 ^^^ h.e.rotateLeft 23) + ((h.e &&& h.f) + (~~~h.e &&& h.g)) + (SHA512.roundConstants[0]!).toBitVec + (word block 0)) + ((h.a.rotateLeft 36 ^^^ h.a.rotateLeft 30 ^^^ h.a.rotateLeft 25) + (((h.b ^^^ h.c) &&& h.a) ^^^ (h.b &&& h.c))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 0).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (h.h + bitVecBigSigma1 h.e + bitVecChoice h.e h.f h.g + (SHA512.roundConstants[0]!).toBitVec + (word block 0)) + (bitVecBigSigma0 h.a + bitVecMajority h.a h.b h.c) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e01 (h : BitVecState) (block : Array Bool) :
    e h block 1 = h.d + (h.h + (h.e.rotateLeft 50 ^^^ h.e.rotateLeft 46 ^^^ h.e.rotateLeft 23) + ((h.e &&& h.f) + (~~~h.e &&& h.g)) + (SHA512.roundConstants[0]!).toBitVec + (word block 0)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 0).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change h.d + (h.h + bitVecBigSigma1 h.e + bitVecChoice h.e h.f h.g + (SHA512.roundConstants[0]!).toBitVec + (word block 0)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a02 (h : BitVecState) (block : Array Bool) :
    a h block 2 = (h.g + ((e h block 1).rotateLeft 50 ^^^ (e h block 1).rotateLeft 46 ^^^ (e h block 1).rotateLeft 23) + (((e h block 1) &&& h.e) + (~~~(e h block 1) &&& h.f)) + (SHA512.roundConstants[1]!).toBitVec + (word block 1)) + (((a h block 1).rotateLeft 36 ^^^ (a h block 1).rotateLeft 30 ^^^ (a h block 1).rotateLeft 25) + (((h.a ^^^ h.b) &&& (a h block 1)) ^^^ (h.a &&& h.b))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 1).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (h.g + bitVecBigSigma1 (e h block 1) + bitVecChoice (e h block 1) h.e h.f + (SHA512.roundConstants[1]!).toBitVec + (word block 1)) + (bitVecBigSigma0 (a h block 1) + bitVecMajority (a h block 1) h.a h.b) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e02 (h : BitVecState) (block : Array Bool) :
    e h block 2 = h.c + (h.g + ((e h block 1).rotateLeft 50 ^^^ (e h block 1).rotateLeft 46 ^^^ (e h block 1).rotateLeft 23) + (((e h block 1) &&& h.e) + (~~~(e h block 1) &&& h.f)) + (SHA512.roundConstants[1]!).toBitVec + (word block 1)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 1).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change h.c + (h.g + bitVecBigSigma1 (e h block 1) + bitVecChoice (e h block 1) h.e h.f + (SHA512.roundConstants[1]!).toBitVec + (word block 1)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a03 (h : BitVecState) (block : Array Bool) :
    a h block 3 = (h.f + ((e h block 2).rotateLeft 50 ^^^ (e h block 2).rotateLeft 46 ^^^ (e h block 2).rotateLeft 23) + (((e h block 2) &&& (e h block 1)) + (~~~(e h block 2) &&& h.e)) + (SHA512.roundConstants[2]!).toBitVec + (word block 2)) + (((a h block 2).rotateLeft 36 ^^^ (a h block 2).rotateLeft 30 ^^^ (a h block 2).rotateLeft 25) + ((((a h block 1) ^^^ h.a) &&& (a h block 2)) ^^^ ((a h block 1) &&& h.a))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 2).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (h.f + bitVecBigSigma1 (e h block 2) + bitVecChoice (e h block 2) (e h block 1) h.e + (SHA512.roundConstants[2]!).toBitVec + (word block 2)) + (bitVecBigSigma0 (a h block 2) + bitVecMajority (a h block 2) (a h block 1) h.a) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e03 (h : BitVecState) (block : Array Bool) :
    e h block 3 = h.b + (h.f + ((e h block 2).rotateLeft 50 ^^^ (e h block 2).rotateLeft 46 ^^^ (e h block 2).rotateLeft 23) + (((e h block 2) &&& (e h block 1)) + (~~~(e h block 2) &&& h.e)) + (SHA512.roundConstants[2]!).toBitVec + (word block 2)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 2).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change h.b + (h.f + bitVecBigSigma1 (e h block 2) + bitVecChoice (e h block 2) (e h block 1) h.e + (SHA512.roundConstants[2]!).toBitVec + (word block 2)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a04 (h : BitVecState) (block : Array Bool) :
    a h block 4 = (h.e + ((e h block 3).rotateLeft 50 ^^^ (e h block 3).rotateLeft 46 ^^^ (e h block 3).rotateLeft 23) + (((e h block 3) &&& (e h block 2)) + (~~~(e h block 3) &&& (e h block 1))) + (SHA512.roundConstants[3]!).toBitVec + (word block 3)) + (((a h block 3).rotateLeft 36 ^^^ (a h block 3).rotateLeft 30 ^^^ (a h block 3).rotateLeft 25) + ((((a h block 2) ^^^ (a h block 1)) &&& (a h block 3)) ^^^ ((a h block 2) &&& (a h block 1)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 3).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (h.e + bitVecBigSigma1 (e h block 3) + bitVecChoice (e h block 3) (e h block 2) (e h block 1) + (SHA512.roundConstants[3]!).toBitVec + (word block 3)) + (bitVecBigSigma0 (a h block 3) + bitVecMajority (a h block 3) (a h block 2) (a h block 1)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e04 (h : BitVecState) (block : Array Bool) :
    e h block 4 = h.a + (h.e + ((e h block 3).rotateLeft 50 ^^^ (e h block 3).rotateLeft 46 ^^^ (e h block 3).rotateLeft 23) + (((e h block 3) &&& (e h block 2)) + (~~~(e h block 3) &&& (e h block 1))) + (SHA512.roundConstants[3]!).toBitVec + (word block 3)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 3).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change h.a + (h.e + bitVecBigSigma1 (e h block 3) + bitVecChoice (e h block 3) (e h block 2) (e h block 1) + (SHA512.roundConstants[3]!).toBitVec + (word block 3)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a05 (h : BitVecState) (block : Array Bool) :
    a h block 5 = ((e h block 1) + ((e h block 4).rotateLeft 50 ^^^ (e h block 4).rotateLeft 46 ^^^ (e h block 4).rotateLeft 23) + (((e h block 4) &&& (e h block 3)) + (~~~(e h block 4) &&& (e h block 2))) + (SHA512.roundConstants[4]!).toBitVec + (word block 4)) + (((a h block 4).rotateLeft 36 ^^^ (a h block 4).rotateLeft 30 ^^^ (a h block 4).rotateLeft 25) + ((((a h block 3) ^^^ (a h block 2)) &&& (a h block 4)) ^^^ ((a h block 3) &&& (a h block 2)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 4).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 1) + bitVecBigSigma1 (e h block 4) + bitVecChoice (e h block 4) (e h block 3) (e h block 2) + (SHA512.roundConstants[4]!).toBitVec + (word block 4)) + (bitVecBigSigma0 (a h block 4) + bitVecMajority (a h block 4) (a h block 3) (a h block 2)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e05 (h : BitVecState) (block : Array Bool) :
    e h block 5 = (a h block 1) + ((e h block 1) + ((e h block 4).rotateLeft 50 ^^^ (e h block 4).rotateLeft 46 ^^^ (e h block 4).rotateLeft 23) + (((e h block 4) &&& (e h block 3)) + (~~~(e h block 4) &&& (e h block 2))) + (SHA512.roundConstants[4]!).toBitVec + (word block 4)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 4).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 1) + ((e h block 1) + bitVecBigSigma1 (e h block 4) + bitVecChoice (e h block 4) (e h block 3) (e h block 2) + (SHA512.roundConstants[4]!).toBitVec + (word block 4)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a06 (h : BitVecState) (block : Array Bool) :
    a h block 6 = ((e h block 2) + ((e h block 5).rotateLeft 50 ^^^ (e h block 5).rotateLeft 46 ^^^ (e h block 5).rotateLeft 23) + (((e h block 5) &&& (e h block 4)) + (~~~(e h block 5) &&& (e h block 3))) + (SHA512.roundConstants[5]!).toBitVec + (word block 5)) + (((a h block 5).rotateLeft 36 ^^^ (a h block 5).rotateLeft 30 ^^^ (a h block 5).rotateLeft 25) + ((((a h block 4) ^^^ (a h block 3)) &&& (a h block 5)) ^^^ ((a h block 4) &&& (a h block 3)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 5).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 2) + bitVecBigSigma1 (e h block 5) + bitVecChoice (e h block 5) (e h block 4) (e h block 3) + (SHA512.roundConstants[5]!).toBitVec + (word block 5)) + (bitVecBigSigma0 (a h block 5) + bitVecMajority (a h block 5) (a h block 4) (a h block 3)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e06 (h : BitVecState) (block : Array Bool) :
    e h block 6 = (a h block 2) + ((e h block 2) + ((e h block 5).rotateLeft 50 ^^^ (e h block 5).rotateLeft 46 ^^^ (e h block 5).rotateLeft 23) + (((e h block 5) &&& (e h block 4)) + (~~~(e h block 5) &&& (e h block 3))) + (SHA512.roundConstants[5]!).toBitVec + (word block 5)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 5).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 2) + ((e h block 2) + bitVecBigSigma1 (e h block 5) + bitVecChoice (e h block 5) (e h block 4) (e h block 3) + (SHA512.roundConstants[5]!).toBitVec + (word block 5)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a07 (h : BitVecState) (block : Array Bool) :
    a h block 7 = ((e h block 3) + ((e h block 6).rotateLeft 50 ^^^ (e h block 6).rotateLeft 46 ^^^ (e h block 6).rotateLeft 23) + (((e h block 6) &&& (e h block 5)) + (~~~(e h block 6) &&& (e h block 4))) + (SHA512.roundConstants[6]!).toBitVec + (word block 6)) + (((a h block 6).rotateLeft 36 ^^^ (a h block 6).rotateLeft 30 ^^^ (a h block 6).rotateLeft 25) + ((((a h block 5) ^^^ (a h block 4)) &&& (a h block 6)) ^^^ ((a h block 5) &&& (a h block 4)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 6).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 3) + bitVecBigSigma1 (e h block 6) + bitVecChoice (e h block 6) (e h block 5) (e h block 4) + (SHA512.roundConstants[6]!).toBitVec + (word block 6)) + (bitVecBigSigma0 (a h block 6) + bitVecMajority (a h block 6) (a h block 5) (a h block 4)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e07 (h : BitVecState) (block : Array Bool) :
    e h block 7 = (a h block 3) + ((e h block 3) + ((e h block 6).rotateLeft 50 ^^^ (e h block 6).rotateLeft 46 ^^^ (e h block 6).rotateLeft 23) + (((e h block 6) &&& (e h block 5)) + (~~~(e h block 6) &&& (e h block 4))) + (SHA512.roundConstants[6]!).toBitVec + (word block 6)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 6).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 3) + ((e h block 3) + bitVecBigSigma1 (e h block 6) + bitVecChoice (e h block 6) (e h block 5) (e h block 4) + (SHA512.roundConstants[6]!).toBitVec + (word block 6)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a08 (h : BitVecState) (block : Array Bool) :
    a h block 8 = ((e h block 4) + ((e h block 7).rotateLeft 50 ^^^ (e h block 7).rotateLeft 46 ^^^ (e h block 7).rotateLeft 23) + (((e h block 7) &&& (e h block 6)) + (~~~(e h block 7) &&& (e h block 5))) + (SHA512.roundConstants[7]!).toBitVec + (word block 7)) + (((a h block 7).rotateLeft 36 ^^^ (a h block 7).rotateLeft 30 ^^^ (a h block 7).rotateLeft 25) + ((((a h block 6) ^^^ (a h block 5)) &&& (a h block 7)) ^^^ ((a h block 6) &&& (a h block 5)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 7).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 4) + bitVecBigSigma1 (e h block 7) + bitVecChoice (e h block 7) (e h block 6) (e h block 5) + (SHA512.roundConstants[7]!).toBitVec + (word block 7)) + (bitVecBigSigma0 (a h block 7) + bitVecMajority (a h block 7) (a h block 6) (a h block 5)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e08 (h : BitVecState) (block : Array Bool) :
    e h block 8 = (a h block 4) + ((e h block 4) + ((e h block 7).rotateLeft 50 ^^^ (e h block 7).rotateLeft 46 ^^^ (e h block 7).rotateLeft 23) + (((e h block 7) &&& (e h block 6)) + (~~~(e h block 7) &&& (e h block 5))) + (SHA512.roundConstants[7]!).toBitVec + (word block 7)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 7).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 4) + ((e h block 4) + bitVecBigSigma1 (e h block 7) + bitVecChoice (e h block 7) (e h block 6) (e h block 5) + (SHA512.roundConstants[7]!).toBitVec + (word block 7)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a09 (h : BitVecState) (block : Array Bool) :
    a h block 9 = ((e h block 5) + ((e h block 8).rotateLeft 50 ^^^ (e h block 8).rotateLeft 46 ^^^ (e h block 8).rotateLeft 23) + (((e h block 8) &&& (e h block 7)) + (~~~(e h block 8) &&& (e h block 6))) + (SHA512.roundConstants[8]!).toBitVec + (word block 8)) + (((a h block 8).rotateLeft 36 ^^^ (a h block 8).rotateLeft 30 ^^^ (a h block 8).rotateLeft 25) + ((((a h block 7) ^^^ (a h block 6)) &&& (a h block 8)) ^^^ ((a h block 7) &&& (a h block 6)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 8).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 5) + bitVecBigSigma1 (e h block 8) + bitVecChoice (e h block 8) (e h block 7) (e h block 6) + (SHA512.roundConstants[8]!).toBitVec + (word block 8)) + (bitVecBigSigma0 (a h block 8) + bitVecMajority (a h block 8) (a h block 7) (a h block 6)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e09 (h : BitVecState) (block : Array Bool) :
    e h block 9 = (a h block 5) + ((e h block 5) + ((e h block 8).rotateLeft 50 ^^^ (e h block 8).rotateLeft 46 ^^^ (e h block 8).rotateLeft 23) + (((e h block 8) &&& (e h block 7)) + (~~~(e h block 8) &&& (e h block 6))) + (SHA512.roundConstants[8]!).toBitVec + (word block 8)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 8).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 5) + ((e h block 5) + bitVecBigSigma1 (e h block 8) + bitVecChoice (e h block 8) (e h block 7) (e h block 6) + (SHA512.roundConstants[8]!).toBitVec + (word block 8)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a10 (h : BitVecState) (block : Array Bool) :
    a h block 10 = ((e h block 6) + ((e h block 9).rotateLeft 50 ^^^ (e h block 9).rotateLeft 46 ^^^ (e h block 9).rotateLeft 23) + (((e h block 9) &&& (e h block 8)) + (~~~(e h block 9) &&& (e h block 7))) + (SHA512.roundConstants[9]!).toBitVec + (word block 9)) + (((a h block 9).rotateLeft 36 ^^^ (a h block 9).rotateLeft 30 ^^^ (a h block 9).rotateLeft 25) + ((((a h block 8) ^^^ (a h block 7)) &&& (a h block 9)) ^^^ ((a h block 8) &&& (a h block 7)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 9).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 6) + bitVecBigSigma1 (e h block 9) + bitVecChoice (e h block 9) (e h block 8) (e h block 7) + (SHA512.roundConstants[9]!).toBitVec + (word block 9)) + (bitVecBigSigma0 (a h block 9) + bitVecMajority (a h block 9) (a h block 8) (a h block 7)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e10 (h : BitVecState) (block : Array Bool) :
    e h block 10 = (a h block 6) + ((e h block 6) + ((e h block 9).rotateLeft 50 ^^^ (e h block 9).rotateLeft 46 ^^^ (e h block 9).rotateLeft 23) + (((e h block 9) &&& (e h block 8)) + (~~~(e h block 9) &&& (e h block 7))) + (SHA512.roundConstants[9]!).toBitVec + (word block 9)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 9).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 6) + ((e h block 6) + bitVecBigSigma1 (e h block 9) + bitVecChoice (e h block 9) (e h block 8) (e h block 7) + (SHA512.roundConstants[9]!).toBitVec + (word block 9)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a11 (h : BitVecState) (block : Array Bool) :
    a h block 11 = ((e h block 7) + ((e h block 10).rotateLeft 50 ^^^ (e h block 10).rotateLeft 46 ^^^ (e h block 10).rotateLeft 23) + (((e h block 10) &&& (e h block 9)) + (~~~(e h block 10) &&& (e h block 8))) + (SHA512.roundConstants[10]!).toBitVec + (word block 10)) + (((a h block 10).rotateLeft 36 ^^^ (a h block 10).rotateLeft 30 ^^^ (a h block 10).rotateLeft 25) + ((((a h block 9) ^^^ (a h block 8)) &&& (a h block 10)) ^^^ ((a h block 9) &&& (a h block 8)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 10).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 7) + bitVecBigSigma1 (e h block 10) + bitVecChoice (e h block 10) (e h block 9) (e h block 8) + (SHA512.roundConstants[10]!).toBitVec + (word block 10)) + (bitVecBigSigma0 (a h block 10) + bitVecMajority (a h block 10) (a h block 9) (a h block 8)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e11 (h : BitVecState) (block : Array Bool) :
    e h block 11 = (a h block 7) + ((e h block 7) + ((e h block 10).rotateLeft 50 ^^^ (e h block 10).rotateLeft 46 ^^^ (e h block 10).rotateLeft 23) + (((e h block 10) &&& (e h block 9)) + (~~~(e h block 10) &&& (e h block 8))) + (SHA512.roundConstants[10]!).toBitVec + (word block 10)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 10).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 7) + ((e h block 7) + bitVecBigSigma1 (e h block 10) + bitVecChoice (e h block 10) (e h block 9) (e h block 8) + (SHA512.roundConstants[10]!).toBitVec + (word block 10)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a12 (h : BitVecState) (block : Array Bool) :
    a h block 12 = ((e h block 8) + ((e h block 11).rotateLeft 50 ^^^ (e h block 11).rotateLeft 46 ^^^ (e h block 11).rotateLeft 23) + (((e h block 11) &&& (e h block 10)) + (~~~(e h block 11) &&& (e h block 9))) + (SHA512.roundConstants[11]!).toBitVec + (word block 11)) + (((a h block 11).rotateLeft 36 ^^^ (a h block 11).rotateLeft 30 ^^^ (a h block 11).rotateLeft 25) + ((((a h block 10) ^^^ (a h block 9)) &&& (a h block 11)) ^^^ ((a h block 10) &&& (a h block 9)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 11).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 8) + bitVecBigSigma1 (e h block 11) + bitVecChoice (e h block 11) (e h block 10) (e h block 9) + (SHA512.roundConstants[11]!).toBitVec + (word block 11)) + (bitVecBigSigma0 (a h block 11) + bitVecMajority (a h block 11) (a h block 10) (a h block 9)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e12 (h : BitVecState) (block : Array Bool) :
    e h block 12 = (a h block 8) + ((e h block 8) + ((e h block 11).rotateLeft 50 ^^^ (e h block 11).rotateLeft 46 ^^^ (e h block 11).rotateLeft 23) + (((e h block 11) &&& (e h block 10)) + (~~~(e h block 11) &&& (e h block 9))) + (SHA512.roundConstants[11]!).toBitVec + (word block 11)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 11).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 8) + ((e h block 8) + bitVecBigSigma1 (e h block 11) + bitVecChoice (e h block 11) (e h block 10) (e h block 9) + (SHA512.roundConstants[11]!).toBitVec + (word block 11)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a13 (h : BitVecState) (block : Array Bool) :
    a h block 13 = ((e h block 9) + ((e h block 12).rotateLeft 50 ^^^ (e h block 12).rotateLeft 46 ^^^ (e h block 12).rotateLeft 23) + (((e h block 12) &&& (e h block 11)) + (~~~(e h block 12) &&& (e h block 10))) + (SHA512.roundConstants[12]!).toBitVec + (word block 12)) + (((a h block 12).rotateLeft 36 ^^^ (a h block 12).rotateLeft 30 ^^^ (a h block 12).rotateLeft 25) + ((((a h block 11) ^^^ (a h block 10)) &&& (a h block 12)) ^^^ ((a h block 11) &&& (a h block 10)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 12).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 9) + bitVecBigSigma1 (e h block 12) + bitVecChoice (e h block 12) (e h block 11) (e h block 10) + (SHA512.roundConstants[12]!).toBitVec + (word block 12)) + (bitVecBigSigma0 (a h block 12) + bitVecMajority (a h block 12) (a h block 11) (a h block 10)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e13 (h : BitVecState) (block : Array Bool) :
    e h block 13 = (a h block 9) + ((e h block 9) + ((e h block 12).rotateLeft 50 ^^^ (e h block 12).rotateLeft 46 ^^^ (e h block 12).rotateLeft 23) + (((e h block 12) &&& (e h block 11)) + (~~~(e h block 12) &&& (e h block 10))) + (SHA512.roundConstants[12]!).toBitVec + (word block 12)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 12).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 9) + ((e h block 9) + bitVecBigSigma1 (e h block 12) + bitVecChoice (e h block 12) (e h block 11) (e h block 10) + (SHA512.roundConstants[12]!).toBitVec + (word block 12)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a14 (h : BitVecState) (block : Array Bool) :
    a h block 14 = ((e h block 10) + ((e h block 13).rotateLeft 50 ^^^ (e h block 13).rotateLeft 46 ^^^ (e h block 13).rotateLeft 23) + (((e h block 13) &&& (e h block 12)) + (~~~(e h block 13) &&& (e h block 11))) + (SHA512.roundConstants[13]!).toBitVec + (word block 13)) + (((a h block 13).rotateLeft 36 ^^^ (a h block 13).rotateLeft 30 ^^^ (a h block 13).rotateLeft 25) + ((((a h block 12) ^^^ (a h block 11)) &&& (a h block 13)) ^^^ ((a h block 12) &&& (a h block 11)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 13).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 10) + bitVecBigSigma1 (e h block 13) + bitVecChoice (e h block 13) (e h block 12) (e h block 11) + (SHA512.roundConstants[13]!).toBitVec + (word block 13)) + (bitVecBigSigma0 (a h block 13) + bitVecMajority (a h block 13) (a h block 12) (a h block 11)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e14 (h : BitVecState) (block : Array Bool) :
    e h block 14 = (a h block 10) + ((e h block 10) + ((e h block 13).rotateLeft 50 ^^^ (e h block 13).rotateLeft 46 ^^^ (e h block 13).rotateLeft 23) + (((e h block 13) &&& (e h block 12)) + (~~~(e h block 13) &&& (e h block 11))) + (SHA512.roundConstants[13]!).toBitVec + (word block 13)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 13).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 10) + ((e h block 10) + bitVecBigSigma1 (e h block 13) + bitVecChoice (e h block 13) (e h block 12) (e h block 11) + (SHA512.roundConstants[13]!).toBitVec + (word block 13)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a15 (h : BitVecState) (block : Array Bool) :
    a h block 15 = ((e h block 11) + ((e h block 14).rotateLeft 50 ^^^ (e h block 14).rotateLeft 46 ^^^ (e h block 14).rotateLeft 23) + (((e h block 14) &&& (e h block 13)) + (~~~(e h block 14) &&& (e h block 12))) + (SHA512.roundConstants[14]!).toBitVec + (word block 14)) + (((a h block 14).rotateLeft 36 ^^^ (a h block 14).rotateLeft 30 ^^^ (a h block 14).rotateLeft 25) + ((((a h block 13) ^^^ (a h block 12)) &&& (a h block 14)) ^^^ ((a h block 13) &&& (a h block 12)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 14).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 11) + bitVecBigSigma1 (e h block 14) + bitVecChoice (e h block 14) (e h block 13) (e h block 12) + (SHA512.roundConstants[14]!).toBitVec + (word block 14)) + (bitVecBigSigma0 (a h block 14) + bitVecMajority (a h block 14) (a h block 13) (a h block 12)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e15 (h : BitVecState) (block : Array Bool) :
    e h block 15 = (a h block 11) + ((e h block 11) + ((e h block 14).rotateLeft 50 ^^^ (e h block 14).rotateLeft 46 ^^^ (e h block 14).rotateLeft 23) + (((e h block 14) &&& (e h block 13)) + (~~~(e h block 14) &&& (e h block 12))) + (SHA512.roundConstants[14]!).toBitVec + (word block 14)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 14).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 11) + ((e h block 11) + bitVecBigSigma1 (e h block 14) + bitVecChoice (e h block 14) (e h block 13) (e h block 12) + (SHA512.roundConstants[14]!).toBitVec + (word block 14)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a16 (h : BitVecState) (block : Array Bool) :
    a h block 16 = ((e h block 12) + ((e h block 15).rotateLeft 50 ^^^ (e h block 15).rotateLeft 46 ^^^ (e h block 15).rotateLeft 23) + (((e h block 15) &&& (e h block 14)) + (~~~(e h block 15) &&& (e h block 13))) + (SHA512.roundConstants[15]!).toBitVec + (word block 15)) + (((a h block 15).rotateLeft 36 ^^^ (a h block 15).rotateLeft 30 ^^^ (a h block 15).rotateLeft 25) + ((((a h block 14) ^^^ (a h block 13)) &&& (a h block 15)) ^^^ ((a h block 14) &&& (a h block 13)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 15).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 12) + bitVecBigSigma1 (e h block 15) + bitVecChoice (e h block 15) (e h block 14) (e h block 13) + (SHA512.roundConstants[15]!).toBitVec + (word block 15)) + (bitVecBigSigma0 (a h block 15) + bitVecMajority (a h block 15) (a h block 14) (a h block 13)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e16 (h : BitVecState) (block : Array Bool) :
    e h block 16 = (a h block 12) + ((e h block 12) + ((e h block 15).rotateLeft 50 ^^^ (e h block 15).rotateLeft 46 ^^^ (e h block 15).rotateLeft 23) + (((e h block 15) &&& (e h block 14)) + (~~~(e h block 15) &&& (e h block 13))) + (SHA512.roundConstants[15]!).toBitVec + (word block 15)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 15).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 12) + ((e h block 12) + bitVecBigSigma1 (e h block 15) + bitVecChoice (e h block 15) (e h block 14) (e h block 13) + (SHA512.roundConstants[15]!).toBitVec + (word block 15)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a17 (h : BitVecState) (block : Array Bool) :
    a h block 17 = ((e h block 13) + ((e h block 16).rotateLeft 50 ^^^ (e h block 16).rotateLeft 46 ^^^ (e h block 16).rotateLeft 23) + (((e h block 16) &&& (e h block 15)) + (~~~(e h block 16) &&& (e h block 14))) + (SHA512.roundConstants[16]!).toBitVec + (word block 16)) + (((a h block 16).rotateLeft 36 ^^^ (a h block 16).rotateLeft 30 ^^^ (a h block 16).rotateLeft 25) + ((((a h block 15) ^^^ (a h block 14)) &&& (a h block 16)) ^^^ ((a h block 15) &&& (a h block 14)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 16).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 13) + bitVecBigSigma1 (e h block 16) + bitVecChoice (e h block 16) (e h block 15) (e h block 14) + (SHA512.roundConstants[16]!).toBitVec + (word block 16)) + (bitVecBigSigma0 (a h block 16) + bitVecMajority (a h block 16) (a h block 15) (a h block 14)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e17 (h : BitVecState) (block : Array Bool) :
    e h block 17 = (a h block 13) + ((e h block 13) + ((e h block 16).rotateLeft 50 ^^^ (e h block 16).rotateLeft 46 ^^^ (e h block 16).rotateLeft 23) + (((e h block 16) &&& (e h block 15)) + (~~~(e h block 16) &&& (e h block 14))) + (SHA512.roundConstants[16]!).toBitVec + (word block 16)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 16).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 13) + ((e h block 13) + bitVecBigSigma1 (e h block 16) + bitVecChoice (e h block 16) (e h block 15) (e h block 14) + (SHA512.roundConstants[16]!).toBitVec + (word block 16)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a18 (h : BitVecState) (block : Array Bool) :
    a h block 18 = ((e h block 14) + ((e h block 17).rotateLeft 50 ^^^ (e h block 17).rotateLeft 46 ^^^ (e h block 17).rotateLeft 23) + (((e h block 17) &&& (e h block 16)) + (~~~(e h block 17) &&& (e h block 15))) + (SHA512.roundConstants[17]!).toBitVec + (word block 17)) + (((a h block 17).rotateLeft 36 ^^^ (a h block 17).rotateLeft 30 ^^^ (a h block 17).rotateLeft 25) + ((((a h block 16) ^^^ (a h block 15)) &&& (a h block 17)) ^^^ ((a h block 16) &&& (a h block 15)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 17).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 14) + bitVecBigSigma1 (e h block 17) + bitVecChoice (e h block 17) (e h block 16) (e h block 15) + (SHA512.roundConstants[17]!).toBitVec + (word block 17)) + (bitVecBigSigma0 (a h block 17) + bitVecMajority (a h block 17) (a h block 16) (a h block 15)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e18 (h : BitVecState) (block : Array Bool) :
    e h block 18 = (a h block 14) + ((e h block 14) + ((e h block 17).rotateLeft 50 ^^^ (e h block 17).rotateLeft 46 ^^^ (e h block 17).rotateLeft 23) + (((e h block 17) &&& (e h block 16)) + (~~~(e h block 17) &&& (e h block 15))) + (SHA512.roundConstants[17]!).toBitVec + (word block 17)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 17).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 14) + ((e h block 14) + bitVecBigSigma1 (e h block 17) + bitVecChoice (e h block 17) (e h block 16) (e h block 15) + (SHA512.roundConstants[17]!).toBitVec + (word block 17)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a19 (h : BitVecState) (block : Array Bool) :
    a h block 19 = ((e h block 15) + ((e h block 18).rotateLeft 50 ^^^ (e h block 18).rotateLeft 46 ^^^ (e h block 18).rotateLeft 23) + (((e h block 18) &&& (e h block 17)) + (~~~(e h block 18) &&& (e h block 16))) + (SHA512.roundConstants[18]!).toBitVec + (word block 18)) + (((a h block 18).rotateLeft 36 ^^^ (a h block 18).rotateLeft 30 ^^^ (a h block 18).rotateLeft 25) + ((((a h block 17) ^^^ (a h block 16)) &&& (a h block 18)) ^^^ ((a h block 17) &&& (a h block 16)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 18).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 15) + bitVecBigSigma1 (e h block 18) + bitVecChoice (e h block 18) (e h block 17) (e h block 16) + (SHA512.roundConstants[18]!).toBitVec + (word block 18)) + (bitVecBigSigma0 (a h block 18) + bitVecMajority (a h block 18) (a h block 17) (a h block 16)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e19 (h : BitVecState) (block : Array Bool) :
    e h block 19 = (a h block 15) + ((e h block 15) + ((e h block 18).rotateLeft 50 ^^^ (e h block 18).rotateLeft 46 ^^^ (e h block 18).rotateLeft 23) + (((e h block 18) &&& (e h block 17)) + (~~~(e h block 18) &&& (e h block 16))) + (SHA512.roundConstants[18]!).toBitVec + (word block 18)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 18).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 15) + ((e h block 15) + bitVecBigSigma1 (e h block 18) + bitVecChoice (e h block 18) (e h block 17) (e h block 16) + (SHA512.roundConstants[18]!).toBitVec + (word block 18)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a20 (h : BitVecState) (block : Array Bool) :
    a h block 20 = ((e h block 16) + ((e h block 19).rotateLeft 50 ^^^ (e h block 19).rotateLeft 46 ^^^ (e h block 19).rotateLeft 23) + (((e h block 19) &&& (e h block 18)) + (~~~(e h block 19) &&& (e h block 17))) + (SHA512.roundConstants[19]!).toBitVec + (word block 19)) + (((a h block 19).rotateLeft 36 ^^^ (a h block 19).rotateLeft 30 ^^^ (a h block 19).rotateLeft 25) + ((((a h block 18) ^^^ (a h block 17)) &&& (a h block 19)) ^^^ ((a h block 18) &&& (a h block 17)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 19).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 16) + bitVecBigSigma1 (e h block 19) + bitVecChoice (e h block 19) (e h block 18) (e h block 17) + (SHA512.roundConstants[19]!).toBitVec + (word block 19)) + (bitVecBigSigma0 (a h block 19) + bitVecMajority (a h block 19) (a h block 18) (a h block 17)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e20 (h : BitVecState) (block : Array Bool) :
    e h block 20 = (a h block 16) + ((e h block 16) + ((e h block 19).rotateLeft 50 ^^^ (e h block 19).rotateLeft 46 ^^^ (e h block 19).rotateLeft 23) + (((e h block 19) &&& (e h block 18)) + (~~~(e h block 19) &&& (e h block 17))) + (SHA512.roundConstants[19]!).toBitVec + (word block 19)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 19).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 16) + ((e h block 16) + bitVecBigSigma1 (e h block 19) + bitVecChoice (e h block 19) (e h block 18) (e h block 17) + (SHA512.roundConstants[19]!).toBitVec + (word block 19)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a21 (h : BitVecState) (block : Array Bool) :
    a h block 21 = ((e h block 17) + ((e h block 20).rotateLeft 50 ^^^ (e h block 20).rotateLeft 46 ^^^ (e h block 20).rotateLeft 23) + (((e h block 20) &&& (e h block 19)) + (~~~(e h block 20) &&& (e h block 18))) + (SHA512.roundConstants[20]!).toBitVec + (word block 20)) + (((a h block 20).rotateLeft 36 ^^^ (a h block 20).rotateLeft 30 ^^^ (a h block 20).rotateLeft 25) + ((((a h block 19) ^^^ (a h block 18)) &&& (a h block 20)) ^^^ ((a h block 19) &&& (a h block 18)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 20).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 17) + bitVecBigSigma1 (e h block 20) + bitVecChoice (e h block 20) (e h block 19) (e h block 18) + (SHA512.roundConstants[20]!).toBitVec + (word block 20)) + (bitVecBigSigma0 (a h block 20) + bitVecMajority (a h block 20) (a h block 19) (a h block 18)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e21 (h : BitVecState) (block : Array Bool) :
    e h block 21 = (a h block 17) + ((e h block 17) + ((e h block 20).rotateLeft 50 ^^^ (e h block 20).rotateLeft 46 ^^^ (e h block 20).rotateLeft 23) + (((e h block 20) &&& (e h block 19)) + (~~~(e h block 20) &&& (e h block 18))) + (SHA512.roundConstants[20]!).toBitVec + (word block 20)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 20).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 17) + ((e h block 17) + bitVecBigSigma1 (e h block 20) + bitVecChoice (e h block 20) (e h block 19) (e h block 18) + (SHA512.roundConstants[20]!).toBitVec + (word block 20)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a22 (h : BitVecState) (block : Array Bool) :
    a h block 22 = ((e h block 18) + ((e h block 21).rotateLeft 50 ^^^ (e h block 21).rotateLeft 46 ^^^ (e h block 21).rotateLeft 23) + (((e h block 21) &&& (e h block 20)) + (~~~(e h block 21) &&& (e h block 19))) + (SHA512.roundConstants[21]!).toBitVec + (word block 21)) + (((a h block 21).rotateLeft 36 ^^^ (a h block 21).rotateLeft 30 ^^^ (a h block 21).rotateLeft 25) + ((((a h block 20) ^^^ (a h block 19)) &&& (a h block 21)) ^^^ ((a h block 20) &&& (a h block 19)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 21).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 18) + bitVecBigSigma1 (e h block 21) + bitVecChoice (e h block 21) (e h block 20) (e h block 19) + (SHA512.roundConstants[21]!).toBitVec + (word block 21)) + (bitVecBigSigma0 (a h block 21) + bitVecMajority (a h block 21) (a h block 20) (a h block 19)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e22 (h : BitVecState) (block : Array Bool) :
    e h block 22 = (a h block 18) + ((e h block 18) + ((e h block 21).rotateLeft 50 ^^^ (e h block 21).rotateLeft 46 ^^^ (e h block 21).rotateLeft 23) + (((e h block 21) &&& (e h block 20)) + (~~~(e h block 21) &&& (e h block 19))) + (SHA512.roundConstants[21]!).toBitVec + (word block 21)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 21).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 18) + ((e h block 18) + bitVecBigSigma1 (e h block 21) + bitVecChoice (e h block 21) (e h block 20) (e h block 19) + (SHA512.roundConstants[21]!).toBitVec + (word block 21)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a23 (h : BitVecState) (block : Array Bool) :
    a h block 23 = ((e h block 19) + ((e h block 22).rotateLeft 50 ^^^ (e h block 22).rotateLeft 46 ^^^ (e h block 22).rotateLeft 23) + (((e h block 22) &&& (e h block 21)) + (~~~(e h block 22) &&& (e h block 20))) + (SHA512.roundConstants[22]!).toBitVec + (word block 22)) + (((a h block 22).rotateLeft 36 ^^^ (a h block 22).rotateLeft 30 ^^^ (a h block 22).rotateLeft 25) + ((((a h block 21) ^^^ (a h block 20)) &&& (a h block 22)) ^^^ ((a h block 21) &&& (a h block 20)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 22).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 19) + bitVecBigSigma1 (e h block 22) + bitVecChoice (e h block 22) (e h block 21) (e h block 20) + (SHA512.roundConstants[22]!).toBitVec + (word block 22)) + (bitVecBigSigma0 (a h block 22) + bitVecMajority (a h block 22) (a h block 21) (a h block 20)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e23 (h : BitVecState) (block : Array Bool) :
    e h block 23 = (a h block 19) + ((e h block 19) + ((e h block 22).rotateLeft 50 ^^^ (e h block 22).rotateLeft 46 ^^^ (e h block 22).rotateLeft 23) + (((e h block 22) &&& (e h block 21)) + (~~~(e h block 22) &&& (e h block 20))) + (SHA512.roundConstants[22]!).toBitVec + (word block 22)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 22).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 19) + ((e h block 19) + bitVecBigSigma1 (e h block 22) + bitVecChoice (e h block 22) (e h block 21) (e h block 20) + (SHA512.roundConstants[22]!).toBitVec + (word block 22)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a24 (h : BitVecState) (block : Array Bool) :
    a h block 24 = ((e h block 20) + ((e h block 23).rotateLeft 50 ^^^ (e h block 23).rotateLeft 46 ^^^ (e h block 23).rotateLeft 23) + (((e h block 23) &&& (e h block 22)) + (~~~(e h block 23) &&& (e h block 21))) + (SHA512.roundConstants[23]!).toBitVec + (word block 23)) + (((a h block 23).rotateLeft 36 ^^^ (a h block 23).rotateLeft 30 ^^^ (a h block 23).rotateLeft 25) + ((((a h block 22) ^^^ (a h block 21)) &&& (a h block 23)) ^^^ ((a h block 22) &&& (a h block 21)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 23).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 20) + bitVecBigSigma1 (e h block 23) + bitVecChoice (e h block 23) (e h block 22) (e h block 21) + (SHA512.roundConstants[23]!).toBitVec + (word block 23)) + (bitVecBigSigma0 (a h block 23) + bitVecMajority (a h block 23) (a h block 22) (a h block 21)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e24 (h : BitVecState) (block : Array Bool) :
    e h block 24 = (a h block 20) + ((e h block 20) + ((e h block 23).rotateLeft 50 ^^^ (e h block 23).rotateLeft 46 ^^^ (e h block 23).rotateLeft 23) + (((e h block 23) &&& (e h block 22)) + (~~~(e h block 23) &&& (e h block 21))) + (SHA512.roundConstants[23]!).toBitVec + (word block 23)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 23).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 20) + ((e h block 20) + bitVecBigSigma1 (e h block 23) + bitVecChoice (e h block 23) (e h block 22) (e h block 21) + (SHA512.roundConstants[23]!).toBitVec + (word block 23)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a25 (h : BitVecState) (block : Array Bool) :
    a h block 25 = ((e h block 21) + ((e h block 24).rotateLeft 50 ^^^ (e h block 24).rotateLeft 46 ^^^ (e h block 24).rotateLeft 23) + (((e h block 24) &&& (e h block 23)) + (~~~(e h block 24) &&& (e h block 22))) + (SHA512.roundConstants[24]!).toBitVec + (word block 24)) + (((a h block 24).rotateLeft 36 ^^^ (a h block 24).rotateLeft 30 ^^^ (a h block 24).rotateLeft 25) + ((((a h block 23) ^^^ (a h block 22)) &&& (a h block 24)) ^^^ ((a h block 23) &&& (a h block 22)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 24).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 21) + bitVecBigSigma1 (e h block 24) + bitVecChoice (e h block 24) (e h block 23) (e h block 22) + (SHA512.roundConstants[24]!).toBitVec + (word block 24)) + (bitVecBigSigma0 (a h block 24) + bitVecMajority (a h block 24) (a h block 23) (a h block 22)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e25 (h : BitVecState) (block : Array Bool) :
    e h block 25 = (a h block 21) + ((e h block 21) + ((e h block 24).rotateLeft 50 ^^^ (e h block 24).rotateLeft 46 ^^^ (e h block 24).rotateLeft 23) + (((e h block 24) &&& (e h block 23)) + (~~~(e h block 24) &&& (e h block 22))) + (SHA512.roundConstants[24]!).toBitVec + (word block 24)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 24).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 21) + ((e h block 21) + bitVecBigSigma1 (e h block 24) + bitVecChoice (e h block 24) (e h block 23) (e h block 22) + (SHA512.roundConstants[24]!).toBitVec + (word block 24)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a26 (h : BitVecState) (block : Array Bool) :
    a h block 26 = ((e h block 22) + ((e h block 25).rotateLeft 50 ^^^ (e h block 25).rotateLeft 46 ^^^ (e h block 25).rotateLeft 23) + (((e h block 25) &&& (e h block 24)) + (~~~(e h block 25) &&& (e h block 23))) + (SHA512.roundConstants[25]!).toBitVec + (word block 25)) + (((a h block 25).rotateLeft 36 ^^^ (a h block 25).rotateLeft 30 ^^^ (a h block 25).rotateLeft 25) + ((((a h block 24) ^^^ (a h block 23)) &&& (a h block 25)) ^^^ ((a h block 24) &&& (a h block 23)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 25).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 22) + bitVecBigSigma1 (e h block 25) + bitVecChoice (e h block 25) (e h block 24) (e h block 23) + (SHA512.roundConstants[25]!).toBitVec + (word block 25)) + (bitVecBigSigma0 (a h block 25) + bitVecMajority (a h block 25) (a h block 24) (a h block 23)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e26 (h : BitVecState) (block : Array Bool) :
    e h block 26 = (a h block 22) + ((e h block 22) + ((e h block 25).rotateLeft 50 ^^^ (e h block 25).rotateLeft 46 ^^^ (e h block 25).rotateLeft 23) + (((e h block 25) &&& (e h block 24)) + (~~~(e h block 25) &&& (e h block 23))) + (SHA512.roundConstants[25]!).toBitVec + (word block 25)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 25).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 22) + ((e h block 22) + bitVecBigSigma1 (e h block 25) + bitVecChoice (e h block 25) (e h block 24) (e h block 23) + (SHA512.roundConstants[25]!).toBitVec + (word block 25)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a27 (h : BitVecState) (block : Array Bool) :
    a h block 27 = ((e h block 23) + ((e h block 26).rotateLeft 50 ^^^ (e h block 26).rotateLeft 46 ^^^ (e h block 26).rotateLeft 23) + (((e h block 26) &&& (e h block 25)) + (~~~(e h block 26) &&& (e h block 24))) + (SHA512.roundConstants[26]!).toBitVec + (word block 26)) + (((a h block 26).rotateLeft 36 ^^^ (a h block 26).rotateLeft 30 ^^^ (a h block 26).rotateLeft 25) + ((((a h block 25) ^^^ (a h block 24)) &&& (a h block 26)) ^^^ ((a h block 25) &&& (a h block 24)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 26).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 23) + bitVecBigSigma1 (e h block 26) + bitVecChoice (e h block 26) (e h block 25) (e h block 24) + (SHA512.roundConstants[26]!).toBitVec + (word block 26)) + (bitVecBigSigma0 (a h block 26) + bitVecMajority (a h block 26) (a h block 25) (a h block 24)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e27 (h : BitVecState) (block : Array Bool) :
    e h block 27 = (a h block 23) + ((e h block 23) + ((e h block 26).rotateLeft 50 ^^^ (e h block 26).rotateLeft 46 ^^^ (e h block 26).rotateLeft 23) + (((e h block 26) &&& (e h block 25)) + (~~~(e h block 26) &&& (e h block 24))) + (SHA512.roundConstants[26]!).toBitVec + (word block 26)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 26).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 23) + ((e h block 23) + bitVecBigSigma1 (e h block 26) + bitVecChoice (e h block 26) (e h block 25) (e h block 24) + (SHA512.roundConstants[26]!).toBitVec + (word block 26)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a28 (h : BitVecState) (block : Array Bool) :
    a h block 28 = ((e h block 24) + ((e h block 27).rotateLeft 50 ^^^ (e h block 27).rotateLeft 46 ^^^ (e h block 27).rotateLeft 23) + (((e h block 27) &&& (e h block 26)) + (~~~(e h block 27) &&& (e h block 25))) + (SHA512.roundConstants[27]!).toBitVec + (word block 27)) + (((a h block 27).rotateLeft 36 ^^^ (a h block 27).rotateLeft 30 ^^^ (a h block 27).rotateLeft 25) + ((((a h block 26) ^^^ (a h block 25)) &&& (a h block 27)) ^^^ ((a h block 26) &&& (a h block 25)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 27).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 24) + bitVecBigSigma1 (e h block 27) + bitVecChoice (e h block 27) (e h block 26) (e h block 25) + (SHA512.roundConstants[27]!).toBitVec + (word block 27)) + (bitVecBigSigma0 (a h block 27) + bitVecMajority (a h block 27) (a h block 26) (a h block 25)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e28 (h : BitVecState) (block : Array Bool) :
    e h block 28 = (a h block 24) + ((e h block 24) + ((e h block 27).rotateLeft 50 ^^^ (e h block 27).rotateLeft 46 ^^^ (e h block 27).rotateLeft 23) + (((e h block 27) &&& (e h block 26)) + (~~~(e h block 27) &&& (e h block 25))) + (SHA512.roundConstants[27]!).toBitVec + (word block 27)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 27).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 24) + ((e h block 24) + bitVecBigSigma1 (e h block 27) + bitVecChoice (e h block 27) (e h block 26) (e h block 25) + (SHA512.roundConstants[27]!).toBitVec + (word block 27)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a29 (h : BitVecState) (block : Array Bool) :
    a h block 29 = ((e h block 25) + ((e h block 28).rotateLeft 50 ^^^ (e h block 28).rotateLeft 46 ^^^ (e h block 28).rotateLeft 23) + (((e h block 28) &&& (e h block 27)) + (~~~(e h block 28) &&& (e h block 26))) + (SHA512.roundConstants[28]!).toBitVec + (word block 28)) + (((a h block 28).rotateLeft 36 ^^^ (a h block 28).rotateLeft 30 ^^^ (a h block 28).rotateLeft 25) + ((((a h block 27) ^^^ (a h block 26)) &&& (a h block 28)) ^^^ ((a h block 27) &&& (a h block 26)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 28).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 25) + bitVecBigSigma1 (e h block 28) + bitVecChoice (e h block 28) (e h block 27) (e h block 26) + (SHA512.roundConstants[28]!).toBitVec + (word block 28)) + (bitVecBigSigma0 (a h block 28) + bitVecMajority (a h block 28) (a h block 27) (a h block 26)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e29 (h : BitVecState) (block : Array Bool) :
    e h block 29 = (a h block 25) + ((e h block 25) + ((e h block 28).rotateLeft 50 ^^^ (e h block 28).rotateLeft 46 ^^^ (e h block 28).rotateLeft 23) + (((e h block 28) &&& (e h block 27)) + (~~~(e h block 28) &&& (e h block 26))) + (SHA512.roundConstants[28]!).toBitVec + (word block 28)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 28).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 25) + ((e h block 25) + bitVecBigSigma1 (e h block 28) + bitVecChoice (e h block 28) (e h block 27) (e h block 26) + (SHA512.roundConstants[28]!).toBitVec + (word block 28)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a30 (h : BitVecState) (block : Array Bool) :
    a h block 30 = ((e h block 26) + ((e h block 29).rotateLeft 50 ^^^ (e h block 29).rotateLeft 46 ^^^ (e h block 29).rotateLeft 23) + (((e h block 29) &&& (e h block 28)) + (~~~(e h block 29) &&& (e h block 27))) + (SHA512.roundConstants[29]!).toBitVec + (word block 29)) + (((a h block 29).rotateLeft 36 ^^^ (a h block 29).rotateLeft 30 ^^^ (a h block 29).rotateLeft 25) + ((((a h block 28) ^^^ (a h block 27)) &&& (a h block 29)) ^^^ ((a h block 28) &&& (a h block 27)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 29).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 26) + bitVecBigSigma1 (e h block 29) + bitVecChoice (e h block 29) (e h block 28) (e h block 27) + (SHA512.roundConstants[29]!).toBitVec + (word block 29)) + (bitVecBigSigma0 (a h block 29) + bitVecMajority (a h block 29) (a h block 28) (a h block 27)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e30 (h : BitVecState) (block : Array Bool) :
    e h block 30 = (a h block 26) + ((e h block 26) + ((e h block 29).rotateLeft 50 ^^^ (e h block 29).rotateLeft 46 ^^^ (e h block 29).rotateLeft 23) + (((e h block 29) &&& (e h block 28)) + (~~~(e h block 29) &&& (e h block 27))) + (SHA512.roundConstants[29]!).toBitVec + (word block 29)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 29).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 26) + ((e h block 26) + bitVecBigSigma1 (e h block 29) + bitVecChoice (e h block 29) (e h block 28) (e h block 27) + (SHA512.roundConstants[29]!).toBitVec + (word block 29)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a31 (h : BitVecState) (block : Array Bool) :
    a h block 31 = ((e h block 27) + ((e h block 30).rotateLeft 50 ^^^ (e h block 30).rotateLeft 46 ^^^ (e h block 30).rotateLeft 23) + (((e h block 30) &&& (e h block 29)) + (~~~(e h block 30) &&& (e h block 28))) + (SHA512.roundConstants[30]!).toBitVec + (word block 30)) + (((a h block 30).rotateLeft 36 ^^^ (a h block 30).rotateLeft 30 ^^^ (a h block 30).rotateLeft 25) + ((((a h block 29) ^^^ (a h block 28)) &&& (a h block 30)) ^^^ ((a h block 29) &&& (a h block 28)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 30).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 27) + bitVecBigSigma1 (e h block 30) + bitVecChoice (e h block 30) (e h block 29) (e h block 28) + (SHA512.roundConstants[30]!).toBitVec + (word block 30)) + (bitVecBigSigma0 (a h block 30) + bitVecMajority (a h block 30) (a h block 29) (a h block 28)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e31 (h : BitVecState) (block : Array Bool) :
    e h block 31 = (a h block 27) + ((e h block 27) + ((e h block 30).rotateLeft 50 ^^^ (e h block 30).rotateLeft 46 ^^^ (e h block 30).rotateLeft 23) + (((e h block 30) &&& (e h block 29)) + (~~~(e h block 30) &&& (e h block 28))) + (SHA512.roundConstants[30]!).toBitVec + (word block 30)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 30).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 27) + ((e h block 27) + bitVecBigSigma1 (e h block 30) + bitVecChoice (e h block 30) (e h block 29) (e h block 28) + (SHA512.roundConstants[30]!).toBitVec + (word block 30)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a32 (h : BitVecState) (block : Array Bool) :
    a h block 32 = ((e h block 28) + ((e h block 31).rotateLeft 50 ^^^ (e h block 31).rotateLeft 46 ^^^ (e h block 31).rotateLeft 23) + (((e h block 31) &&& (e h block 30)) + (~~~(e h block 31) &&& (e h block 29))) + (SHA512.roundConstants[31]!).toBitVec + (word block 31)) + (((a h block 31).rotateLeft 36 ^^^ (a h block 31).rotateLeft 30 ^^^ (a h block 31).rotateLeft 25) + ((((a h block 30) ^^^ (a h block 29)) &&& (a h block 31)) ^^^ ((a h block 30) &&& (a h block 29)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 31).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 28) + bitVecBigSigma1 (e h block 31) + bitVecChoice (e h block 31) (e h block 30) (e h block 29) + (SHA512.roundConstants[31]!).toBitVec + (word block 31)) + (bitVecBigSigma0 (a h block 31) + bitVecMajority (a h block 31) (a h block 30) (a h block 29)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e32 (h : BitVecState) (block : Array Bool) :
    e h block 32 = (a h block 28) + ((e h block 28) + ((e h block 31).rotateLeft 50 ^^^ (e h block 31).rotateLeft 46 ^^^ (e h block 31).rotateLeft 23) + (((e h block 31) &&& (e h block 30)) + (~~~(e h block 31) &&& (e h block 29))) + (SHA512.roundConstants[31]!).toBitVec + (word block 31)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 31).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 28) + ((e h block 28) + bitVecBigSigma1 (e h block 31) + bitVecChoice (e h block 31) (e h block 30) (e h block 29) + (SHA512.roundConstants[31]!).toBitVec + (word block 31)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a33 (h : BitVecState) (block : Array Bool) :
    a h block 33 = ((e h block 29) + ((e h block 32).rotateLeft 50 ^^^ (e h block 32).rotateLeft 46 ^^^ (e h block 32).rotateLeft 23) + (((e h block 32) &&& (e h block 31)) + (~~~(e h block 32) &&& (e h block 30))) + (SHA512.roundConstants[32]!).toBitVec + (word block 32)) + (((a h block 32).rotateLeft 36 ^^^ (a h block 32).rotateLeft 30 ^^^ (a h block 32).rotateLeft 25) + ((((a h block 31) ^^^ (a h block 30)) &&& (a h block 32)) ^^^ ((a h block 31) &&& (a h block 30)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 32).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 29) + bitVecBigSigma1 (e h block 32) + bitVecChoice (e h block 32) (e h block 31) (e h block 30) + (SHA512.roundConstants[32]!).toBitVec + (word block 32)) + (bitVecBigSigma0 (a h block 32) + bitVecMajority (a h block 32) (a h block 31) (a h block 30)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e33 (h : BitVecState) (block : Array Bool) :
    e h block 33 = (a h block 29) + ((e h block 29) + ((e h block 32).rotateLeft 50 ^^^ (e h block 32).rotateLeft 46 ^^^ (e h block 32).rotateLeft 23) + (((e h block 32) &&& (e h block 31)) + (~~~(e h block 32) &&& (e h block 30))) + (SHA512.roundConstants[32]!).toBitVec + (word block 32)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 32).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 29) + ((e h block 29) + bitVecBigSigma1 (e h block 32) + bitVecChoice (e h block 32) (e h block 31) (e h block 30) + (SHA512.roundConstants[32]!).toBitVec + (word block 32)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a34 (h : BitVecState) (block : Array Bool) :
    a h block 34 = ((e h block 30) + ((e h block 33).rotateLeft 50 ^^^ (e h block 33).rotateLeft 46 ^^^ (e h block 33).rotateLeft 23) + (((e h block 33) &&& (e h block 32)) + (~~~(e h block 33) &&& (e h block 31))) + (SHA512.roundConstants[33]!).toBitVec + (word block 33)) + (((a h block 33).rotateLeft 36 ^^^ (a h block 33).rotateLeft 30 ^^^ (a h block 33).rotateLeft 25) + ((((a h block 32) ^^^ (a h block 31)) &&& (a h block 33)) ^^^ ((a h block 32) &&& (a h block 31)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 33).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 30) + bitVecBigSigma1 (e h block 33) + bitVecChoice (e h block 33) (e h block 32) (e h block 31) + (SHA512.roundConstants[33]!).toBitVec + (word block 33)) + (bitVecBigSigma0 (a h block 33) + bitVecMajority (a h block 33) (a h block 32) (a h block 31)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e34 (h : BitVecState) (block : Array Bool) :
    e h block 34 = (a h block 30) + ((e h block 30) + ((e h block 33).rotateLeft 50 ^^^ (e h block 33).rotateLeft 46 ^^^ (e h block 33).rotateLeft 23) + (((e h block 33) &&& (e h block 32)) + (~~~(e h block 33) &&& (e h block 31))) + (SHA512.roundConstants[33]!).toBitVec + (word block 33)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 33).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 30) + ((e h block 30) + bitVecBigSigma1 (e h block 33) + bitVecChoice (e h block 33) (e h block 32) (e h block 31) + (SHA512.roundConstants[33]!).toBitVec + (word block 33)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a35 (h : BitVecState) (block : Array Bool) :
    a h block 35 = ((e h block 31) + ((e h block 34).rotateLeft 50 ^^^ (e h block 34).rotateLeft 46 ^^^ (e h block 34).rotateLeft 23) + (((e h block 34) &&& (e h block 33)) + (~~~(e h block 34) &&& (e h block 32))) + (SHA512.roundConstants[34]!).toBitVec + (word block 34)) + (((a h block 34).rotateLeft 36 ^^^ (a h block 34).rotateLeft 30 ^^^ (a h block 34).rotateLeft 25) + ((((a h block 33) ^^^ (a h block 32)) &&& (a h block 34)) ^^^ ((a h block 33) &&& (a h block 32)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 34).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 31) + bitVecBigSigma1 (e h block 34) + bitVecChoice (e h block 34) (e h block 33) (e h block 32) + (SHA512.roundConstants[34]!).toBitVec + (word block 34)) + (bitVecBigSigma0 (a h block 34) + bitVecMajority (a h block 34) (a h block 33) (a h block 32)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e35 (h : BitVecState) (block : Array Bool) :
    e h block 35 = (a h block 31) + ((e h block 31) + ((e h block 34).rotateLeft 50 ^^^ (e h block 34).rotateLeft 46 ^^^ (e h block 34).rotateLeft 23) + (((e h block 34) &&& (e h block 33)) + (~~~(e h block 34) &&& (e h block 32))) + (SHA512.roundConstants[34]!).toBitVec + (word block 34)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 34).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 31) + ((e h block 31) + bitVecBigSigma1 (e h block 34) + bitVecChoice (e h block 34) (e h block 33) (e h block 32) + (SHA512.roundConstants[34]!).toBitVec + (word block 34)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a36 (h : BitVecState) (block : Array Bool) :
    a h block 36 = ((e h block 32) + ((e h block 35).rotateLeft 50 ^^^ (e h block 35).rotateLeft 46 ^^^ (e h block 35).rotateLeft 23) + (((e h block 35) &&& (e h block 34)) + (~~~(e h block 35) &&& (e h block 33))) + (SHA512.roundConstants[35]!).toBitVec + (word block 35)) + (((a h block 35).rotateLeft 36 ^^^ (a h block 35).rotateLeft 30 ^^^ (a h block 35).rotateLeft 25) + ((((a h block 34) ^^^ (a h block 33)) &&& (a h block 35)) ^^^ ((a h block 34) &&& (a h block 33)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 35).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 32) + bitVecBigSigma1 (e h block 35) + bitVecChoice (e h block 35) (e h block 34) (e h block 33) + (SHA512.roundConstants[35]!).toBitVec + (word block 35)) + (bitVecBigSigma0 (a h block 35) + bitVecMajority (a h block 35) (a h block 34) (a h block 33)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e36 (h : BitVecState) (block : Array Bool) :
    e h block 36 = (a h block 32) + ((e h block 32) + ((e h block 35).rotateLeft 50 ^^^ (e h block 35).rotateLeft 46 ^^^ (e h block 35).rotateLeft 23) + (((e h block 35) &&& (e h block 34)) + (~~~(e h block 35) &&& (e h block 33))) + (SHA512.roundConstants[35]!).toBitVec + (word block 35)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 35).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 32) + ((e h block 32) + bitVecBigSigma1 (e h block 35) + bitVecChoice (e h block 35) (e h block 34) (e h block 33) + (SHA512.roundConstants[35]!).toBitVec + (word block 35)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a37 (h : BitVecState) (block : Array Bool) :
    a h block 37 = ((e h block 33) + ((e h block 36).rotateLeft 50 ^^^ (e h block 36).rotateLeft 46 ^^^ (e h block 36).rotateLeft 23) + (((e h block 36) &&& (e h block 35)) + (~~~(e h block 36) &&& (e h block 34))) + (SHA512.roundConstants[36]!).toBitVec + (word block 36)) + (((a h block 36).rotateLeft 36 ^^^ (a h block 36).rotateLeft 30 ^^^ (a h block 36).rotateLeft 25) + ((((a h block 35) ^^^ (a h block 34)) &&& (a h block 36)) ^^^ ((a h block 35) &&& (a h block 34)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 36).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 33) + bitVecBigSigma1 (e h block 36) + bitVecChoice (e h block 36) (e h block 35) (e h block 34) + (SHA512.roundConstants[36]!).toBitVec + (word block 36)) + (bitVecBigSigma0 (a h block 36) + bitVecMajority (a h block 36) (a h block 35) (a h block 34)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e37 (h : BitVecState) (block : Array Bool) :
    e h block 37 = (a h block 33) + ((e h block 33) + ((e h block 36).rotateLeft 50 ^^^ (e h block 36).rotateLeft 46 ^^^ (e h block 36).rotateLeft 23) + (((e h block 36) &&& (e h block 35)) + (~~~(e h block 36) &&& (e h block 34))) + (SHA512.roundConstants[36]!).toBitVec + (word block 36)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 36).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 33) + ((e h block 33) + bitVecBigSigma1 (e h block 36) + bitVecChoice (e h block 36) (e h block 35) (e h block 34) + (SHA512.roundConstants[36]!).toBitVec + (word block 36)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a38 (h : BitVecState) (block : Array Bool) :
    a h block 38 = ((e h block 34) + ((e h block 37).rotateLeft 50 ^^^ (e h block 37).rotateLeft 46 ^^^ (e h block 37).rotateLeft 23) + (((e h block 37) &&& (e h block 36)) + (~~~(e h block 37) &&& (e h block 35))) + (SHA512.roundConstants[37]!).toBitVec + (word block 37)) + (((a h block 37).rotateLeft 36 ^^^ (a h block 37).rotateLeft 30 ^^^ (a h block 37).rotateLeft 25) + ((((a h block 36) ^^^ (a h block 35)) &&& (a h block 37)) ^^^ ((a h block 36) &&& (a h block 35)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 37).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 34) + bitVecBigSigma1 (e h block 37) + bitVecChoice (e h block 37) (e h block 36) (e h block 35) + (SHA512.roundConstants[37]!).toBitVec + (word block 37)) + (bitVecBigSigma0 (a h block 37) + bitVecMajority (a h block 37) (a h block 36) (a h block 35)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e38 (h : BitVecState) (block : Array Bool) :
    e h block 38 = (a h block 34) + ((e h block 34) + ((e h block 37).rotateLeft 50 ^^^ (e h block 37).rotateLeft 46 ^^^ (e h block 37).rotateLeft 23) + (((e h block 37) &&& (e h block 36)) + (~~~(e h block 37) &&& (e h block 35))) + (SHA512.roundConstants[37]!).toBitVec + (word block 37)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 37).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 34) + ((e h block 34) + bitVecBigSigma1 (e h block 37) + bitVecChoice (e h block 37) (e h block 36) (e h block 35) + (SHA512.roundConstants[37]!).toBitVec + (word block 37)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a39 (h : BitVecState) (block : Array Bool) :
    a h block 39 = ((e h block 35) + ((e h block 38).rotateLeft 50 ^^^ (e h block 38).rotateLeft 46 ^^^ (e h block 38).rotateLeft 23) + (((e h block 38) &&& (e h block 37)) + (~~~(e h block 38) &&& (e h block 36))) + (SHA512.roundConstants[38]!).toBitVec + (word block 38)) + (((a h block 38).rotateLeft 36 ^^^ (a h block 38).rotateLeft 30 ^^^ (a h block 38).rotateLeft 25) + ((((a h block 37) ^^^ (a h block 36)) &&& (a h block 38)) ^^^ ((a h block 37) &&& (a h block 36)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 38).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 35) + bitVecBigSigma1 (e h block 38) + bitVecChoice (e h block 38) (e h block 37) (e h block 36) + (SHA512.roundConstants[38]!).toBitVec + (word block 38)) + (bitVecBigSigma0 (a h block 38) + bitVecMajority (a h block 38) (a h block 37) (a h block 36)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e39 (h : BitVecState) (block : Array Bool) :
    e h block 39 = (a h block 35) + ((e h block 35) + ((e h block 38).rotateLeft 50 ^^^ (e h block 38).rotateLeft 46 ^^^ (e h block 38).rotateLeft 23) + (((e h block 38) &&& (e h block 37)) + (~~~(e h block 38) &&& (e h block 36))) + (SHA512.roundConstants[38]!).toBitVec + (word block 38)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 38).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 35) + ((e h block 35) + bitVecBigSigma1 (e h block 38) + bitVecChoice (e h block 38) (e h block 37) (e h block 36) + (SHA512.roundConstants[38]!).toBitVec + (word block 38)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a40 (h : BitVecState) (block : Array Bool) :
    a h block 40 = ((e h block 36) + ((e h block 39).rotateLeft 50 ^^^ (e h block 39).rotateLeft 46 ^^^ (e h block 39).rotateLeft 23) + (((e h block 39) &&& (e h block 38)) + (~~~(e h block 39) &&& (e h block 37))) + (SHA512.roundConstants[39]!).toBitVec + (word block 39)) + (((a h block 39).rotateLeft 36 ^^^ (a h block 39).rotateLeft 30 ^^^ (a h block 39).rotateLeft 25) + ((((a h block 38) ^^^ (a h block 37)) &&& (a h block 39)) ^^^ ((a h block 38) &&& (a h block 37)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 39).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 36) + bitVecBigSigma1 (e h block 39) + bitVecChoice (e h block 39) (e h block 38) (e h block 37) + (SHA512.roundConstants[39]!).toBitVec + (word block 39)) + (bitVecBigSigma0 (a h block 39) + bitVecMajority (a h block 39) (a h block 38) (a h block 37)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e40 (h : BitVecState) (block : Array Bool) :
    e h block 40 = (a h block 36) + ((e h block 36) + ((e h block 39).rotateLeft 50 ^^^ (e h block 39).rotateLeft 46 ^^^ (e h block 39).rotateLeft 23) + (((e h block 39) &&& (e h block 38)) + (~~~(e h block 39) &&& (e h block 37))) + (SHA512.roundConstants[39]!).toBitVec + (word block 39)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 39).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 36) + ((e h block 36) + bitVecBigSigma1 (e h block 39) + bitVecChoice (e h block 39) (e h block 38) (e h block 37) + (SHA512.roundConstants[39]!).toBitVec + (word block 39)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a41 (h : BitVecState) (block : Array Bool) :
    a h block 41 = ((e h block 37) + ((e h block 40).rotateLeft 50 ^^^ (e h block 40).rotateLeft 46 ^^^ (e h block 40).rotateLeft 23) + (((e h block 40) &&& (e h block 39)) + (~~~(e h block 40) &&& (e h block 38))) + (SHA512.roundConstants[40]!).toBitVec + (word block 40)) + (((a h block 40).rotateLeft 36 ^^^ (a h block 40).rotateLeft 30 ^^^ (a h block 40).rotateLeft 25) + ((((a h block 39) ^^^ (a h block 38)) &&& (a h block 40)) ^^^ ((a h block 39) &&& (a h block 38)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 40).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 37) + bitVecBigSigma1 (e h block 40) + bitVecChoice (e h block 40) (e h block 39) (e h block 38) + (SHA512.roundConstants[40]!).toBitVec + (word block 40)) + (bitVecBigSigma0 (a h block 40) + bitVecMajority (a h block 40) (a h block 39) (a h block 38)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e41 (h : BitVecState) (block : Array Bool) :
    e h block 41 = (a h block 37) + ((e h block 37) + ((e h block 40).rotateLeft 50 ^^^ (e h block 40).rotateLeft 46 ^^^ (e h block 40).rotateLeft 23) + (((e h block 40) &&& (e h block 39)) + (~~~(e h block 40) &&& (e h block 38))) + (SHA512.roundConstants[40]!).toBitVec + (word block 40)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 40).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 37) + ((e h block 37) + bitVecBigSigma1 (e h block 40) + bitVecChoice (e h block 40) (e h block 39) (e h block 38) + (SHA512.roundConstants[40]!).toBitVec + (word block 40)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a42 (h : BitVecState) (block : Array Bool) :
    a h block 42 = ((e h block 38) + ((e h block 41).rotateLeft 50 ^^^ (e h block 41).rotateLeft 46 ^^^ (e h block 41).rotateLeft 23) + (((e h block 41) &&& (e h block 40)) + (~~~(e h block 41) &&& (e h block 39))) + (SHA512.roundConstants[41]!).toBitVec + (word block 41)) + (((a h block 41).rotateLeft 36 ^^^ (a h block 41).rotateLeft 30 ^^^ (a h block 41).rotateLeft 25) + ((((a h block 40) ^^^ (a h block 39)) &&& (a h block 41)) ^^^ ((a h block 40) &&& (a h block 39)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 41).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 38) + bitVecBigSigma1 (e h block 41) + bitVecChoice (e h block 41) (e h block 40) (e h block 39) + (SHA512.roundConstants[41]!).toBitVec + (word block 41)) + (bitVecBigSigma0 (a h block 41) + bitVecMajority (a h block 41) (a h block 40) (a h block 39)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e42 (h : BitVecState) (block : Array Bool) :
    e h block 42 = (a h block 38) + ((e h block 38) + ((e h block 41).rotateLeft 50 ^^^ (e h block 41).rotateLeft 46 ^^^ (e h block 41).rotateLeft 23) + (((e h block 41) &&& (e h block 40)) + (~~~(e h block 41) &&& (e h block 39))) + (SHA512.roundConstants[41]!).toBitVec + (word block 41)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 41).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 38) + ((e h block 38) + bitVecBigSigma1 (e h block 41) + bitVecChoice (e h block 41) (e h block 40) (e h block 39) + (SHA512.roundConstants[41]!).toBitVec + (word block 41)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a43 (h : BitVecState) (block : Array Bool) :
    a h block 43 = ((e h block 39) + ((e h block 42).rotateLeft 50 ^^^ (e h block 42).rotateLeft 46 ^^^ (e h block 42).rotateLeft 23) + (((e h block 42) &&& (e h block 41)) + (~~~(e h block 42) &&& (e h block 40))) + (SHA512.roundConstants[42]!).toBitVec + (word block 42)) + (((a h block 42).rotateLeft 36 ^^^ (a h block 42).rotateLeft 30 ^^^ (a h block 42).rotateLeft 25) + ((((a h block 41) ^^^ (a h block 40)) &&& (a h block 42)) ^^^ ((a h block 41) &&& (a h block 40)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 42).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 39) + bitVecBigSigma1 (e h block 42) + bitVecChoice (e h block 42) (e h block 41) (e h block 40) + (SHA512.roundConstants[42]!).toBitVec + (word block 42)) + (bitVecBigSigma0 (a h block 42) + bitVecMajority (a h block 42) (a h block 41) (a h block 40)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e43 (h : BitVecState) (block : Array Bool) :
    e h block 43 = (a h block 39) + ((e h block 39) + ((e h block 42).rotateLeft 50 ^^^ (e h block 42).rotateLeft 46 ^^^ (e h block 42).rotateLeft 23) + (((e h block 42) &&& (e h block 41)) + (~~~(e h block 42) &&& (e h block 40))) + (SHA512.roundConstants[42]!).toBitVec + (word block 42)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 42).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 39) + ((e h block 39) + bitVecBigSigma1 (e h block 42) + bitVecChoice (e h block 42) (e h block 41) (e h block 40) + (SHA512.roundConstants[42]!).toBitVec + (word block 42)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a44 (h : BitVecState) (block : Array Bool) :
    a h block 44 = ((e h block 40) + ((e h block 43).rotateLeft 50 ^^^ (e h block 43).rotateLeft 46 ^^^ (e h block 43).rotateLeft 23) + (((e h block 43) &&& (e h block 42)) + (~~~(e h block 43) &&& (e h block 41))) + (SHA512.roundConstants[43]!).toBitVec + (word block 43)) + (((a h block 43).rotateLeft 36 ^^^ (a h block 43).rotateLeft 30 ^^^ (a h block 43).rotateLeft 25) + ((((a h block 42) ^^^ (a h block 41)) &&& (a h block 43)) ^^^ ((a h block 42) &&& (a h block 41)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 43).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 40) + bitVecBigSigma1 (e h block 43) + bitVecChoice (e h block 43) (e h block 42) (e h block 41) + (SHA512.roundConstants[43]!).toBitVec + (word block 43)) + (bitVecBigSigma0 (a h block 43) + bitVecMajority (a h block 43) (a h block 42) (a h block 41)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e44 (h : BitVecState) (block : Array Bool) :
    e h block 44 = (a h block 40) + ((e h block 40) + ((e h block 43).rotateLeft 50 ^^^ (e h block 43).rotateLeft 46 ^^^ (e h block 43).rotateLeft 23) + (((e h block 43) &&& (e h block 42)) + (~~~(e h block 43) &&& (e h block 41))) + (SHA512.roundConstants[43]!).toBitVec + (word block 43)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 43).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 40) + ((e h block 40) + bitVecBigSigma1 (e h block 43) + bitVecChoice (e h block 43) (e h block 42) (e h block 41) + (SHA512.roundConstants[43]!).toBitVec + (word block 43)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a45 (h : BitVecState) (block : Array Bool) :
    a h block 45 = ((e h block 41) + ((e h block 44).rotateLeft 50 ^^^ (e h block 44).rotateLeft 46 ^^^ (e h block 44).rotateLeft 23) + (((e h block 44) &&& (e h block 43)) + (~~~(e h block 44) &&& (e h block 42))) + (SHA512.roundConstants[44]!).toBitVec + (word block 44)) + (((a h block 44).rotateLeft 36 ^^^ (a h block 44).rotateLeft 30 ^^^ (a h block 44).rotateLeft 25) + ((((a h block 43) ^^^ (a h block 42)) &&& (a h block 44)) ^^^ ((a h block 43) &&& (a h block 42)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 44).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 41) + bitVecBigSigma1 (e h block 44) + bitVecChoice (e h block 44) (e h block 43) (e h block 42) + (SHA512.roundConstants[44]!).toBitVec + (word block 44)) + (bitVecBigSigma0 (a h block 44) + bitVecMajority (a h block 44) (a h block 43) (a h block 42)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e45 (h : BitVecState) (block : Array Bool) :
    e h block 45 = (a h block 41) + ((e h block 41) + ((e h block 44).rotateLeft 50 ^^^ (e h block 44).rotateLeft 46 ^^^ (e h block 44).rotateLeft 23) + (((e h block 44) &&& (e h block 43)) + (~~~(e h block 44) &&& (e h block 42))) + (SHA512.roundConstants[44]!).toBitVec + (word block 44)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 44).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 41) + ((e h block 41) + bitVecBigSigma1 (e h block 44) + bitVecChoice (e h block 44) (e h block 43) (e h block 42) + (SHA512.roundConstants[44]!).toBitVec + (word block 44)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a46 (h : BitVecState) (block : Array Bool) :
    a h block 46 = ((e h block 42) + ((e h block 45).rotateLeft 50 ^^^ (e h block 45).rotateLeft 46 ^^^ (e h block 45).rotateLeft 23) + (((e h block 45) &&& (e h block 44)) + (~~~(e h block 45) &&& (e h block 43))) + (SHA512.roundConstants[45]!).toBitVec + (word block 45)) + (((a h block 45).rotateLeft 36 ^^^ (a h block 45).rotateLeft 30 ^^^ (a h block 45).rotateLeft 25) + ((((a h block 44) ^^^ (a h block 43)) &&& (a h block 45)) ^^^ ((a h block 44) &&& (a h block 43)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 45).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 42) + bitVecBigSigma1 (e h block 45) + bitVecChoice (e h block 45) (e h block 44) (e h block 43) + (SHA512.roundConstants[45]!).toBitVec + (word block 45)) + (bitVecBigSigma0 (a h block 45) + bitVecMajority (a h block 45) (a h block 44) (a h block 43)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e46 (h : BitVecState) (block : Array Bool) :
    e h block 46 = (a h block 42) + ((e h block 42) + ((e h block 45).rotateLeft 50 ^^^ (e h block 45).rotateLeft 46 ^^^ (e h block 45).rotateLeft 23) + (((e h block 45) &&& (e h block 44)) + (~~~(e h block 45) &&& (e h block 43))) + (SHA512.roundConstants[45]!).toBitVec + (word block 45)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 45).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 42) + ((e h block 42) + bitVecBigSigma1 (e h block 45) + bitVecChoice (e h block 45) (e h block 44) (e h block 43) + (SHA512.roundConstants[45]!).toBitVec + (word block 45)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a47 (h : BitVecState) (block : Array Bool) :
    a h block 47 = ((e h block 43) + ((e h block 46).rotateLeft 50 ^^^ (e h block 46).rotateLeft 46 ^^^ (e h block 46).rotateLeft 23) + (((e h block 46) &&& (e h block 45)) + (~~~(e h block 46) &&& (e h block 44))) + (SHA512.roundConstants[46]!).toBitVec + (word block 46)) + (((a h block 46).rotateLeft 36 ^^^ (a h block 46).rotateLeft 30 ^^^ (a h block 46).rotateLeft 25) + ((((a h block 45) ^^^ (a h block 44)) &&& (a h block 46)) ^^^ ((a h block 45) &&& (a h block 44)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 46).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 43) + bitVecBigSigma1 (e h block 46) + bitVecChoice (e h block 46) (e h block 45) (e h block 44) + (SHA512.roundConstants[46]!).toBitVec + (word block 46)) + (bitVecBigSigma0 (a h block 46) + bitVecMajority (a h block 46) (a h block 45) (a h block 44)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e47 (h : BitVecState) (block : Array Bool) :
    e h block 47 = (a h block 43) + ((e h block 43) + ((e h block 46).rotateLeft 50 ^^^ (e h block 46).rotateLeft 46 ^^^ (e h block 46).rotateLeft 23) + (((e h block 46) &&& (e h block 45)) + (~~~(e h block 46) &&& (e h block 44))) + (SHA512.roundConstants[46]!).toBitVec + (word block 46)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 46).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 43) + ((e h block 43) + bitVecBigSigma1 (e h block 46) + bitVecChoice (e h block 46) (e h block 45) (e h block 44) + (SHA512.roundConstants[46]!).toBitVec + (word block 46)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a48 (h : BitVecState) (block : Array Bool) :
    a h block 48 = ((e h block 44) + ((e h block 47).rotateLeft 50 ^^^ (e h block 47).rotateLeft 46 ^^^ (e h block 47).rotateLeft 23) + (((e h block 47) &&& (e h block 46)) + (~~~(e h block 47) &&& (e h block 45))) + (SHA512.roundConstants[47]!).toBitVec + (word block 47)) + (((a h block 47).rotateLeft 36 ^^^ (a h block 47).rotateLeft 30 ^^^ (a h block 47).rotateLeft 25) + ((((a h block 46) ^^^ (a h block 45)) &&& (a h block 47)) ^^^ ((a h block 46) &&& (a h block 45)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 47).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 44) + bitVecBigSigma1 (e h block 47) + bitVecChoice (e h block 47) (e h block 46) (e h block 45) + (SHA512.roundConstants[47]!).toBitVec + (word block 47)) + (bitVecBigSigma0 (a h block 47) + bitVecMajority (a h block 47) (a h block 46) (a h block 45)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e48 (h : BitVecState) (block : Array Bool) :
    e h block 48 = (a h block 44) + ((e h block 44) + ((e h block 47).rotateLeft 50 ^^^ (e h block 47).rotateLeft 46 ^^^ (e h block 47).rotateLeft 23) + (((e h block 47) &&& (e h block 46)) + (~~~(e h block 47) &&& (e h block 45))) + (SHA512.roundConstants[47]!).toBitVec + (word block 47)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 47).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 44) + ((e h block 44) + bitVecBigSigma1 (e h block 47) + bitVecChoice (e h block 47) (e h block 46) (e h block 45) + (SHA512.roundConstants[47]!).toBitVec + (word block 47)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a49 (h : BitVecState) (block : Array Bool) :
    a h block 49 = ((e h block 45) + ((e h block 48).rotateLeft 50 ^^^ (e h block 48).rotateLeft 46 ^^^ (e h block 48).rotateLeft 23) + (((e h block 48) &&& (e h block 47)) + (~~~(e h block 48) &&& (e h block 46))) + (SHA512.roundConstants[48]!).toBitVec + (word block 48)) + (((a h block 48).rotateLeft 36 ^^^ (a h block 48).rotateLeft 30 ^^^ (a h block 48).rotateLeft 25) + ((((a h block 47) ^^^ (a h block 46)) &&& (a h block 48)) ^^^ ((a h block 47) &&& (a h block 46)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 48).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 45) + bitVecBigSigma1 (e h block 48) + bitVecChoice (e h block 48) (e h block 47) (e h block 46) + (SHA512.roundConstants[48]!).toBitVec + (word block 48)) + (bitVecBigSigma0 (a h block 48) + bitVecMajority (a h block 48) (a h block 47) (a h block 46)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e49 (h : BitVecState) (block : Array Bool) :
    e h block 49 = (a h block 45) + ((e h block 45) + ((e h block 48).rotateLeft 50 ^^^ (e h block 48).rotateLeft 46 ^^^ (e h block 48).rotateLeft 23) + (((e h block 48) &&& (e h block 47)) + (~~~(e h block 48) &&& (e h block 46))) + (SHA512.roundConstants[48]!).toBitVec + (word block 48)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 48).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 45) + ((e h block 45) + bitVecBigSigma1 (e h block 48) + bitVecChoice (e h block 48) (e h block 47) (e h block 46) + (SHA512.roundConstants[48]!).toBitVec + (word block 48)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a50 (h : BitVecState) (block : Array Bool) :
    a h block 50 = ((e h block 46) + ((e h block 49).rotateLeft 50 ^^^ (e h block 49).rotateLeft 46 ^^^ (e h block 49).rotateLeft 23) + (((e h block 49) &&& (e h block 48)) + (~~~(e h block 49) &&& (e h block 47))) + (SHA512.roundConstants[49]!).toBitVec + (word block 49)) + (((a h block 49).rotateLeft 36 ^^^ (a h block 49).rotateLeft 30 ^^^ (a h block 49).rotateLeft 25) + ((((a h block 48) ^^^ (a h block 47)) &&& (a h block 49)) ^^^ ((a h block 48) &&& (a h block 47)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 49).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 46) + bitVecBigSigma1 (e h block 49) + bitVecChoice (e h block 49) (e h block 48) (e h block 47) + (SHA512.roundConstants[49]!).toBitVec + (word block 49)) + (bitVecBigSigma0 (a h block 49) + bitVecMajority (a h block 49) (a h block 48) (a h block 47)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e50 (h : BitVecState) (block : Array Bool) :
    e h block 50 = (a h block 46) + ((e h block 46) + ((e h block 49).rotateLeft 50 ^^^ (e h block 49).rotateLeft 46 ^^^ (e h block 49).rotateLeft 23) + (((e h block 49) &&& (e h block 48)) + (~~~(e h block 49) &&& (e h block 47))) + (SHA512.roundConstants[49]!).toBitVec + (word block 49)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 49).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 46) + ((e h block 46) + bitVecBigSigma1 (e h block 49) + bitVecChoice (e h block 49) (e h block 48) (e h block 47) + (SHA512.roundConstants[49]!).toBitVec + (word block 49)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a51 (h : BitVecState) (block : Array Bool) :
    a h block 51 = ((e h block 47) + ((e h block 50).rotateLeft 50 ^^^ (e h block 50).rotateLeft 46 ^^^ (e h block 50).rotateLeft 23) + (((e h block 50) &&& (e h block 49)) + (~~~(e h block 50) &&& (e h block 48))) + (SHA512.roundConstants[50]!).toBitVec + (word block 50)) + (((a h block 50).rotateLeft 36 ^^^ (a h block 50).rotateLeft 30 ^^^ (a h block 50).rotateLeft 25) + ((((a h block 49) ^^^ (a h block 48)) &&& (a h block 50)) ^^^ ((a h block 49) &&& (a h block 48)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 50).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 47) + bitVecBigSigma1 (e h block 50) + bitVecChoice (e h block 50) (e h block 49) (e h block 48) + (SHA512.roundConstants[50]!).toBitVec + (word block 50)) + (bitVecBigSigma0 (a h block 50) + bitVecMajority (a h block 50) (a h block 49) (a h block 48)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e51 (h : BitVecState) (block : Array Bool) :
    e h block 51 = (a h block 47) + ((e h block 47) + ((e h block 50).rotateLeft 50 ^^^ (e h block 50).rotateLeft 46 ^^^ (e h block 50).rotateLeft 23) + (((e h block 50) &&& (e h block 49)) + (~~~(e h block 50) &&& (e h block 48))) + (SHA512.roundConstants[50]!).toBitVec + (word block 50)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 50).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 47) + ((e h block 47) + bitVecBigSigma1 (e h block 50) + bitVecChoice (e h block 50) (e h block 49) (e h block 48) + (SHA512.roundConstants[50]!).toBitVec + (word block 50)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a52 (h : BitVecState) (block : Array Bool) :
    a h block 52 = ((e h block 48) + ((e h block 51).rotateLeft 50 ^^^ (e h block 51).rotateLeft 46 ^^^ (e h block 51).rotateLeft 23) + (((e h block 51) &&& (e h block 50)) + (~~~(e h block 51) &&& (e h block 49))) + (SHA512.roundConstants[51]!).toBitVec + (word block 51)) + (((a h block 51).rotateLeft 36 ^^^ (a h block 51).rotateLeft 30 ^^^ (a h block 51).rotateLeft 25) + ((((a h block 50) ^^^ (a h block 49)) &&& (a h block 51)) ^^^ ((a h block 50) &&& (a h block 49)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 51).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 48) + bitVecBigSigma1 (e h block 51) + bitVecChoice (e h block 51) (e h block 50) (e h block 49) + (SHA512.roundConstants[51]!).toBitVec + (word block 51)) + (bitVecBigSigma0 (a h block 51) + bitVecMajority (a h block 51) (a h block 50) (a h block 49)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e52 (h : BitVecState) (block : Array Bool) :
    e h block 52 = (a h block 48) + ((e h block 48) + ((e h block 51).rotateLeft 50 ^^^ (e h block 51).rotateLeft 46 ^^^ (e h block 51).rotateLeft 23) + (((e h block 51) &&& (e h block 50)) + (~~~(e h block 51) &&& (e h block 49))) + (SHA512.roundConstants[51]!).toBitVec + (word block 51)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 51).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 48) + ((e h block 48) + bitVecBigSigma1 (e h block 51) + bitVecChoice (e h block 51) (e h block 50) (e h block 49) + (SHA512.roundConstants[51]!).toBitVec + (word block 51)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a53 (h : BitVecState) (block : Array Bool) :
    a h block 53 = ((e h block 49) + ((e h block 52).rotateLeft 50 ^^^ (e h block 52).rotateLeft 46 ^^^ (e h block 52).rotateLeft 23) + (((e h block 52) &&& (e h block 51)) + (~~~(e h block 52) &&& (e h block 50))) + (SHA512.roundConstants[52]!).toBitVec + (word block 52)) + (((a h block 52).rotateLeft 36 ^^^ (a h block 52).rotateLeft 30 ^^^ (a h block 52).rotateLeft 25) + ((((a h block 51) ^^^ (a h block 50)) &&& (a h block 52)) ^^^ ((a h block 51) &&& (a h block 50)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 52).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 49) + bitVecBigSigma1 (e h block 52) + bitVecChoice (e h block 52) (e h block 51) (e h block 50) + (SHA512.roundConstants[52]!).toBitVec + (word block 52)) + (bitVecBigSigma0 (a h block 52) + bitVecMajority (a h block 52) (a h block 51) (a h block 50)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e53 (h : BitVecState) (block : Array Bool) :
    e h block 53 = (a h block 49) + ((e h block 49) + ((e h block 52).rotateLeft 50 ^^^ (e h block 52).rotateLeft 46 ^^^ (e h block 52).rotateLeft 23) + (((e h block 52) &&& (e h block 51)) + (~~~(e h block 52) &&& (e h block 50))) + (SHA512.roundConstants[52]!).toBitVec + (word block 52)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 52).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 49) + ((e h block 49) + bitVecBigSigma1 (e h block 52) + bitVecChoice (e h block 52) (e h block 51) (e h block 50) + (SHA512.roundConstants[52]!).toBitVec + (word block 52)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a54 (h : BitVecState) (block : Array Bool) :
    a h block 54 = ((e h block 50) + ((e h block 53).rotateLeft 50 ^^^ (e h block 53).rotateLeft 46 ^^^ (e h block 53).rotateLeft 23) + (((e h block 53) &&& (e h block 52)) + (~~~(e h block 53) &&& (e h block 51))) + (SHA512.roundConstants[53]!).toBitVec + (word block 53)) + (((a h block 53).rotateLeft 36 ^^^ (a h block 53).rotateLeft 30 ^^^ (a h block 53).rotateLeft 25) + ((((a h block 52) ^^^ (a h block 51)) &&& (a h block 53)) ^^^ ((a h block 52) &&& (a h block 51)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 53).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 50) + bitVecBigSigma1 (e h block 53) + bitVecChoice (e h block 53) (e h block 52) (e h block 51) + (SHA512.roundConstants[53]!).toBitVec + (word block 53)) + (bitVecBigSigma0 (a h block 53) + bitVecMajority (a h block 53) (a h block 52) (a h block 51)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e54 (h : BitVecState) (block : Array Bool) :
    e h block 54 = (a h block 50) + ((e h block 50) + ((e h block 53).rotateLeft 50 ^^^ (e h block 53).rotateLeft 46 ^^^ (e h block 53).rotateLeft 23) + (((e h block 53) &&& (e h block 52)) + (~~~(e h block 53) &&& (e h block 51))) + (SHA512.roundConstants[53]!).toBitVec + (word block 53)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 53).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 50) + ((e h block 50) + bitVecBigSigma1 (e h block 53) + bitVecChoice (e h block 53) (e h block 52) (e h block 51) + (SHA512.roundConstants[53]!).toBitVec + (word block 53)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a55 (h : BitVecState) (block : Array Bool) :
    a h block 55 = ((e h block 51) + ((e h block 54).rotateLeft 50 ^^^ (e h block 54).rotateLeft 46 ^^^ (e h block 54).rotateLeft 23) + (((e h block 54) &&& (e h block 53)) + (~~~(e h block 54) &&& (e h block 52))) + (SHA512.roundConstants[54]!).toBitVec + (word block 54)) + (((a h block 54).rotateLeft 36 ^^^ (a h block 54).rotateLeft 30 ^^^ (a h block 54).rotateLeft 25) + ((((a h block 53) ^^^ (a h block 52)) &&& (a h block 54)) ^^^ ((a h block 53) &&& (a h block 52)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 54).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 51) + bitVecBigSigma1 (e h block 54) + bitVecChoice (e h block 54) (e h block 53) (e h block 52) + (SHA512.roundConstants[54]!).toBitVec + (word block 54)) + (bitVecBigSigma0 (a h block 54) + bitVecMajority (a h block 54) (a h block 53) (a h block 52)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e55 (h : BitVecState) (block : Array Bool) :
    e h block 55 = (a h block 51) + ((e h block 51) + ((e h block 54).rotateLeft 50 ^^^ (e h block 54).rotateLeft 46 ^^^ (e h block 54).rotateLeft 23) + (((e h block 54) &&& (e h block 53)) + (~~~(e h block 54) &&& (e h block 52))) + (SHA512.roundConstants[54]!).toBitVec + (word block 54)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 54).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 51) + ((e h block 51) + bitVecBigSigma1 (e h block 54) + bitVecChoice (e h block 54) (e h block 53) (e h block 52) + (SHA512.roundConstants[54]!).toBitVec + (word block 54)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a56 (h : BitVecState) (block : Array Bool) :
    a h block 56 = ((e h block 52) + ((e h block 55).rotateLeft 50 ^^^ (e h block 55).rotateLeft 46 ^^^ (e h block 55).rotateLeft 23) + (((e h block 55) &&& (e h block 54)) + (~~~(e h block 55) &&& (e h block 53))) + (SHA512.roundConstants[55]!).toBitVec + (word block 55)) + (((a h block 55).rotateLeft 36 ^^^ (a h block 55).rotateLeft 30 ^^^ (a h block 55).rotateLeft 25) + ((((a h block 54) ^^^ (a h block 53)) &&& (a h block 55)) ^^^ ((a h block 54) &&& (a h block 53)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 55).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 52) + bitVecBigSigma1 (e h block 55) + bitVecChoice (e h block 55) (e h block 54) (e h block 53) + (SHA512.roundConstants[55]!).toBitVec + (word block 55)) + (bitVecBigSigma0 (a h block 55) + bitVecMajority (a h block 55) (a h block 54) (a h block 53)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e56 (h : BitVecState) (block : Array Bool) :
    e h block 56 = (a h block 52) + ((e h block 52) + ((e h block 55).rotateLeft 50 ^^^ (e h block 55).rotateLeft 46 ^^^ (e h block 55).rotateLeft 23) + (((e h block 55) &&& (e h block 54)) + (~~~(e h block 55) &&& (e h block 53))) + (SHA512.roundConstants[55]!).toBitVec + (word block 55)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 55).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 52) + ((e h block 52) + bitVecBigSigma1 (e h block 55) + bitVecChoice (e h block 55) (e h block 54) (e h block 53) + (SHA512.roundConstants[55]!).toBitVec + (word block 55)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a57 (h : BitVecState) (block : Array Bool) :
    a h block 57 = ((e h block 53) + ((e h block 56).rotateLeft 50 ^^^ (e h block 56).rotateLeft 46 ^^^ (e h block 56).rotateLeft 23) + (((e h block 56) &&& (e h block 55)) + (~~~(e h block 56) &&& (e h block 54))) + (SHA512.roundConstants[56]!).toBitVec + (word block 56)) + (((a h block 56).rotateLeft 36 ^^^ (a h block 56).rotateLeft 30 ^^^ (a h block 56).rotateLeft 25) + ((((a h block 55) ^^^ (a h block 54)) &&& (a h block 56)) ^^^ ((a h block 55) &&& (a h block 54)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 56).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 53) + bitVecBigSigma1 (e h block 56) + bitVecChoice (e h block 56) (e h block 55) (e h block 54) + (SHA512.roundConstants[56]!).toBitVec + (word block 56)) + (bitVecBigSigma0 (a h block 56) + bitVecMajority (a h block 56) (a h block 55) (a h block 54)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e57 (h : BitVecState) (block : Array Bool) :
    e h block 57 = (a h block 53) + ((e h block 53) + ((e h block 56).rotateLeft 50 ^^^ (e h block 56).rotateLeft 46 ^^^ (e h block 56).rotateLeft 23) + (((e h block 56) &&& (e h block 55)) + (~~~(e h block 56) &&& (e h block 54))) + (SHA512.roundConstants[56]!).toBitVec + (word block 56)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 56).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 53) + ((e h block 53) + bitVecBigSigma1 (e h block 56) + bitVecChoice (e h block 56) (e h block 55) (e h block 54) + (SHA512.roundConstants[56]!).toBitVec + (word block 56)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a58 (h : BitVecState) (block : Array Bool) :
    a h block 58 = ((e h block 54) + ((e h block 57).rotateLeft 50 ^^^ (e h block 57).rotateLeft 46 ^^^ (e h block 57).rotateLeft 23) + (((e h block 57) &&& (e h block 56)) + (~~~(e h block 57) &&& (e h block 55))) + (SHA512.roundConstants[57]!).toBitVec + (word block 57)) + (((a h block 57).rotateLeft 36 ^^^ (a h block 57).rotateLeft 30 ^^^ (a h block 57).rotateLeft 25) + ((((a h block 56) ^^^ (a h block 55)) &&& (a h block 57)) ^^^ ((a h block 56) &&& (a h block 55)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 57).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 54) + bitVecBigSigma1 (e h block 57) + bitVecChoice (e h block 57) (e h block 56) (e h block 55) + (SHA512.roundConstants[57]!).toBitVec + (word block 57)) + (bitVecBigSigma0 (a h block 57) + bitVecMajority (a h block 57) (a h block 56) (a h block 55)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e58 (h : BitVecState) (block : Array Bool) :
    e h block 58 = (a h block 54) + ((e h block 54) + ((e h block 57).rotateLeft 50 ^^^ (e h block 57).rotateLeft 46 ^^^ (e h block 57).rotateLeft 23) + (((e h block 57) &&& (e h block 56)) + (~~~(e h block 57) &&& (e h block 55))) + (SHA512.roundConstants[57]!).toBitVec + (word block 57)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 57).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 54) + ((e h block 54) + bitVecBigSigma1 (e h block 57) + bitVecChoice (e h block 57) (e h block 56) (e h block 55) + (SHA512.roundConstants[57]!).toBitVec + (word block 57)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a59 (h : BitVecState) (block : Array Bool) :
    a h block 59 = ((e h block 55) + ((e h block 58).rotateLeft 50 ^^^ (e h block 58).rotateLeft 46 ^^^ (e h block 58).rotateLeft 23) + (((e h block 58) &&& (e h block 57)) + (~~~(e h block 58) &&& (e h block 56))) + (SHA512.roundConstants[58]!).toBitVec + (word block 58)) + (((a h block 58).rotateLeft 36 ^^^ (a h block 58).rotateLeft 30 ^^^ (a h block 58).rotateLeft 25) + ((((a h block 57) ^^^ (a h block 56)) &&& (a h block 58)) ^^^ ((a h block 57) &&& (a h block 56)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 58).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 55) + bitVecBigSigma1 (e h block 58) + bitVecChoice (e h block 58) (e h block 57) (e h block 56) + (SHA512.roundConstants[58]!).toBitVec + (word block 58)) + (bitVecBigSigma0 (a h block 58) + bitVecMajority (a h block 58) (a h block 57) (a h block 56)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e59 (h : BitVecState) (block : Array Bool) :
    e h block 59 = (a h block 55) + ((e h block 55) + ((e h block 58).rotateLeft 50 ^^^ (e h block 58).rotateLeft 46 ^^^ (e h block 58).rotateLeft 23) + (((e h block 58) &&& (e h block 57)) + (~~~(e h block 58) &&& (e h block 56))) + (SHA512.roundConstants[58]!).toBitVec + (word block 58)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 58).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 55) + ((e h block 55) + bitVecBigSigma1 (e h block 58) + bitVecChoice (e h block 58) (e h block 57) (e h block 56) + (SHA512.roundConstants[58]!).toBitVec + (word block 58)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a60 (h : BitVecState) (block : Array Bool) :
    a h block 60 = ((e h block 56) + ((e h block 59).rotateLeft 50 ^^^ (e h block 59).rotateLeft 46 ^^^ (e h block 59).rotateLeft 23) + (((e h block 59) &&& (e h block 58)) + (~~~(e h block 59) &&& (e h block 57))) + (SHA512.roundConstants[59]!).toBitVec + (word block 59)) + (((a h block 59).rotateLeft 36 ^^^ (a h block 59).rotateLeft 30 ^^^ (a h block 59).rotateLeft 25) + ((((a h block 58) ^^^ (a h block 57)) &&& (a h block 59)) ^^^ ((a h block 58) &&& (a h block 57)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 59).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 56) + bitVecBigSigma1 (e h block 59) + bitVecChoice (e h block 59) (e h block 58) (e h block 57) + (SHA512.roundConstants[59]!).toBitVec + (word block 59)) + (bitVecBigSigma0 (a h block 59) + bitVecMajority (a h block 59) (a h block 58) (a h block 57)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e60 (h : BitVecState) (block : Array Bool) :
    e h block 60 = (a h block 56) + ((e h block 56) + ((e h block 59).rotateLeft 50 ^^^ (e h block 59).rotateLeft 46 ^^^ (e h block 59).rotateLeft 23) + (((e h block 59) &&& (e h block 58)) + (~~~(e h block 59) &&& (e h block 57))) + (SHA512.roundConstants[59]!).toBitVec + (word block 59)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 59).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 56) + ((e h block 56) + bitVecBigSigma1 (e h block 59) + bitVecChoice (e h block 59) (e h block 58) (e h block 57) + (SHA512.roundConstants[59]!).toBitVec + (word block 59)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a61 (h : BitVecState) (block : Array Bool) :
    a h block 61 = ((e h block 57) + ((e h block 60).rotateLeft 50 ^^^ (e h block 60).rotateLeft 46 ^^^ (e h block 60).rotateLeft 23) + (((e h block 60) &&& (e h block 59)) + (~~~(e h block 60) &&& (e h block 58))) + (SHA512.roundConstants[60]!).toBitVec + (word block 60)) + (((a h block 60).rotateLeft 36 ^^^ (a h block 60).rotateLeft 30 ^^^ (a h block 60).rotateLeft 25) + ((((a h block 59) ^^^ (a h block 58)) &&& (a h block 60)) ^^^ ((a h block 59) &&& (a h block 58)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 60).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 57) + bitVecBigSigma1 (e h block 60) + bitVecChoice (e h block 60) (e h block 59) (e h block 58) + (SHA512.roundConstants[60]!).toBitVec + (word block 60)) + (bitVecBigSigma0 (a h block 60) + bitVecMajority (a h block 60) (a h block 59) (a h block 58)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e61 (h : BitVecState) (block : Array Bool) :
    e h block 61 = (a h block 57) + ((e h block 57) + ((e h block 60).rotateLeft 50 ^^^ (e h block 60).rotateLeft 46 ^^^ (e h block 60).rotateLeft 23) + (((e h block 60) &&& (e h block 59)) + (~~~(e h block 60) &&& (e h block 58))) + (SHA512.roundConstants[60]!).toBitVec + (word block 60)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 60).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 57) + ((e h block 57) + bitVecBigSigma1 (e h block 60) + bitVecChoice (e h block 60) (e h block 59) (e h block 58) + (SHA512.roundConstants[60]!).toBitVec + (word block 60)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a62 (h : BitVecState) (block : Array Bool) :
    a h block 62 = ((e h block 58) + ((e h block 61).rotateLeft 50 ^^^ (e h block 61).rotateLeft 46 ^^^ (e h block 61).rotateLeft 23) + (((e h block 61) &&& (e h block 60)) + (~~~(e h block 61) &&& (e h block 59))) + (SHA512.roundConstants[61]!).toBitVec + (word block 61)) + (((a h block 61).rotateLeft 36 ^^^ (a h block 61).rotateLeft 30 ^^^ (a h block 61).rotateLeft 25) + ((((a h block 60) ^^^ (a h block 59)) &&& (a h block 61)) ^^^ ((a h block 60) &&& (a h block 59)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 61).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 58) + bitVecBigSigma1 (e h block 61) + bitVecChoice (e h block 61) (e h block 60) (e h block 59) + (SHA512.roundConstants[61]!).toBitVec + (word block 61)) + (bitVecBigSigma0 (a h block 61) + bitVecMajority (a h block 61) (a h block 60) (a h block 59)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e62 (h : BitVecState) (block : Array Bool) :
    e h block 62 = (a h block 58) + ((e h block 58) + ((e h block 61).rotateLeft 50 ^^^ (e h block 61).rotateLeft 46 ^^^ (e h block 61).rotateLeft 23) + (((e h block 61) &&& (e h block 60)) + (~~~(e h block 61) &&& (e h block 59))) + (SHA512.roundConstants[61]!).toBitVec + (word block 61)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 61).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 58) + ((e h block 58) + bitVecBigSigma1 (e h block 61) + bitVecChoice (e h block 61) (e h block 60) (e h block 59) + (SHA512.roundConstants[61]!).toBitVec + (word block 61)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a63 (h : BitVecState) (block : Array Bool) :
    a h block 63 = ((e h block 59) + ((e h block 62).rotateLeft 50 ^^^ (e h block 62).rotateLeft 46 ^^^ (e h block 62).rotateLeft 23) + (((e h block 62) &&& (e h block 61)) + (~~~(e h block 62) &&& (e h block 60))) + (SHA512.roundConstants[62]!).toBitVec + (word block 62)) + (((a h block 62).rotateLeft 36 ^^^ (a h block 62).rotateLeft 30 ^^^ (a h block 62).rotateLeft 25) + ((((a h block 61) ^^^ (a h block 60)) &&& (a h block 62)) ^^^ ((a h block 61) &&& (a h block 60)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 62).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 59) + bitVecBigSigma1 (e h block 62) + bitVecChoice (e h block 62) (e h block 61) (e h block 60) + (SHA512.roundConstants[62]!).toBitVec + (word block 62)) + (bitVecBigSigma0 (a h block 62) + bitVecMajority (a h block 62) (a h block 61) (a h block 60)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e63 (h : BitVecState) (block : Array Bool) :
    e h block 63 = (a h block 59) + ((e h block 59) + ((e h block 62).rotateLeft 50 ^^^ (e h block 62).rotateLeft 46 ^^^ (e h block 62).rotateLeft 23) + (((e h block 62) &&& (e h block 61)) + (~~~(e h block 62) &&& (e h block 60))) + (SHA512.roundConstants[62]!).toBitVec + (word block 62)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 62).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 59) + ((e h block 59) + bitVecBigSigma1 (e h block 62) + bitVecChoice (e h block 62) (e h block 61) (e h block 60) + (SHA512.roundConstants[62]!).toBitVec + (word block 62)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a64 (h : BitVecState) (block : Array Bool) :
    a h block 64 = ((e h block 60) + ((e h block 63).rotateLeft 50 ^^^ (e h block 63).rotateLeft 46 ^^^ (e h block 63).rotateLeft 23) + (((e h block 63) &&& (e h block 62)) + (~~~(e h block 63) &&& (e h block 61))) + (SHA512.roundConstants[63]!).toBitVec + (word block 63)) + (((a h block 63).rotateLeft 36 ^^^ (a h block 63).rotateLeft 30 ^^^ (a h block 63).rotateLeft 25) + ((((a h block 62) ^^^ (a h block 61)) &&& (a h block 63)) ^^^ ((a h block 62) &&& (a h block 61)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 63).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 60) + bitVecBigSigma1 (e h block 63) + bitVecChoice (e h block 63) (e h block 62) (e h block 61) + (SHA512.roundConstants[63]!).toBitVec + (word block 63)) + (bitVecBigSigma0 (a h block 63) + bitVecMajority (a h block 63) (a h block 62) (a h block 61)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e64 (h : BitVecState) (block : Array Bool) :
    e h block 64 = (a h block 60) + ((e h block 60) + ((e h block 63).rotateLeft 50 ^^^ (e h block 63).rotateLeft 46 ^^^ (e h block 63).rotateLeft 23) + (((e h block 63) &&& (e h block 62)) + (~~~(e h block 63) &&& (e h block 61))) + (SHA512.roundConstants[63]!).toBitVec + (word block 63)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 63).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 60) + ((e h block 60) + bitVecBigSigma1 (e h block 63) + bitVecChoice (e h block 63) (e h block 62) (e h block 61) + (SHA512.roundConstants[63]!).toBitVec + (word block 63)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a65 (h : BitVecState) (block : Array Bool) :
    a h block 65 = ((e h block 61) + ((e h block 64).rotateLeft 50 ^^^ (e h block 64).rotateLeft 46 ^^^ (e h block 64).rotateLeft 23) + (((e h block 64) &&& (e h block 63)) + (~~~(e h block 64) &&& (e h block 62))) + (SHA512.roundConstants[64]!).toBitVec + (word block 64)) + (((a h block 64).rotateLeft 36 ^^^ (a h block 64).rotateLeft 30 ^^^ (a h block 64).rotateLeft 25) + ((((a h block 63) ^^^ (a h block 62)) &&& (a h block 64)) ^^^ ((a h block 63) &&& (a h block 62)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 64).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 61) + bitVecBigSigma1 (e h block 64) + bitVecChoice (e h block 64) (e h block 63) (e h block 62) + (SHA512.roundConstants[64]!).toBitVec + (word block 64)) + (bitVecBigSigma0 (a h block 64) + bitVecMajority (a h block 64) (a h block 63) (a h block 62)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e65 (h : BitVecState) (block : Array Bool) :
    e h block 65 = (a h block 61) + ((e h block 61) + ((e h block 64).rotateLeft 50 ^^^ (e h block 64).rotateLeft 46 ^^^ (e h block 64).rotateLeft 23) + (((e h block 64) &&& (e h block 63)) + (~~~(e h block 64) &&& (e h block 62))) + (SHA512.roundConstants[64]!).toBitVec + (word block 64)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 64).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 61) + ((e h block 61) + bitVecBigSigma1 (e h block 64) + bitVecChoice (e h block 64) (e h block 63) (e h block 62) + (SHA512.roundConstants[64]!).toBitVec + (word block 64)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a66 (h : BitVecState) (block : Array Bool) :
    a h block 66 = ((e h block 62) + ((e h block 65).rotateLeft 50 ^^^ (e h block 65).rotateLeft 46 ^^^ (e h block 65).rotateLeft 23) + (((e h block 65) &&& (e h block 64)) + (~~~(e h block 65) &&& (e h block 63))) + (SHA512.roundConstants[65]!).toBitVec + (word block 65)) + (((a h block 65).rotateLeft 36 ^^^ (a h block 65).rotateLeft 30 ^^^ (a h block 65).rotateLeft 25) + ((((a h block 64) ^^^ (a h block 63)) &&& (a h block 65)) ^^^ ((a h block 64) &&& (a h block 63)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 65).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 62) + bitVecBigSigma1 (e h block 65) + bitVecChoice (e h block 65) (e h block 64) (e h block 63) + (SHA512.roundConstants[65]!).toBitVec + (word block 65)) + (bitVecBigSigma0 (a h block 65) + bitVecMajority (a h block 65) (a h block 64) (a h block 63)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e66 (h : BitVecState) (block : Array Bool) :
    e h block 66 = (a h block 62) + ((e h block 62) + ((e h block 65).rotateLeft 50 ^^^ (e h block 65).rotateLeft 46 ^^^ (e h block 65).rotateLeft 23) + (((e h block 65) &&& (e h block 64)) + (~~~(e h block 65) &&& (e h block 63))) + (SHA512.roundConstants[65]!).toBitVec + (word block 65)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 65).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 62) + ((e h block 62) + bitVecBigSigma1 (e h block 65) + bitVecChoice (e h block 65) (e h block 64) (e h block 63) + (SHA512.roundConstants[65]!).toBitVec + (word block 65)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a67 (h : BitVecState) (block : Array Bool) :
    a h block 67 = ((e h block 63) + ((e h block 66).rotateLeft 50 ^^^ (e h block 66).rotateLeft 46 ^^^ (e h block 66).rotateLeft 23) + (((e h block 66) &&& (e h block 65)) + (~~~(e h block 66) &&& (e h block 64))) + (SHA512.roundConstants[66]!).toBitVec + (word block 66)) + (((a h block 66).rotateLeft 36 ^^^ (a h block 66).rotateLeft 30 ^^^ (a h block 66).rotateLeft 25) + ((((a h block 65) ^^^ (a h block 64)) &&& (a h block 66)) ^^^ ((a h block 65) &&& (a h block 64)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 66).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 63) + bitVecBigSigma1 (e h block 66) + bitVecChoice (e h block 66) (e h block 65) (e h block 64) + (SHA512.roundConstants[66]!).toBitVec + (word block 66)) + (bitVecBigSigma0 (a h block 66) + bitVecMajority (a h block 66) (a h block 65) (a h block 64)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e67 (h : BitVecState) (block : Array Bool) :
    e h block 67 = (a h block 63) + ((e h block 63) + ((e h block 66).rotateLeft 50 ^^^ (e h block 66).rotateLeft 46 ^^^ (e h block 66).rotateLeft 23) + (((e h block 66) &&& (e h block 65)) + (~~~(e h block 66) &&& (e h block 64))) + (SHA512.roundConstants[66]!).toBitVec + (word block 66)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 66).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 63) + ((e h block 63) + bitVecBigSigma1 (e h block 66) + bitVecChoice (e h block 66) (e h block 65) (e h block 64) + (SHA512.roundConstants[66]!).toBitVec + (word block 66)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a68 (h : BitVecState) (block : Array Bool) :
    a h block 68 = ((e h block 64) + ((e h block 67).rotateLeft 50 ^^^ (e h block 67).rotateLeft 46 ^^^ (e h block 67).rotateLeft 23) + (((e h block 67) &&& (e h block 66)) + (~~~(e h block 67) &&& (e h block 65))) + (SHA512.roundConstants[67]!).toBitVec + (word block 67)) + (((a h block 67).rotateLeft 36 ^^^ (a h block 67).rotateLeft 30 ^^^ (a h block 67).rotateLeft 25) + ((((a h block 66) ^^^ (a h block 65)) &&& (a h block 67)) ^^^ ((a h block 66) &&& (a h block 65)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 67).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 64) + bitVecBigSigma1 (e h block 67) + bitVecChoice (e h block 67) (e h block 66) (e h block 65) + (SHA512.roundConstants[67]!).toBitVec + (word block 67)) + (bitVecBigSigma0 (a h block 67) + bitVecMajority (a h block 67) (a h block 66) (a h block 65)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e68 (h : BitVecState) (block : Array Bool) :
    e h block 68 = (a h block 64) + ((e h block 64) + ((e h block 67).rotateLeft 50 ^^^ (e h block 67).rotateLeft 46 ^^^ (e h block 67).rotateLeft 23) + (((e h block 67) &&& (e h block 66)) + (~~~(e h block 67) &&& (e h block 65))) + (SHA512.roundConstants[67]!).toBitVec + (word block 67)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 67).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 64) + ((e h block 64) + bitVecBigSigma1 (e h block 67) + bitVecChoice (e h block 67) (e h block 66) (e h block 65) + (SHA512.roundConstants[67]!).toBitVec + (word block 67)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a69 (h : BitVecState) (block : Array Bool) :
    a h block 69 = ((e h block 65) + ((e h block 68).rotateLeft 50 ^^^ (e h block 68).rotateLeft 46 ^^^ (e h block 68).rotateLeft 23) + (((e h block 68) &&& (e h block 67)) + (~~~(e h block 68) &&& (e h block 66))) + (SHA512.roundConstants[68]!).toBitVec + (word block 68)) + (((a h block 68).rotateLeft 36 ^^^ (a h block 68).rotateLeft 30 ^^^ (a h block 68).rotateLeft 25) + ((((a h block 67) ^^^ (a h block 66)) &&& (a h block 68)) ^^^ ((a h block 67) &&& (a h block 66)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 68).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 65) + bitVecBigSigma1 (e h block 68) + bitVecChoice (e h block 68) (e h block 67) (e h block 66) + (SHA512.roundConstants[68]!).toBitVec + (word block 68)) + (bitVecBigSigma0 (a h block 68) + bitVecMajority (a h block 68) (a h block 67) (a h block 66)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e69 (h : BitVecState) (block : Array Bool) :
    e h block 69 = (a h block 65) + ((e h block 65) + ((e h block 68).rotateLeft 50 ^^^ (e h block 68).rotateLeft 46 ^^^ (e h block 68).rotateLeft 23) + (((e h block 68) &&& (e h block 67)) + (~~~(e h block 68) &&& (e h block 66))) + (SHA512.roundConstants[68]!).toBitVec + (word block 68)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 68).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 65) + ((e h block 65) + bitVecBigSigma1 (e h block 68) + bitVecChoice (e h block 68) (e h block 67) (e h block 66) + (SHA512.roundConstants[68]!).toBitVec + (word block 68)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a70 (h : BitVecState) (block : Array Bool) :
    a h block 70 = ((e h block 66) + ((e h block 69).rotateLeft 50 ^^^ (e h block 69).rotateLeft 46 ^^^ (e h block 69).rotateLeft 23) + (((e h block 69) &&& (e h block 68)) + (~~~(e h block 69) &&& (e h block 67))) + (SHA512.roundConstants[69]!).toBitVec + (word block 69)) + (((a h block 69).rotateLeft 36 ^^^ (a h block 69).rotateLeft 30 ^^^ (a h block 69).rotateLeft 25) + ((((a h block 68) ^^^ (a h block 67)) &&& (a h block 69)) ^^^ ((a h block 68) &&& (a h block 67)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 69).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 66) + bitVecBigSigma1 (e h block 69) + bitVecChoice (e h block 69) (e h block 68) (e h block 67) + (SHA512.roundConstants[69]!).toBitVec + (word block 69)) + (bitVecBigSigma0 (a h block 69) + bitVecMajority (a h block 69) (a h block 68) (a h block 67)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e70 (h : BitVecState) (block : Array Bool) :
    e h block 70 = (a h block 66) + ((e h block 66) + ((e h block 69).rotateLeft 50 ^^^ (e h block 69).rotateLeft 46 ^^^ (e h block 69).rotateLeft 23) + (((e h block 69) &&& (e h block 68)) + (~~~(e h block 69) &&& (e h block 67))) + (SHA512.roundConstants[69]!).toBitVec + (word block 69)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 69).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 66) + ((e h block 66) + bitVecBigSigma1 (e h block 69) + bitVecChoice (e h block 69) (e h block 68) (e h block 67) + (SHA512.roundConstants[69]!).toBitVec + (word block 69)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a71 (h : BitVecState) (block : Array Bool) :
    a h block 71 = ((e h block 67) + ((e h block 70).rotateLeft 50 ^^^ (e h block 70).rotateLeft 46 ^^^ (e h block 70).rotateLeft 23) + (((e h block 70) &&& (e h block 69)) + (~~~(e h block 70) &&& (e h block 68))) + (SHA512.roundConstants[70]!).toBitVec + (word block 70)) + (((a h block 70).rotateLeft 36 ^^^ (a h block 70).rotateLeft 30 ^^^ (a h block 70).rotateLeft 25) + ((((a h block 69) ^^^ (a h block 68)) &&& (a h block 70)) ^^^ ((a h block 69) &&& (a h block 68)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 70).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 67) + bitVecBigSigma1 (e h block 70) + bitVecChoice (e h block 70) (e h block 69) (e h block 68) + (SHA512.roundConstants[70]!).toBitVec + (word block 70)) + (bitVecBigSigma0 (a h block 70) + bitVecMajority (a h block 70) (a h block 69) (a h block 68)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e71 (h : BitVecState) (block : Array Bool) :
    e h block 71 = (a h block 67) + ((e h block 67) + ((e h block 70).rotateLeft 50 ^^^ (e h block 70).rotateLeft 46 ^^^ (e h block 70).rotateLeft 23) + (((e h block 70) &&& (e h block 69)) + (~~~(e h block 70) &&& (e h block 68))) + (SHA512.roundConstants[70]!).toBitVec + (word block 70)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 70).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 67) + ((e h block 67) + bitVecBigSigma1 (e h block 70) + bitVecChoice (e h block 70) (e h block 69) (e h block 68) + (SHA512.roundConstants[70]!).toBitVec + (word block 70)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a72 (h : BitVecState) (block : Array Bool) :
    a h block 72 = ((e h block 68) + ((e h block 71).rotateLeft 50 ^^^ (e h block 71).rotateLeft 46 ^^^ (e h block 71).rotateLeft 23) + (((e h block 71) &&& (e h block 70)) + (~~~(e h block 71) &&& (e h block 69))) + (SHA512.roundConstants[71]!).toBitVec + (word block 71)) + (((a h block 71).rotateLeft 36 ^^^ (a h block 71).rotateLeft 30 ^^^ (a h block 71).rotateLeft 25) + ((((a h block 70) ^^^ (a h block 69)) &&& (a h block 71)) ^^^ ((a h block 70) &&& (a h block 69)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 71).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 68) + bitVecBigSigma1 (e h block 71) + bitVecChoice (e h block 71) (e h block 70) (e h block 69) + (SHA512.roundConstants[71]!).toBitVec + (word block 71)) + (bitVecBigSigma0 (a h block 71) + bitVecMajority (a h block 71) (a h block 70) (a h block 69)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e72 (h : BitVecState) (block : Array Bool) :
    e h block 72 = (a h block 68) + ((e h block 68) + ((e h block 71).rotateLeft 50 ^^^ (e h block 71).rotateLeft 46 ^^^ (e h block 71).rotateLeft 23) + (((e h block 71) &&& (e h block 70)) + (~~~(e h block 71) &&& (e h block 69))) + (SHA512.roundConstants[71]!).toBitVec + (word block 71)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 71).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 68) + ((e h block 68) + bitVecBigSigma1 (e h block 71) + bitVecChoice (e h block 71) (e h block 70) (e h block 69) + (SHA512.roundConstants[71]!).toBitVec + (word block 71)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a73 (h : BitVecState) (block : Array Bool) :
    a h block 73 = ((e h block 69) + ((e h block 72).rotateLeft 50 ^^^ (e h block 72).rotateLeft 46 ^^^ (e h block 72).rotateLeft 23) + (((e h block 72) &&& (e h block 71)) + (~~~(e h block 72) &&& (e h block 70))) + (SHA512.roundConstants[72]!).toBitVec + (word block 72)) + (((a h block 72).rotateLeft 36 ^^^ (a h block 72).rotateLeft 30 ^^^ (a h block 72).rotateLeft 25) + ((((a h block 71) ^^^ (a h block 70)) &&& (a h block 72)) ^^^ ((a h block 71) &&& (a h block 70)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 72).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 69) + bitVecBigSigma1 (e h block 72) + bitVecChoice (e h block 72) (e h block 71) (e h block 70) + (SHA512.roundConstants[72]!).toBitVec + (word block 72)) + (bitVecBigSigma0 (a h block 72) + bitVecMajority (a h block 72) (a h block 71) (a h block 70)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e73 (h : BitVecState) (block : Array Bool) :
    e h block 73 = (a h block 69) + ((e h block 69) + ((e h block 72).rotateLeft 50 ^^^ (e h block 72).rotateLeft 46 ^^^ (e h block 72).rotateLeft 23) + (((e h block 72) &&& (e h block 71)) + (~~~(e h block 72) &&& (e h block 70))) + (SHA512.roundConstants[72]!).toBitVec + (word block 72)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 72).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 69) + ((e h block 69) + bitVecBigSigma1 (e h block 72) + bitVecChoice (e h block 72) (e h block 71) (e h block 70) + (SHA512.roundConstants[72]!).toBitVec + (word block 72)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a74 (h : BitVecState) (block : Array Bool) :
    a h block 74 = ((e h block 70) + ((e h block 73).rotateLeft 50 ^^^ (e h block 73).rotateLeft 46 ^^^ (e h block 73).rotateLeft 23) + (((e h block 73) &&& (e h block 72)) + (~~~(e h block 73) &&& (e h block 71))) + (SHA512.roundConstants[73]!).toBitVec + (word block 73)) + (((a h block 73).rotateLeft 36 ^^^ (a h block 73).rotateLeft 30 ^^^ (a h block 73).rotateLeft 25) + ((((a h block 72) ^^^ (a h block 71)) &&& (a h block 73)) ^^^ ((a h block 72) &&& (a h block 71)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 73).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 70) + bitVecBigSigma1 (e h block 73) + bitVecChoice (e h block 73) (e h block 72) (e h block 71) + (SHA512.roundConstants[73]!).toBitVec + (word block 73)) + (bitVecBigSigma0 (a h block 73) + bitVecMajority (a h block 73) (a h block 72) (a h block 71)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e74 (h : BitVecState) (block : Array Bool) :
    e h block 74 = (a h block 70) + ((e h block 70) + ((e h block 73).rotateLeft 50 ^^^ (e h block 73).rotateLeft 46 ^^^ (e h block 73).rotateLeft 23) + (((e h block 73) &&& (e h block 72)) + (~~~(e h block 73) &&& (e h block 71))) + (SHA512.roundConstants[73]!).toBitVec + (word block 73)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 73).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 70) + ((e h block 70) + bitVecBigSigma1 (e h block 73) + bitVecChoice (e h block 73) (e h block 72) (e h block 71) + (SHA512.roundConstants[73]!).toBitVec + (word block 73)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a75 (h : BitVecState) (block : Array Bool) :
    a h block 75 = ((e h block 71) + ((e h block 74).rotateLeft 50 ^^^ (e h block 74).rotateLeft 46 ^^^ (e h block 74).rotateLeft 23) + (((e h block 74) &&& (e h block 73)) + (~~~(e h block 74) &&& (e h block 72))) + (SHA512.roundConstants[74]!).toBitVec + (word block 74)) + (((a h block 74).rotateLeft 36 ^^^ (a h block 74).rotateLeft 30 ^^^ (a h block 74).rotateLeft 25) + ((((a h block 73) ^^^ (a h block 72)) &&& (a h block 74)) ^^^ ((a h block 73) &&& (a h block 72)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 74).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 71) + bitVecBigSigma1 (e h block 74) + bitVecChoice (e h block 74) (e h block 73) (e h block 72) + (SHA512.roundConstants[74]!).toBitVec + (word block 74)) + (bitVecBigSigma0 (a h block 74) + bitVecMajority (a h block 74) (a h block 73) (a h block 72)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e75 (h : BitVecState) (block : Array Bool) :
    e h block 75 = (a h block 71) + ((e h block 71) + ((e h block 74).rotateLeft 50 ^^^ (e h block 74).rotateLeft 46 ^^^ (e h block 74).rotateLeft 23) + (((e h block 74) &&& (e h block 73)) + (~~~(e h block 74) &&& (e h block 72))) + (SHA512.roundConstants[74]!).toBitVec + (word block 74)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 74).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 71) + ((e h block 71) + bitVecBigSigma1 (e h block 74) + bitVecChoice (e h block 74) (e h block 73) (e h block 72) + (SHA512.roundConstants[74]!).toBitVec + (word block 74)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a76 (h : BitVecState) (block : Array Bool) :
    a h block 76 = ((e h block 72) + ((e h block 75).rotateLeft 50 ^^^ (e h block 75).rotateLeft 46 ^^^ (e h block 75).rotateLeft 23) + (((e h block 75) &&& (e h block 74)) + (~~~(e h block 75) &&& (e h block 73))) + (SHA512.roundConstants[75]!).toBitVec + (word block 75)) + (((a h block 75).rotateLeft 36 ^^^ (a h block 75).rotateLeft 30 ^^^ (a h block 75).rotateLeft 25) + ((((a h block 74) ^^^ (a h block 73)) &&& (a h block 75)) ^^^ ((a h block 74) &&& (a h block 73)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 75).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 72) + bitVecBigSigma1 (e h block 75) + bitVecChoice (e h block 75) (e h block 74) (e h block 73) + (SHA512.roundConstants[75]!).toBitVec + (word block 75)) + (bitVecBigSigma0 (a h block 75) + bitVecMajority (a h block 75) (a h block 74) (a h block 73)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e76 (h : BitVecState) (block : Array Bool) :
    e h block 76 = (a h block 72) + ((e h block 72) + ((e h block 75).rotateLeft 50 ^^^ (e h block 75).rotateLeft 46 ^^^ (e h block 75).rotateLeft 23) + (((e h block 75) &&& (e h block 74)) + (~~~(e h block 75) &&& (e h block 73))) + (SHA512.roundConstants[75]!).toBitVec + (word block 75)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 75).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 72) + ((e h block 72) + bitVecBigSigma1 (e h block 75) + bitVecChoice (e h block 75) (e h block 74) (e h block 73) + (SHA512.roundConstants[75]!).toBitVec + (word block 75)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a77 (h : BitVecState) (block : Array Bool) :
    a h block 77 = ((e h block 73) + ((e h block 76).rotateLeft 50 ^^^ (e h block 76).rotateLeft 46 ^^^ (e h block 76).rotateLeft 23) + (((e h block 76) &&& (e h block 75)) + (~~~(e h block 76) &&& (e h block 74))) + (SHA512.roundConstants[76]!).toBitVec + (word block 76)) + (((a h block 76).rotateLeft 36 ^^^ (a h block 76).rotateLeft 30 ^^^ (a h block 76).rotateLeft 25) + ((((a h block 75) ^^^ (a h block 74)) &&& (a h block 76)) ^^^ ((a h block 75) &&& (a h block 74)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 76).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 73) + bitVecBigSigma1 (e h block 76) + bitVecChoice (e h block 76) (e h block 75) (e h block 74) + (SHA512.roundConstants[76]!).toBitVec + (word block 76)) + (bitVecBigSigma0 (a h block 76) + bitVecMajority (a h block 76) (a h block 75) (a h block 74)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e77 (h : BitVecState) (block : Array Bool) :
    e h block 77 = (a h block 73) + ((e h block 73) + ((e h block 76).rotateLeft 50 ^^^ (e h block 76).rotateLeft 46 ^^^ (e h block 76).rotateLeft 23) + (((e h block 76) &&& (e h block 75)) + (~~~(e h block 76) &&& (e h block 74))) + (SHA512.roundConstants[76]!).toBitVec + (word block 76)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 76).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 73) + ((e h block 73) + bitVecBigSigma1 (e h block 76) + bitVecChoice (e h block 76) (e h block 75) (e h block 74) + (SHA512.roundConstants[76]!).toBitVec + (word block 76)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a78 (h : BitVecState) (block : Array Bool) :
    a h block 78 = ((e h block 74) + ((e h block 77).rotateLeft 50 ^^^ (e h block 77).rotateLeft 46 ^^^ (e h block 77).rotateLeft 23) + (((e h block 77) &&& (e h block 76)) + (~~~(e h block 77) &&& (e h block 75))) + (SHA512.roundConstants[77]!).toBitVec + (word block 77)) + (((a h block 77).rotateLeft 36 ^^^ (a h block 77).rotateLeft 30 ^^^ (a h block 77).rotateLeft 25) + ((((a h block 76) ^^^ (a h block 75)) &&& (a h block 77)) ^^^ ((a h block 76) &&& (a h block 75)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 77).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 74) + bitVecBigSigma1 (e h block 77) + bitVecChoice (e h block 77) (e h block 76) (e h block 75) + (SHA512.roundConstants[77]!).toBitVec + (word block 77)) + (bitVecBigSigma0 (a h block 77) + bitVecMajority (a h block 77) (a h block 76) (a h block 75)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e78 (h : BitVecState) (block : Array Bool) :
    e h block 78 = (a h block 74) + ((e h block 74) + ((e h block 77).rotateLeft 50 ^^^ (e h block 77).rotateLeft 46 ^^^ (e h block 77).rotateLeft 23) + (((e h block 77) &&& (e h block 76)) + (~~~(e h block 77) &&& (e h block 75))) + (SHA512.roundConstants[77]!).toBitVec + (word block 77)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 77).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 74) + ((e h block 74) + bitVecBigSigma1 (e h block 77) + bitVecChoice (e h block 77) (e h block 76) (e h block 75) + (SHA512.roundConstants[77]!).toBitVec + (word block 77)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a79 (h : BitVecState) (block : Array Bool) :
    a h block 79 = ((e h block 75) + ((e h block 78).rotateLeft 50 ^^^ (e h block 78).rotateLeft 46 ^^^ (e h block 78).rotateLeft 23) + (((e h block 78) &&& (e h block 77)) + (~~~(e h block 78) &&& (e h block 76))) + (SHA512.roundConstants[78]!).toBitVec + (word block 78)) + (((a h block 78).rotateLeft 36 ^^^ (a h block 78).rotateLeft 30 ^^^ (a h block 78).rotateLeft 25) + ((((a h block 77) ^^^ (a h block 76)) &&& (a h block 78)) ^^^ ((a h block 77) &&& (a h block 76)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 78).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 75) + bitVecBigSigma1 (e h block 78) + bitVecChoice (e h block 78) (e h block 77) (e h block 76) + (SHA512.roundConstants[78]!).toBitVec + (word block 78)) + (bitVecBigSigma0 (a h block 78) + bitVecMajority (a h block 78) (a h block 77) (a h block 76)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e79 (h : BitVecState) (block : Array Bool) :
    e h block 79 = (a h block 75) + ((e h block 75) + ((e h block 78).rotateLeft 50 ^^^ (e h block 78).rotateLeft 46 ^^^ (e h block 78).rotateLeft 23) + (((e h block 78) &&& (e h block 77)) + (~~~(e h block 78) &&& (e h block 76))) + (SHA512.roundConstants[78]!).toBitVec + (word block 78)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 78).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 75) + ((e h block 75) + bitVecBigSigma1 (e h block 78) + bitVecChoice (e h block 78) (e h block 77) (e h block 76) + (SHA512.roundConstants[78]!).toBitVec + (word block 78)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem a80 (h : BitVecState) (block : Array Bool) :
    a h block 80 = ((e h block 76) + ((e h block 79).rotateLeft 50 ^^^ (e h block 79).rotateLeft 46 ^^^ (e h block 79).rotateLeft 23) + (((e h block 79) &&& (e h block 78)) + (~~~(e h block 79) &&& (e h block 77))) + (SHA512.roundConstants[79]!).toBitVec + (word block 79)) + (((a h block 79).rotateLeft 36 ^^^ (a h block 79).rotateLeft 30 ^^^ (a h block 79).rotateLeft 25) + ((((a h block 78) ^^^ (a h block 77)) &&& (a h block 79)) ^^^ ((a h block 78) &&& (a h block 77)))) := by
  refine (aWord_succ h ((schedule block).map UInt64.toBitVec) 79).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 76) + bitVecBigSigma1 (e h block 79) + bitVecChoice (e h block 79) (e h block 78) (e h block 77) + (SHA512.roundConstants[79]!).toBitVec + (word block 79)) + (bitVecBigSigma0 (a h block 79) + bitVecMajority (a h block 79) (a h block 78) (a h block 77)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]

theorem e80 (h : BitVecState) (block : Array Bool) :
    e h block 80 = (a h block 76) + ((e h block 76) + ((e h block 79).rotateLeft 50 ^^^ (e h block 79).rotateLeft 46 ^^^ (e h block 79).rotateLeft 23) + (((e h block 79) &&& (e h block 78)) + (~~~(e h block 79) &&& (e h block 77))) + (SHA512.roundConstants[79]!).toBitVec + (word block 79)) := by
  refine (eWord_succ h ((schedule block).map UInt64.toBitVec) 79).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 76) + ((e h block 76) + bitVecBigSigma1 (e h block 79) + bitVecChoice (e h block 79) (e h block 78) (e h block 77) + (SHA512.roundConstants[79]!).toBitVec + (word block 79)) = _
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]

theorem w16 (block : Array Bool) :
    word block 16 = (word block 0) + ((word block 1).rotateLeft 63 ^^^ (word block 1).rotateLeft 56 ^^^ ((word block 1) >>> 7)) + (word block 9) + ((word block 14).rotateLeft 45 ^^^ (word block 14).rotateLeft 3 ^^^ ((word block 14) >>> 6)) := by
  have hs := schedule_toBitVec_recurrence block 16 (by decide) (by decide)
  simpa only [word, map_toBitVec_getElem!, bitVecSmallSigma0, bitVecSmallSigma1, Nat.reduceSub] using hs

theorem w17 (block : Array Bool) :
    word block 17 = (word block 1) + ((word block 2).rotateLeft 63 ^^^ (word block 2).rotateLeft 56 ^^^ ((word block 2) >>> 7)) + (word block 10) + ((word block 15).rotateLeft 45 ^^^ (word block 15).rotateLeft 3 ^^^ ((word block 15) >>> 6)) := by
  have hs := schedule_toBitVec_recurrence block 17 (by decide) (by decide)
  simpa only [word, map_toBitVec_getElem!, bitVecSmallSigma0, bitVecSmallSigma1, Nat.reduceSub] using hs

theorem w18 (block : Array Bool) :
    word block 18 = (word block 2) + ((word block 3).rotateLeft 63 ^^^ (word block 3).rotateLeft 56 ^^^ ((word block 3) >>> 7)) + (word block 11) + ((word block 16).rotateLeft 45 ^^^ (word block 16).rotateLeft 3 ^^^ ((word block 16) >>> 6)) := by
  have hs := schedule_toBitVec_recurrence block 18 (by decide) (by decide)
  simpa only [word, map_toBitVec_getElem!, bitVecSmallSigma0, bitVecSmallSigma1, Nat.reduceSub] using hs

theorem w19 (block : Array Bool) :
    word block 19 = (word block 3) + ((word block 4).rotateLeft 63 ^^^ (word block 4).rotateLeft 56 ^^^ ((word block 4) >>> 7)) + (word block 12) + ((word block 17).rotateLeft 45 ^^^ (word block 17).rotateLeft 3 ^^^ ((word block 17) >>> 6)) := by
  have hs := schedule_toBitVec_recurrence block 19 (by decide) (by decide)
  simpa only [word, map_toBitVec_getElem!, bitVecSmallSigma0, bitVecSmallSigma1, Nat.reduceSub] using hs

theorem w20 (block : Array Bool) :
    word block 20 = (word block 4) + ((word block 5).rotateLeft 63 ^^^ (word block 5).rotateLeft 56 ^^^ ((word block 5) >>> 7)) + (word block 13) + ((word block 18).rotateLeft 45 ^^^ (word block 18).rotateLeft 3 ^^^ ((word block 18) >>> 6)) := by
  have hs := schedule_toBitVec_recurrence block 20 (by decide) (by decide)
  simpa only [word, map_toBitVec_getElem!, bitVecSmallSigma0, bitVecSmallSigma1, Nat.reduceSub] using hs

theorem w21 (block : Array Bool) :
    word block 21 = (word block 5) + ((word block 6).rotateLeft 63 ^^^ (word block 6).rotateLeft 56 ^^^ ((word block 6) >>> 7)) + (word block 14) + ((word block 19).rotateLeft 45 ^^^ (word block 19).rotateLeft 3 ^^^ ((word block 19) >>> 6)) := by
  have hs := schedule_toBitVec_recurrence block 21 (by decide) (by decide)
  simpa only [word, map_toBitVec_getElem!, bitVecSmallSigma0, bitVecSmallSigma1, Nat.reduceSub] using hs

theorem w22 (block : Array Bool) :
    word block 22 = (word block 6) + ((word block 7).rotateLeft 63 ^^^ (word block 7).rotateLeft 56 ^^^ ((word block 7) >>> 7)) + (word block 15) + ((word block 20).rotateLeft 45 ^^^ (word block 20).rotateLeft 3 ^^^ ((word block 20) >>> 6)) := by
  have hs := schedule_toBitVec_recurrence block 22 (by decide) (by decide)
  simpa only [word, map_toBitVec_getElem!, bitVecSmallSigma0, bitVecSmallSigma1, Nat.reduceSub] using hs

theorem w23 (block : Array Bool) :
    word block 23 = (word block 7) + ((word block 8).rotateLeft 63 ^^^ (word block 8).rotateLeft 56 ^^^ ((word block 8) >>> 7)) + (word block 16) + ((word block 21).rotateLeft 45 ^^^ (word block 21).rotateLeft 3 ^^^ ((word block 21) >>> 6)) := by
  have hs := schedule_toBitVec_recurrence block 23 (by decide) (by decide)
  simpa only [word, map_toBitVec_getElem!, bitVecSmallSigma0, bitVecSmallSigma1, Nat.reduceSub] using hs

theorem w24 (block : Array Bool) :
    word block 24 = (word block 8) + ((word block 9).rotateLeft 63 ^^^ (word block 9).rotateLeft 56 ^^^ ((word block 9) >>> 7)) + (word block 17) + ((word block 22).rotateLeft 45 ^^^ (word block 22).rotateLeft 3 ^^^ ((word block 22) >>> 6)) := by
  have hs := schedule_toBitVec_recurrence block 24 (by decide) (by decide)
  simpa only [word, map_toBitVec_getElem!, bitVecSmallSigma0, bitVecSmallSigma1, Nat.reduceSub] using hs

theorem w25 (block : Array Bool) :
    word block 25 = (word block 9) + ((word block 10).rotateLeft 63 ^^^ (word block 10).rotateLeft 56 ^^^ ((word block 10) >>> 7)) + (word block 18) + ((word block 23).rotateLeft 45 ^^^ (word block 23).rotateLeft 3 ^^^ ((word block 23) >>> 6)) := by
  have hs := schedule_toBitVec_recurrence block 25 (by decide) (by decide)
  simpa only [word, map_toBitVec_getElem!, bitVecSmallSigma0, bitVecSmallSigma1, Nat.reduceSub] using hs

theorem w26 (block : Array Bool) :
    word block 26 = (word block 10) + ((word block 11).rotateLeft 63 ^^^ (word block 11).rotateLeft 56 ^^^ ((word block 11) >>> 7)) + (word block 19) + ((word block 24).rotateLeft 45 ^^^ (word block 24).rotateLeft 3 ^^^ ((word block 24) >>> 6)) := by
  have hs := schedule_toBitVec_recurrence block 26 (by decide) (by decide)
  simpa only [word, map_toBitVec_getElem!, bitVecSmallSigma0, bitVecSmallSigma1, Nat.reduceSub] using hs

theorem w27 (block : Array Bool) :
    word block 27 = (word block 11) + ((word block 12).rotateLeft 63 ^^^ (word block 12).rotateLeft 56 ^^^ ((word block 12) >>> 7)) + (word block 20) + ((word block 25).rotateLeft 45 ^^^ (word block 25).rotateLeft 3 ^^^ ((word block 25) >>> 6)) := by
  have hs := schedule_toBitVec_recurrence block 27 (by decide) (by decide)
  simpa only [word, map_toBitVec_getElem!, bitVecSmallSigma0, bitVecSmallSigma1, Nat.reduceSub] using hs

theorem w28 (block : Array Bool) :
    word block 28 = (word block 12) + ((word block 13).rotateLeft 63 ^^^ (word block 13).rotateLeft 56 ^^^ ((word block 13) >>> 7)) + (word block 21) + ((word block 26).rotateLeft 45 ^^^ (word block 26).rotateLeft 3 ^^^ ((word block 26) >>> 6)) := by
  have hs := schedule_toBitVec_recurrence block 28 (by decide) (by decide)
  simpa only [word, map_toBitVec_getElem!, bitVecSmallSigma0, bitVecSmallSigma1, Nat.reduceSub] using hs

theorem w29 (block : Array Bool) :
    word block 29 = (word block 13) + ((word block 14).rotateLeft 63 ^^^ (word block 14).rotateLeft 56 ^^^ ((word block 14) >>> 7)) + (word block 22) + ((word block 27).rotateLeft 45 ^^^ (word block 27).rotateLeft 3 ^^^ ((word block 27) >>> 6)) := by
  have hs := schedule_toBitVec_recurrence block 29 (by decide) (by decide)
  simpa only [word, map_toBitVec_getElem!, bitVecSmallSigma0, bitVecSmallSigma1, Nat.reduceSub] using hs

theorem w30 (block : Array Bool) :
    word block 30 = (word block 14) + ((word block 15).rotateLeft 63 ^^^ (word block 15).rotateLeft 56 ^^^ ((word block 15) >>> 7)) + (word block 23) + ((word block 28).rotateLeft 45 ^^^ (word block 28).rotateLeft 3 ^^^ ((word block 28) >>> 6)) := by
  have hs := schedule_toBitVec_recurrence block 30 (by decide) (by decide)
  simpa only [word, map_toBitVec_getElem!, bitVecSmallSigma0, bitVecSmallSigma1, Nat.reduceSub] using hs

theorem w31 (block : Array Bool) :
    word block 31 = (word block 15) + ((word block 16).rotateLeft 63 ^^^ (word block 16).rotateLeft 56 ^^^ ((word block 16) >>> 7)) + (word block 24) + ((word block 29).rotateLeft 45 ^^^ (word block 29).rotateLeft 3 ^^^ ((word block 29) >>> 6)) := by
  have hs := schedule_toBitVec_recurrence block 31 (by decide) (by decide)
  simpa only [word, map_toBitVec_getElem!, bitVecSmallSigma0, bitVecSmallSigma1, Nat.reduceSub] using hs

theorem w32 (block : Array Bool) :
    word block 32 = (word block 16) + ((word block 17).rotateLeft 63 ^^^ (word block 17).rotateLeft 56 ^^^ ((word block 17) >>> 7)) + (word block 25) + ((word block 30).rotateLeft 45 ^^^ (word block 30).rotateLeft 3 ^^^ ((word block 30) >>> 6)) := by
  have hs := schedule_toBitVec_recurrence block 32 (by decide) (by decide)
  simpa only [word, map_toBitVec_getElem!, bitVecSmallSigma0, bitVecSmallSigma1, Nat.reduceSub] using hs

theorem w33 (block : Array Bool) :
    word block 33 = (word block 17) + ((word block 18).rotateLeft 63 ^^^ (word block 18).rotateLeft 56 ^^^ ((word block 18) >>> 7)) + (word block 26) + ((word block 31).rotateLeft 45 ^^^ (word block 31).rotateLeft 3 ^^^ ((word block 31) >>> 6)) := by
  have hs := schedule_toBitVec_recurrence block 33 (by decide) (by decide)
  simpa only [word, map_toBitVec_getElem!, bitVecSmallSigma0, bitVecSmallSigma1, Nat.reduceSub] using hs

theorem w34 (block : Array Bool) :
    word block 34 = (word block 18) + ((word block 19).rotateLeft 63 ^^^ (word block 19).rotateLeft 56 ^^^ ((word block 19) >>> 7)) + (word block 27) + ((word block 32).rotateLeft 45 ^^^ (word block 32).rotateLeft 3 ^^^ ((word block 32) >>> 6)) := by
  have hs := schedule_toBitVec_recurrence block 34 (by decide) (by decide)
  simpa only [word, map_toBitVec_getElem!, bitVecSmallSigma0, bitVecSmallSigma1, Nat.reduceSub] using hs

theorem w35 (block : Array Bool) :
    word block 35 = (word block 19) + ((word block 20).rotateLeft 63 ^^^ (word block 20).rotateLeft 56 ^^^ ((word block 20) >>> 7)) + (word block 28) + ((word block 33).rotateLeft 45 ^^^ (word block 33).rotateLeft 3 ^^^ ((word block 33) >>> 6)) := by
  have hs := schedule_toBitVec_recurrence block 35 (by decide) (by decide)
  simpa only [word, map_toBitVec_getElem!, bitVecSmallSigma0, bitVecSmallSigma1, Nat.reduceSub] using hs

theorem w36 (block : Array Bool) :
    word block 36 = (word block 20) + ((word block 21).rotateLeft 63 ^^^ (word block 21).rotateLeft 56 ^^^ ((word block 21) >>> 7)) + (word block 29) + ((word block 34).rotateLeft 45 ^^^ (word block 34).rotateLeft 3 ^^^ ((word block 34) >>> 6)) := by
  have hs := schedule_toBitVec_recurrence block 36 (by decide) (by decide)
  simpa only [word, map_toBitVec_getElem!, bitVecSmallSigma0, bitVecSmallSigma1, Nat.reduceSub] using hs

theorem w37 (block : Array Bool) :
    word block 37 = (word block 21) + ((word block 22).rotateLeft 63 ^^^ (word block 22).rotateLeft 56 ^^^ ((word block 22) >>> 7)) + (word block 30) + ((word block 35).rotateLeft 45 ^^^ (word block 35).rotateLeft 3 ^^^ ((word block 35) >>> 6)) := by
  have hs := schedule_toBitVec_recurrence block 37 (by decide) (by decide)
  simpa only [word, map_toBitVec_getElem!, bitVecSmallSigma0, bitVecSmallSigma1, Nat.reduceSub] using hs

theorem w38 (block : Array Bool) :
    word block 38 = (word block 22) + ((word block 23).rotateLeft 63 ^^^ (word block 23).rotateLeft 56 ^^^ ((word block 23) >>> 7)) + (word block 31) + ((word block 36).rotateLeft 45 ^^^ (word block 36).rotateLeft 3 ^^^ ((word block 36) >>> 6)) := by
  have hs := schedule_toBitVec_recurrence block 38 (by decide) (by decide)
  simpa only [word, map_toBitVec_getElem!, bitVecSmallSigma0, bitVecSmallSigma1, Nat.reduceSub] using hs

theorem w39 (block : Array Bool) :
    word block 39 = (word block 23) + ((word block 24).rotateLeft 63 ^^^ (word block 24).rotateLeft 56 ^^^ ((word block 24) >>> 7)) + (word block 32) + ((word block 37).rotateLeft 45 ^^^ (word block 37).rotateLeft 3 ^^^ ((word block 37) >>> 6)) := by
  have hs := schedule_toBitVec_recurrence block 39 (by decide) (by decide)
  simpa only [word, map_toBitVec_getElem!, bitVecSmallSigma0, bitVecSmallSigma1, Nat.reduceSub] using hs

theorem w40 (block : Array Bool) :
    word block 40 = (word block 24) + ((word block 25).rotateLeft 63 ^^^ (word block 25).rotateLeft 56 ^^^ ((word block 25) >>> 7)) + (word block 33) + ((word block 38).rotateLeft 45 ^^^ (word block 38).rotateLeft 3 ^^^ ((word block 38) >>> 6)) := by
  have hs := schedule_toBitVec_recurrence block 40 (by decide) (by decide)
  simpa only [word, map_toBitVec_getElem!, bitVecSmallSigma0, bitVecSmallSigma1, Nat.reduceSub] using hs

theorem w41 (block : Array Bool) :
    word block 41 = (word block 25) + ((word block 26).rotateLeft 63 ^^^ (word block 26).rotateLeft 56 ^^^ ((word block 26) >>> 7)) + (word block 34) + ((word block 39).rotateLeft 45 ^^^ (word block 39).rotateLeft 3 ^^^ ((word block 39) >>> 6)) := by
  have hs := schedule_toBitVec_recurrence block 41 (by decide) (by decide)
  simpa only [word, map_toBitVec_getElem!, bitVecSmallSigma0, bitVecSmallSigma1, Nat.reduceSub] using hs

theorem w42 (block : Array Bool) :
    word block 42 = (word block 26) + ((word block 27).rotateLeft 63 ^^^ (word block 27).rotateLeft 56 ^^^ ((word block 27) >>> 7)) + (word block 35) + ((word block 40).rotateLeft 45 ^^^ (word block 40).rotateLeft 3 ^^^ ((word block 40) >>> 6)) := by
  have hs := schedule_toBitVec_recurrence block 42 (by decide) (by decide)
  simpa only [word, map_toBitVec_getElem!, bitVecSmallSigma0, bitVecSmallSigma1, Nat.reduceSub] using hs

theorem w43 (block : Array Bool) :
    word block 43 = (word block 27) + ((word block 28).rotateLeft 63 ^^^ (word block 28).rotateLeft 56 ^^^ ((word block 28) >>> 7)) + (word block 36) + ((word block 41).rotateLeft 45 ^^^ (word block 41).rotateLeft 3 ^^^ ((word block 41) >>> 6)) := by
  have hs := schedule_toBitVec_recurrence block 43 (by decide) (by decide)
  simpa only [word, map_toBitVec_getElem!, bitVecSmallSigma0, bitVecSmallSigma1, Nat.reduceSub] using hs

theorem w44 (block : Array Bool) :
    word block 44 = (word block 28) + ((word block 29).rotateLeft 63 ^^^ (word block 29).rotateLeft 56 ^^^ ((word block 29) >>> 7)) + (word block 37) + ((word block 42).rotateLeft 45 ^^^ (word block 42).rotateLeft 3 ^^^ ((word block 42) >>> 6)) := by
  have hs := schedule_toBitVec_recurrence block 44 (by decide) (by decide)
  simpa only [word, map_toBitVec_getElem!, bitVecSmallSigma0, bitVecSmallSigma1, Nat.reduceSub] using hs

theorem w45 (block : Array Bool) :
    word block 45 = (word block 29) + ((word block 30).rotateLeft 63 ^^^ (word block 30).rotateLeft 56 ^^^ ((word block 30) >>> 7)) + (word block 38) + ((word block 43).rotateLeft 45 ^^^ (word block 43).rotateLeft 3 ^^^ ((word block 43) >>> 6)) := by
  have hs := schedule_toBitVec_recurrence block 45 (by decide) (by decide)
  simpa only [word, map_toBitVec_getElem!, bitVecSmallSigma0, bitVecSmallSigma1, Nat.reduceSub] using hs

theorem w46 (block : Array Bool) :
    word block 46 = (word block 30) + ((word block 31).rotateLeft 63 ^^^ (word block 31).rotateLeft 56 ^^^ ((word block 31) >>> 7)) + (word block 39) + ((word block 44).rotateLeft 45 ^^^ (word block 44).rotateLeft 3 ^^^ ((word block 44) >>> 6)) := by
  have hs := schedule_toBitVec_recurrence block 46 (by decide) (by decide)
  simpa only [word, map_toBitVec_getElem!, bitVecSmallSigma0, bitVecSmallSigma1, Nat.reduceSub] using hs

theorem w47 (block : Array Bool) :
    word block 47 = (word block 31) + ((word block 32).rotateLeft 63 ^^^ (word block 32).rotateLeft 56 ^^^ ((word block 32) >>> 7)) + (word block 40) + ((word block 45).rotateLeft 45 ^^^ (word block 45).rotateLeft 3 ^^^ ((word block 45) >>> 6)) := by
  have hs := schedule_toBitVec_recurrence block 47 (by decide) (by decide)
  simpa only [word, map_toBitVec_getElem!, bitVecSmallSigma0, bitVecSmallSigma1, Nat.reduceSub] using hs

theorem w48 (block : Array Bool) :
    word block 48 = (word block 32) + ((word block 33).rotateLeft 63 ^^^ (word block 33).rotateLeft 56 ^^^ ((word block 33) >>> 7)) + (word block 41) + ((word block 46).rotateLeft 45 ^^^ (word block 46).rotateLeft 3 ^^^ ((word block 46) >>> 6)) := by
  have hs := schedule_toBitVec_recurrence block 48 (by decide) (by decide)
  simpa only [word, map_toBitVec_getElem!, bitVecSmallSigma0, bitVecSmallSigma1, Nat.reduceSub] using hs

theorem w49 (block : Array Bool) :
    word block 49 = (word block 33) + ((word block 34).rotateLeft 63 ^^^ (word block 34).rotateLeft 56 ^^^ ((word block 34) >>> 7)) + (word block 42) + ((word block 47).rotateLeft 45 ^^^ (word block 47).rotateLeft 3 ^^^ ((word block 47) >>> 6)) := by
  have hs := schedule_toBitVec_recurrence block 49 (by decide) (by decide)
  simpa only [word, map_toBitVec_getElem!, bitVecSmallSigma0, bitVecSmallSigma1, Nat.reduceSub] using hs

theorem w50 (block : Array Bool) :
    word block 50 = (word block 34) + ((word block 35).rotateLeft 63 ^^^ (word block 35).rotateLeft 56 ^^^ ((word block 35) >>> 7)) + (word block 43) + ((word block 48).rotateLeft 45 ^^^ (word block 48).rotateLeft 3 ^^^ ((word block 48) >>> 6)) := by
  have hs := schedule_toBitVec_recurrence block 50 (by decide) (by decide)
  simpa only [word, map_toBitVec_getElem!, bitVecSmallSigma0, bitVecSmallSigma1, Nat.reduceSub] using hs

theorem w51 (block : Array Bool) :
    word block 51 = (word block 35) + ((word block 36).rotateLeft 63 ^^^ (word block 36).rotateLeft 56 ^^^ ((word block 36) >>> 7)) + (word block 44) + ((word block 49).rotateLeft 45 ^^^ (word block 49).rotateLeft 3 ^^^ ((word block 49) >>> 6)) := by
  have hs := schedule_toBitVec_recurrence block 51 (by decide) (by decide)
  simpa only [word, map_toBitVec_getElem!, bitVecSmallSigma0, bitVecSmallSigma1, Nat.reduceSub] using hs

theorem w52 (block : Array Bool) :
    word block 52 = (word block 36) + ((word block 37).rotateLeft 63 ^^^ (word block 37).rotateLeft 56 ^^^ ((word block 37) >>> 7)) + (word block 45) + ((word block 50).rotateLeft 45 ^^^ (word block 50).rotateLeft 3 ^^^ ((word block 50) >>> 6)) := by
  have hs := schedule_toBitVec_recurrence block 52 (by decide) (by decide)
  simpa only [word, map_toBitVec_getElem!, bitVecSmallSigma0, bitVecSmallSigma1, Nat.reduceSub] using hs

theorem w53 (block : Array Bool) :
    word block 53 = (word block 37) + ((word block 38).rotateLeft 63 ^^^ (word block 38).rotateLeft 56 ^^^ ((word block 38) >>> 7)) + (word block 46) + ((word block 51).rotateLeft 45 ^^^ (word block 51).rotateLeft 3 ^^^ ((word block 51) >>> 6)) := by
  have hs := schedule_toBitVec_recurrence block 53 (by decide) (by decide)
  simpa only [word, map_toBitVec_getElem!, bitVecSmallSigma0, bitVecSmallSigma1, Nat.reduceSub] using hs

theorem w54 (block : Array Bool) :
    word block 54 = (word block 38) + ((word block 39).rotateLeft 63 ^^^ (word block 39).rotateLeft 56 ^^^ ((word block 39) >>> 7)) + (word block 47) + ((word block 52).rotateLeft 45 ^^^ (word block 52).rotateLeft 3 ^^^ ((word block 52) >>> 6)) := by
  have hs := schedule_toBitVec_recurrence block 54 (by decide) (by decide)
  simpa only [word, map_toBitVec_getElem!, bitVecSmallSigma0, bitVecSmallSigma1, Nat.reduceSub] using hs

theorem w55 (block : Array Bool) :
    word block 55 = (word block 39) + ((word block 40).rotateLeft 63 ^^^ (word block 40).rotateLeft 56 ^^^ ((word block 40) >>> 7)) + (word block 48) + ((word block 53).rotateLeft 45 ^^^ (word block 53).rotateLeft 3 ^^^ ((word block 53) >>> 6)) := by
  have hs := schedule_toBitVec_recurrence block 55 (by decide) (by decide)
  simpa only [word, map_toBitVec_getElem!, bitVecSmallSigma0, bitVecSmallSigma1, Nat.reduceSub] using hs

theorem w56 (block : Array Bool) :
    word block 56 = (word block 40) + ((word block 41).rotateLeft 63 ^^^ (word block 41).rotateLeft 56 ^^^ ((word block 41) >>> 7)) + (word block 49) + ((word block 54).rotateLeft 45 ^^^ (word block 54).rotateLeft 3 ^^^ ((word block 54) >>> 6)) := by
  have hs := schedule_toBitVec_recurrence block 56 (by decide) (by decide)
  simpa only [word, map_toBitVec_getElem!, bitVecSmallSigma0, bitVecSmallSigma1, Nat.reduceSub] using hs

theorem w57 (block : Array Bool) :
    word block 57 = (word block 41) + ((word block 42).rotateLeft 63 ^^^ (word block 42).rotateLeft 56 ^^^ ((word block 42) >>> 7)) + (word block 50) + ((word block 55).rotateLeft 45 ^^^ (word block 55).rotateLeft 3 ^^^ ((word block 55) >>> 6)) := by
  have hs := schedule_toBitVec_recurrence block 57 (by decide) (by decide)
  simpa only [word, map_toBitVec_getElem!, bitVecSmallSigma0, bitVecSmallSigma1, Nat.reduceSub] using hs

theorem w58 (block : Array Bool) :
    word block 58 = (word block 42) + ((word block 43).rotateLeft 63 ^^^ (word block 43).rotateLeft 56 ^^^ ((word block 43) >>> 7)) + (word block 51) + ((word block 56).rotateLeft 45 ^^^ (word block 56).rotateLeft 3 ^^^ ((word block 56) >>> 6)) := by
  have hs := schedule_toBitVec_recurrence block 58 (by decide) (by decide)
  simpa only [word, map_toBitVec_getElem!, bitVecSmallSigma0, bitVecSmallSigma1, Nat.reduceSub] using hs

theorem w59 (block : Array Bool) :
    word block 59 = (word block 43) + ((word block 44).rotateLeft 63 ^^^ (word block 44).rotateLeft 56 ^^^ ((word block 44) >>> 7)) + (word block 52) + ((word block 57).rotateLeft 45 ^^^ (word block 57).rotateLeft 3 ^^^ ((word block 57) >>> 6)) := by
  have hs := schedule_toBitVec_recurrence block 59 (by decide) (by decide)
  simpa only [word, map_toBitVec_getElem!, bitVecSmallSigma0, bitVecSmallSigma1, Nat.reduceSub] using hs

theorem w60 (block : Array Bool) :
    word block 60 = (word block 44) + ((word block 45).rotateLeft 63 ^^^ (word block 45).rotateLeft 56 ^^^ ((word block 45) >>> 7)) + (word block 53) + ((word block 58).rotateLeft 45 ^^^ (word block 58).rotateLeft 3 ^^^ ((word block 58) >>> 6)) := by
  have hs := schedule_toBitVec_recurrence block 60 (by decide) (by decide)
  simpa only [word, map_toBitVec_getElem!, bitVecSmallSigma0, bitVecSmallSigma1, Nat.reduceSub] using hs

theorem w61 (block : Array Bool) :
    word block 61 = (word block 45) + ((word block 46).rotateLeft 63 ^^^ (word block 46).rotateLeft 56 ^^^ ((word block 46) >>> 7)) + (word block 54) + ((word block 59).rotateLeft 45 ^^^ (word block 59).rotateLeft 3 ^^^ ((word block 59) >>> 6)) := by
  have hs := schedule_toBitVec_recurrence block 61 (by decide) (by decide)
  simpa only [word, map_toBitVec_getElem!, bitVecSmallSigma0, bitVecSmallSigma1, Nat.reduceSub] using hs

theorem w62 (block : Array Bool) :
    word block 62 = (word block 46) + ((word block 47).rotateLeft 63 ^^^ (word block 47).rotateLeft 56 ^^^ ((word block 47) >>> 7)) + (word block 55) + ((word block 60).rotateLeft 45 ^^^ (word block 60).rotateLeft 3 ^^^ ((word block 60) >>> 6)) := by
  have hs := schedule_toBitVec_recurrence block 62 (by decide) (by decide)
  simpa only [word, map_toBitVec_getElem!, bitVecSmallSigma0, bitVecSmallSigma1, Nat.reduceSub] using hs

theorem w63 (block : Array Bool) :
    word block 63 = (word block 47) + ((word block 48).rotateLeft 63 ^^^ (word block 48).rotateLeft 56 ^^^ ((word block 48) >>> 7)) + (word block 56) + ((word block 61).rotateLeft 45 ^^^ (word block 61).rotateLeft 3 ^^^ ((word block 61) >>> 6)) := by
  have hs := schedule_toBitVec_recurrence block 63 (by decide) (by decide)
  simpa only [word, map_toBitVec_getElem!, bitVecSmallSigma0, bitVecSmallSigma1, Nat.reduceSub] using hs

theorem w64 (block : Array Bool) :
    word block 64 = (word block 48) + ((word block 49).rotateLeft 63 ^^^ (word block 49).rotateLeft 56 ^^^ ((word block 49) >>> 7)) + (word block 57) + ((word block 62).rotateLeft 45 ^^^ (word block 62).rotateLeft 3 ^^^ ((word block 62) >>> 6)) := by
  have hs := schedule_toBitVec_recurrence block 64 (by decide) (by decide)
  simpa only [word, map_toBitVec_getElem!, bitVecSmallSigma0, bitVecSmallSigma1, Nat.reduceSub] using hs

theorem w65 (block : Array Bool) :
    word block 65 = (word block 49) + ((word block 50).rotateLeft 63 ^^^ (word block 50).rotateLeft 56 ^^^ ((word block 50) >>> 7)) + (word block 58) + ((word block 63).rotateLeft 45 ^^^ (word block 63).rotateLeft 3 ^^^ ((word block 63) >>> 6)) := by
  have hs := schedule_toBitVec_recurrence block 65 (by decide) (by decide)
  simpa only [word, map_toBitVec_getElem!, bitVecSmallSigma0, bitVecSmallSigma1, Nat.reduceSub] using hs

theorem w66 (block : Array Bool) :
    word block 66 = (word block 50) + ((word block 51).rotateLeft 63 ^^^ (word block 51).rotateLeft 56 ^^^ ((word block 51) >>> 7)) + (word block 59) + ((word block 64).rotateLeft 45 ^^^ (word block 64).rotateLeft 3 ^^^ ((word block 64) >>> 6)) := by
  have hs := schedule_toBitVec_recurrence block 66 (by decide) (by decide)
  simpa only [word, map_toBitVec_getElem!, bitVecSmallSigma0, bitVecSmallSigma1, Nat.reduceSub] using hs

theorem w67 (block : Array Bool) :
    word block 67 = (word block 51) + ((word block 52).rotateLeft 63 ^^^ (word block 52).rotateLeft 56 ^^^ ((word block 52) >>> 7)) + (word block 60) + ((word block 65).rotateLeft 45 ^^^ (word block 65).rotateLeft 3 ^^^ ((word block 65) >>> 6)) := by
  have hs := schedule_toBitVec_recurrence block 67 (by decide) (by decide)
  simpa only [word, map_toBitVec_getElem!, bitVecSmallSigma0, bitVecSmallSigma1, Nat.reduceSub] using hs

theorem w68 (block : Array Bool) :
    word block 68 = (word block 52) + ((word block 53).rotateLeft 63 ^^^ (word block 53).rotateLeft 56 ^^^ ((word block 53) >>> 7)) + (word block 61) + ((word block 66).rotateLeft 45 ^^^ (word block 66).rotateLeft 3 ^^^ ((word block 66) >>> 6)) := by
  have hs := schedule_toBitVec_recurrence block 68 (by decide) (by decide)
  simpa only [word, map_toBitVec_getElem!, bitVecSmallSigma0, bitVecSmallSigma1, Nat.reduceSub] using hs

theorem w69 (block : Array Bool) :
    word block 69 = (word block 53) + ((word block 54).rotateLeft 63 ^^^ (word block 54).rotateLeft 56 ^^^ ((word block 54) >>> 7)) + (word block 62) + ((word block 67).rotateLeft 45 ^^^ (word block 67).rotateLeft 3 ^^^ ((word block 67) >>> 6)) := by
  have hs := schedule_toBitVec_recurrence block 69 (by decide) (by decide)
  simpa only [word, map_toBitVec_getElem!, bitVecSmallSigma0, bitVecSmallSigma1, Nat.reduceSub] using hs

theorem w70 (block : Array Bool) :
    word block 70 = (word block 54) + ((word block 55).rotateLeft 63 ^^^ (word block 55).rotateLeft 56 ^^^ ((word block 55) >>> 7)) + (word block 63) + ((word block 68).rotateLeft 45 ^^^ (word block 68).rotateLeft 3 ^^^ ((word block 68) >>> 6)) := by
  have hs := schedule_toBitVec_recurrence block 70 (by decide) (by decide)
  simpa only [word, map_toBitVec_getElem!, bitVecSmallSigma0, bitVecSmallSigma1, Nat.reduceSub] using hs

theorem w71 (block : Array Bool) :
    word block 71 = (word block 55) + ((word block 56).rotateLeft 63 ^^^ (word block 56).rotateLeft 56 ^^^ ((word block 56) >>> 7)) + (word block 64) + ((word block 69).rotateLeft 45 ^^^ (word block 69).rotateLeft 3 ^^^ ((word block 69) >>> 6)) := by
  have hs := schedule_toBitVec_recurrence block 71 (by decide) (by decide)
  simpa only [word, map_toBitVec_getElem!, bitVecSmallSigma0, bitVecSmallSigma1, Nat.reduceSub] using hs

theorem w72 (block : Array Bool) :
    word block 72 = (word block 56) + ((word block 57).rotateLeft 63 ^^^ (word block 57).rotateLeft 56 ^^^ ((word block 57) >>> 7)) + (word block 65) + ((word block 70).rotateLeft 45 ^^^ (word block 70).rotateLeft 3 ^^^ ((word block 70) >>> 6)) := by
  have hs := schedule_toBitVec_recurrence block 72 (by decide) (by decide)
  simpa only [word, map_toBitVec_getElem!, bitVecSmallSigma0, bitVecSmallSigma1, Nat.reduceSub] using hs

theorem w73 (block : Array Bool) :
    word block 73 = (word block 57) + ((word block 58).rotateLeft 63 ^^^ (word block 58).rotateLeft 56 ^^^ ((word block 58) >>> 7)) + (word block 66) + ((word block 71).rotateLeft 45 ^^^ (word block 71).rotateLeft 3 ^^^ ((word block 71) >>> 6)) := by
  have hs := schedule_toBitVec_recurrence block 73 (by decide) (by decide)
  simpa only [word, map_toBitVec_getElem!, bitVecSmallSigma0, bitVecSmallSigma1, Nat.reduceSub] using hs

theorem w74 (block : Array Bool) :
    word block 74 = (word block 58) + ((word block 59).rotateLeft 63 ^^^ (word block 59).rotateLeft 56 ^^^ ((word block 59) >>> 7)) + (word block 67) + ((word block 72).rotateLeft 45 ^^^ (word block 72).rotateLeft 3 ^^^ ((word block 72) >>> 6)) := by
  have hs := schedule_toBitVec_recurrence block 74 (by decide) (by decide)
  simpa only [word, map_toBitVec_getElem!, bitVecSmallSigma0, bitVecSmallSigma1, Nat.reduceSub] using hs

theorem w75 (block : Array Bool) :
    word block 75 = (word block 59) + ((word block 60).rotateLeft 63 ^^^ (word block 60).rotateLeft 56 ^^^ ((word block 60) >>> 7)) + (word block 68) + ((word block 73).rotateLeft 45 ^^^ (word block 73).rotateLeft 3 ^^^ ((word block 73) >>> 6)) := by
  have hs := schedule_toBitVec_recurrence block 75 (by decide) (by decide)
  simpa only [word, map_toBitVec_getElem!, bitVecSmallSigma0, bitVecSmallSigma1, Nat.reduceSub] using hs

theorem w76 (block : Array Bool) :
    word block 76 = (word block 60) + ((word block 61).rotateLeft 63 ^^^ (word block 61).rotateLeft 56 ^^^ ((word block 61) >>> 7)) + (word block 69) + ((word block 74).rotateLeft 45 ^^^ (word block 74).rotateLeft 3 ^^^ ((word block 74) >>> 6)) := by
  have hs := schedule_toBitVec_recurrence block 76 (by decide) (by decide)
  simpa only [word, map_toBitVec_getElem!, bitVecSmallSigma0, bitVecSmallSigma1, Nat.reduceSub] using hs

theorem w77 (block : Array Bool) :
    word block 77 = (word block 61) + ((word block 62).rotateLeft 63 ^^^ (word block 62).rotateLeft 56 ^^^ ((word block 62) >>> 7)) + (word block 70) + ((word block 75).rotateLeft 45 ^^^ (word block 75).rotateLeft 3 ^^^ ((word block 75) >>> 6)) := by
  have hs := schedule_toBitVec_recurrence block 77 (by decide) (by decide)
  simpa only [word, map_toBitVec_getElem!, bitVecSmallSigma0, bitVecSmallSigma1, Nat.reduceSub] using hs

theorem w78 (block : Array Bool) :
    word block 78 = (word block 62) + ((word block 63).rotateLeft 63 ^^^ (word block 63).rotateLeft 56 ^^^ ((word block 63) >>> 7)) + (word block 71) + ((word block 76).rotateLeft 45 ^^^ (word block 76).rotateLeft 3 ^^^ ((word block 76) >>> 6)) := by
  have hs := schedule_toBitVec_recurrence block 78 (by decide) (by decide)
  simpa only [word, map_toBitVec_getElem!, bitVecSmallSigma0, bitVecSmallSigma1, Nat.reduceSub] using hs

theorem w79 (block : Array Bool) :
    word block 79 = (word block 63) + ((word block 64).rotateLeft 63 ^^^ (word block 64).rotateLeft 56 ^^^ ((word block 64) >>> 7)) + (word block 72) + ((word block 77).rotateLeft 45 ^^^ (word block 77).rotateLeft 3 ^^^ ((word block 77) >>> 6)) := by
  have hs := schedule_toBitVec_recurrence block 79 (by decide) (by decide)
  simpa only [word, map_toBitVec_getElem!, bitVecSmallSigma0, bitVecSmallSigma1, Nat.reduceSub] using hs

end Sha2.Proofs.Common.SHA512.Compression.Values.Correctness
