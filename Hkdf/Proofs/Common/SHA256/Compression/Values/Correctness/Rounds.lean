import Hkdf.Proofs.Common.SHA256.Compression.Values.Correctness.Algebra

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Values.Correctness

open Hkdf.Proofs.NIST

theorem a01 (h : BitVecState) (block : Array Bool) :
    (a h block 1) = (((~~~h.e) &&& h.g) + (h.e &&& h.f) + (((h.b ^^^ h.c) &&& h.a) ^^^ (h.b &&& h.c)) + ((h.a).rotateLeft 10 ^^^ (h.a).rotateLeft 19 ^^^ (h.a).rotateLeft 30) + ((h.e).rotateLeft 21 ^^^ (h.e).rotateLeft 26 ^^^ (h.e).rotateLeft 7) + 0x428a2f98 + (word block 0) + h.h) := by
  refine (aWord_succ h ((schedule block).map UInt32.toBitVec) 0).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (h.h + bitVecBigSigma1 h.e + bitVecChoice h.e h.f h.g + 0x428a2f98 + (word block 0)) + (bitVecBigSigma0 h.a + bitVecMajority h.a h.b h.c) = (((~~~h.e) &&& h.g) + (h.e &&& h.f) + (((h.b ^^^ h.c) &&& h.a) ^^^ (h.b &&& h.c)) + ((h.a).rotateLeft 10 ^^^ (h.a).rotateLeft 19 ^^^ (h.a).rotateLeft 30) + ((h.e).rotateLeft 21 ^^^ (h.e).rotateLeft 26 ^^^ (h.e).rotateLeft 7) + 0x428a2f98 + (word block 0) + h.h)
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]
  generalize (word block 0) = v0
  ac_rfl

theorem e01 (h : BitVecState) (block : Array Bool) :
    (e h block 1) = (((~~~h.e) &&& h.g) + (h.e &&& h.f) + ((h.e).rotateLeft 21 ^^^ (h.e).rotateLeft 26 ^^^ (h.e).rotateLeft 7) + 0x428a2f98 + (word block 0) + h.d + h.h) := by
  refine (eWord_succ h ((schedule block).map UInt32.toBitVec) 0).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change h.d + (h.h + bitVecBigSigma1 h.e + bitVecChoice h.e h.f h.g + 0x428a2f98 + (word block 0)) = (((~~~h.e) &&& h.g) + (h.e &&& h.f) + ((h.e).rotateLeft 21 ^^^ (h.e).rotateLeft 26 ^^^ (h.e).rotateLeft 7) + 0x428a2f98 + (word block 0) + h.d + h.h)
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]
  generalize (word block 0) = v0
  ac_rfl

theorem a02 (h : BitVecState) (block : Array Bool) :
    (a h block 2) = (((~~~(e h block 1)) &&& h.f) + ((e h block 1) &&& h.e) + (((h.a ^^^ h.b) &&& (a h block 1)) ^^^ (h.a &&& h.b)) + (((a h block 1)).rotateLeft 10 ^^^ ((a h block 1)).rotateLeft 19 ^^^ ((a h block 1)).rotateLeft 30) + (((e h block 1)).rotateLeft 21 ^^^ ((e h block 1)).rotateLeft 26 ^^^ ((e h block 1)).rotateLeft 7) + 0x71374491 + (word block 1) + h.g) := by
  refine (aWord_succ h ((schedule block).map UInt32.toBitVec) 1).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (h.g + bitVecBigSigma1 (e h block 1) + bitVecChoice (e h block 1) h.e h.f + 0x71374491 + (word block 1)) + (bitVecBigSigma0 (a h block 1) + bitVecMajority (a h block 1) h.a h.b) = (((~~~(e h block 1)) &&& h.f) + ((e h block 1) &&& h.e) + (((h.a ^^^ h.b) &&& (a h block 1)) ^^^ (h.a &&& h.b)) + (((a h block 1)).rotateLeft 10 ^^^ ((a h block 1)).rotateLeft 19 ^^^ ((a h block 1)).rotateLeft 30) + (((e h block 1)).rotateLeft 21 ^^^ ((e h block 1)).rotateLeft 26 ^^^ ((e h block 1)).rotateLeft 7) + 0x71374491 + (word block 1) + h.g)
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]
  generalize (a h block 1) = v0
  generalize (e h block 1) = v1
  generalize (word block 1) = v2
  ac_rfl

theorem e02 (h : BitVecState) (block : Array Bool) :
    (e h block 2) = (((~~~(e h block 1)) &&& h.f) + ((e h block 1) &&& h.e) + (((e h block 1)).rotateLeft 21 ^^^ ((e h block 1)).rotateLeft 26 ^^^ ((e h block 1)).rotateLeft 7) + 0x71374491 + (word block 1) + h.c + h.g) := by
  refine (eWord_succ h ((schedule block).map UInt32.toBitVec) 1).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change h.c + (h.g + bitVecBigSigma1 (e h block 1) + bitVecChoice (e h block 1) h.e h.f + 0x71374491 + (word block 1)) = (((~~~(e h block 1)) &&& h.f) + ((e h block 1) &&& h.e) + (((e h block 1)).rotateLeft 21 ^^^ ((e h block 1)).rotateLeft 26 ^^^ ((e h block 1)).rotateLeft 7) + 0x71374491 + (word block 1) + h.c + h.g)
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]
  generalize (e h block 1) = v0
  generalize (word block 1) = v1
  ac_rfl

theorem a03 (h : BitVecState) (block : Array Bool) :
    (a h block 3) = (((~~~(e h block 2)) &&& h.e) + ((e h block 1) &&& (e h block 2)) + ((((a h block 1) ^^^ h.a) &&& (a h block 2)) ^^^ ((a h block 1) &&& h.a)) + (((a h block 2)).rotateLeft 10 ^^^ ((a h block 2)).rotateLeft 19 ^^^ ((a h block 2)).rotateLeft 30) + (((e h block 2)).rotateLeft 21 ^^^ ((e h block 2)).rotateLeft 26 ^^^ ((e h block 2)).rotateLeft 7) + 0xb5c0fbcf + (word block 2) + h.f) := by
  refine (aWord_succ h ((schedule block).map UInt32.toBitVec) 2).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (h.f + bitVecBigSigma1 (e h block 2) + bitVecChoice (e h block 2) (e h block 1) h.e + 0xb5c0fbcf + (word block 2)) + (bitVecBigSigma0 (a h block 2) + bitVecMajority (a h block 2) (a h block 1) h.a) = (((~~~(e h block 2)) &&& h.e) + ((e h block 1) &&& (e h block 2)) + ((((a h block 1) ^^^ h.a) &&& (a h block 2)) ^^^ ((a h block 1) &&& h.a)) + (((a h block 2)).rotateLeft 10 ^^^ ((a h block 2)).rotateLeft 19 ^^^ ((a h block 2)).rotateLeft 30) + (((e h block 2)).rotateLeft 21 ^^^ ((e h block 2)).rotateLeft 26 ^^^ ((e h block 2)).rotateLeft 7) + 0xb5c0fbcf + (word block 2) + h.f)
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]
  generalize (a h block 1) = v0
  generalize (a h block 2) = v1
  generalize (e h block 1) = v2
  generalize (e h block 2) = v3
  generalize (word block 2) = v4
  ac_rfl

theorem e03 (h : BitVecState) (block : Array Bool) :
    (e h block 3) = (((~~~(e h block 2)) &&& h.e) + ((e h block 1) &&& (e h block 2)) + (((e h block 2)).rotateLeft 21 ^^^ ((e h block 2)).rotateLeft 26 ^^^ ((e h block 2)).rotateLeft 7) + 0xb5c0fbcf + (word block 2) + h.b + h.f) := by
  refine (eWord_succ h ((schedule block).map UInt32.toBitVec) 2).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change h.b + (h.f + bitVecBigSigma1 (e h block 2) + bitVecChoice (e h block 2) (e h block 1) h.e + 0xb5c0fbcf + (word block 2)) = (((~~~(e h block 2)) &&& h.e) + ((e h block 1) &&& (e h block 2)) + (((e h block 2)).rotateLeft 21 ^^^ ((e h block 2)).rotateLeft 26 ^^^ ((e h block 2)).rotateLeft 7) + 0xb5c0fbcf + (word block 2) + h.b + h.f)
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]
  generalize (e h block 1) = v0
  generalize (e h block 2) = v1
  generalize (word block 2) = v2
  ac_rfl

theorem a04 (h : BitVecState) (block : Array Bool) :
    (a h block 4) = (((~~~(e h block 3)) &&& (e h block 1)) + ((e h block 2) &&& (e h block 3)) + ((((a h block 1) ^^^ (a h block 2)) &&& (a h block 3)) ^^^ ((a h block 1) &&& (a h block 2))) + (((a h block 3)).rotateLeft 10 ^^^ ((a h block 3)).rotateLeft 19 ^^^ ((a h block 3)).rotateLeft 30) + (((e h block 3)).rotateLeft 21 ^^^ ((e h block 3)).rotateLeft 26 ^^^ ((e h block 3)).rotateLeft 7) + 0xe9b5dba5 + (word block 3) + h.e) := by
  refine (aWord_succ h ((schedule block).map UInt32.toBitVec) 3).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (h.e + bitVecBigSigma1 (e h block 3) + bitVecChoice (e h block 3) (e h block 2) (e h block 1) + 0xe9b5dba5 + (word block 3)) + (bitVecBigSigma0 (a h block 3) + bitVecMajority (a h block 3) (a h block 2) (a h block 1)) = (((~~~(e h block 3)) &&& (e h block 1)) + ((e h block 2) &&& (e h block 3)) + ((((a h block 1) ^^^ (a h block 2)) &&& (a h block 3)) ^^^ ((a h block 1) &&& (a h block 2))) + (((a h block 3)).rotateLeft 10 ^^^ ((a h block 3)).rotateLeft 19 ^^^ ((a h block 3)).rotateLeft 30) + (((e h block 3)).rotateLeft 21 ^^^ ((e h block 3)).rotateLeft 26 ^^^ ((e h block 3)).rotateLeft 7) + 0xe9b5dba5 + (word block 3) + h.e)
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]
  generalize (a h block 1) = v0
  generalize (a h block 2) = v1
  generalize (a h block 3) = v2
  generalize (e h block 1) = v3
  generalize (e h block 2) = v4
  generalize (e h block 3) = v5
  generalize (word block 3) = v6
  ac_rfl

theorem e04 (h : BitVecState) (block : Array Bool) :
    (e h block 4) = (((~~~(e h block 3)) &&& (e h block 1)) + ((e h block 2) &&& (e h block 3)) + (((e h block 3)).rotateLeft 21 ^^^ ((e h block 3)).rotateLeft 26 ^^^ ((e h block 3)).rotateLeft 7) + 0xe9b5dba5 + (word block 3) + h.a + h.e) := by
  refine (eWord_succ h ((schedule block).map UInt32.toBitVec) 3).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change h.a + (h.e + bitVecBigSigma1 (e h block 3) + bitVecChoice (e h block 3) (e h block 2) (e h block 1) + 0xe9b5dba5 + (word block 3)) = (((~~~(e h block 3)) &&& (e h block 1)) + ((e h block 2) &&& (e h block 3)) + (((e h block 3)).rotateLeft 21 ^^^ ((e h block 3)).rotateLeft 26 ^^^ ((e h block 3)).rotateLeft 7) + 0xe9b5dba5 + (word block 3) + h.a + h.e)
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]
  generalize (e h block 1) = v0
  generalize (e h block 2) = v1
  generalize (e h block 3) = v2
  generalize (word block 3) = v3
  ac_rfl

theorem a05 (h : BitVecState) (block : Array Bool) :
    (a h block 5) = (((~~~(e h block 4)) &&& (e h block 2)) + ((e h block 3) &&& (e h block 4)) + ((((a h block 2) ^^^ (a h block 3)) &&& (a h block 4)) ^^^ ((a h block 2) &&& (a h block 3))) + (((a h block 4)).rotateLeft 10 ^^^ ((a h block 4)).rotateLeft 19 ^^^ ((a h block 4)).rotateLeft 30) + (((e h block 4)).rotateLeft 21 ^^^ ((e h block 4)).rotateLeft 26 ^^^ ((e h block 4)).rotateLeft 7) + 0x3956c25b + (e h block 1) + (word block 4)) := by
  refine (aWord_succ h ((schedule block).map UInt32.toBitVec) 4).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 1) + bitVecBigSigma1 (e h block 4) + bitVecChoice (e h block 4) (e h block 3) (e h block 2) + 0x3956c25b + (word block 4)) + (bitVecBigSigma0 (a h block 4) + bitVecMajority (a h block 4) (a h block 3) (a h block 2)) = (((~~~(e h block 4)) &&& (e h block 2)) + ((e h block 3) &&& (e h block 4)) + ((((a h block 2) ^^^ (a h block 3)) &&& (a h block 4)) ^^^ ((a h block 2) &&& (a h block 3))) + (((a h block 4)).rotateLeft 10 ^^^ ((a h block 4)).rotateLeft 19 ^^^ ((a h block 4)).rotateLeft 30) + (((e h block 4)).rotateLeft 21 ^^^ ((e h block 4)).rotateLeft 26 ^^^ ((e h block 4)).rotateLeft 7) + 0x3956c25b + (e h block 1) + (word block 4))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]
  generalize (a h block 2) = v0
  generalize (a h block 3) = v1
  generalize (a h block 4) = v2
  generalize (e h block 1) = v3
  generalize (e h block 2) = v4
  generalize (e h block 3) = v5
  generalize (e h block 4) = v6
  generalize (word block 4) = v7
  ac_rfl

theorem e05 (h : BitVecState) (block : Array Bool) :
    (e h block 5) = (((~~~(e h block 4)) &&& (e h block 2)) + ((e h block 3) &&& (e h block 4)) + (((e h block 4)).rotateLeft 21 ^^^ ((e h block 4)).rotateLeft 26 ^^^ ((e h block 4)).rotateLeft 7) + 0x3956c25b + (a h block 1) + (e h block 1) + (word block 4)) := by
  refine (eWord_succ h ((schedule block).map UInt32.toBitVec) 4).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 1) + ((e h block 1) + bitVecBigSigma1 (e h block 4) + bitVecChoice (e h block 4) (e h block 3) (e h block 2) + 0x3956c25b + (word block 4)) = (((~~~(e h block 4)) &&& (e h block 2)) + ((e h block 3) &&& (e h block 4)) + (((e h block 4)).rotateLeft 21 ^^^ ((e h block 4)).rotateLeft 26 ^^^ ((e h block 4)).rotateLeft 7) + 0x3956c25b + (a h block 1) + (e h block 1) + (word block 4))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]
  generalize (a h block 1) = v0
  generalize (e h block 1) = v1
  generalize (e h block 2) = v2
  generalize (e h block 3) = v3
  generalize (e h block 4) = v4
  generalize (word block 4) = v5
  ac_rfl

theorem a06 (h : BitVecState) (block : Array Bool) :
    (a h block 6) = (((~~~(e h block 5)) &&& (e h block 3)) + ((e h block 4) &&& (e h block 5)) + ((((a h block 3) ^^^ (a h block 4)) &&& (a h block 5)) ^^^ ((a h block 3) &&& (a h block 4))) + (((a h block 5)).rotateLeft 10 ^^^ ((a h block 5)).rotateLeft 19 ^^^ ((a h block 5)).rotateLeft 30) + (((e h block 5)).rotateLeft 21 ^^^ ((e h block 5)).rotateLeft 26 ^^^ ((e h block 5)).rotateLeft 7) + 0x59f111f1 + (e h block 2) + (word block 5)) := by
  refine (aWord_succ h ((schedule block).map UInt32.toBitVec) 5).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 2) + bitVecBigSigma1 (e h block 5) + bitVecChoice (e h block 5) (e h block 4) (e h block 3) + 0x59f111f1 + (word block 5)) + (bitVecBigSigma0 (a h block 5) + bitVecMajority (a h block 5) (a h block 4) (a h block 3)) = (((~~~(e h block 5)) &&& (e h block 3)) + ((e h block 4) &&& (e h block 5)) + ((((a h block 3) ^^^ (a h block 4)) &&& (a h block 5)) ^^^ ((a h block 3) &&& (a h block 4))) + (((a h block 5)).rotateLeft 10 ^^^ ((a h block 5)).rotateLeft 19 ^^^ ((a h block 5)).rotateLeft 30) + (((e h block 5)).rotateLeft 21 ^^^ ((e h block 5)).rotateLeft 26 ^^^ ((e h block 5)).rotateLeft 7) + 0x59f111f1 + (e h block 2) + (word block 5))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]
  generalize (a h block 3) = v0
  generalize (a h block 4) = v1
  generalize (a h block 5) = v2
  generalize (e h block 2) = v3
  generalize (e h block 3) = v4
  generalize (e h block 4) = v5
  generalize (e h block 5) = v6
  generalize (word block 5) = v7
  ac_rfl

theorem e06 (h : BitVecState) (block : Array Bool) :
    (e h block 6) = (((~~~(e h block 5)) &&& (e h block 3)) + ((e h block 4) &&& (e h block 5)) + (((e h block 5)).rotateLeft 21 ^^^ ((e h block 5)).rotateLeft 26 ^^^ ((e h block 5)).rotateLeft 7) + 0x59f111f1 + (a h block 2) + (e h block 2) + (word block 5)) := by
  refine (eWord_succ h ((schedule block).map UInt32.toBitVec) 5).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 2) + ((e h block 2) + bitVecBigSigma1 (e h block 5) + bitVecChoice (e h block 5) (e h block 4) (e h block 3) + 0x59f111f1 + (word block 5)) = (((~~~(e h block 5)) &&& (e h block 3)) + ((e h block 4) &&& (e h block 5)) + (((e h block 5)).rotateLeft 21 ^^^ ((e h block 5)).rotateLeft 26 ^^^ ((e h block 5)).rotateLeft 7) + 0x59f111f1 + (a h block 2) + (e h block 2) + (word block 5))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]
  generalize (a h block 2) = v0
  generalize (e h block 2) = v1
  generalize (e h block 3) = v2
  generalize (e h block 4) = v3
  generalize (e h block 5) = v4
  generalize (word block 5) = v5
  ac_rfl

theorem a07 (h : BitVecState) (block : Array Bool) :
    (a h block 7) = (((~~~(e h block 6)) &&& (e h block 4)) + ((e h block 5) &&& (e h block 6)) + ((((a h block 4) ^^^ (a h block 5)) &&& (a h block 6)) ^^^ ((a h block 4) &&& (a h block 5))) + (((a h block 6)).rotateLeft 10 ^^^ ((a h block 6)).rotateLeft 19 ^^^ ((a h block 6)).rotateLeft 30) + (((e h block 6)).rotateLeft 21 ^^^ ((e h block 6)).rotateLeft 26 ^^^ ((e h block 6)).rotateLeft 7) + 0x923f82a4 + (e h block 3) + (word block 6)) := by
  refine (aWord_succ h ((schedule block).map UInt32.toBitVec) 6).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 3) + bitVecBigSigma1 (e h block 6) + bitVecChoice (e h block 6) (e h block 5) (e h block 4) + 0x923f82a4 + (word block 6)) + (bitVecBigSigma0 (a h block 6) + bitVecMajority (a h block 6) (a h block 5) (a h block 4)) = (((~~~(e h block 6)) &&& (e h block 4)) + ((e h block 5) &&& (e h block 6)) + ((((a h block 4) ^^^ (a h block 5)) &&& (a h block 6)) ^^^ ((a h block 4) &&& (a h block 5))) + (((a h block 6)).rotateLeft 10 ^^^ ((a h block 6)).rotateLeft 19 ^^^ ((a h block 6)).rotateLeft 30) + (((e h block 6)).rotateLeft 21 ^^^ ((e h block 6)).rotateLeft 26 ^^^ ((e h block 6)).rotateLeft 7) + 0x923f82a4 + (e h block 3) + (word block 6))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]
  generalize (a h block 4) = v0
  generalize (a h block 5) = v1
  generalize (a h block 6) = v2
  generalize (e h block 3) = v3
  generalize (e h block 4) = v4
  generalize (e h block 5) = v5
  generalize (e h block 6) = v6
  generalize (word block 6) = v7
  ac_rfl

theorem e07 (h : BitVecState) (block : Array Bool) :
    (e h block 7) = (((~~~(e h block 6)) &&& (e h block 4)) + ((e h block 5) &&& (e h block 6)) + (((e h block 6)).rotateLeft 21 ^^^ ((e h block 6)).rotateLeft 26 ^^^ ((e h block 6)).rotateLeft 7) + 0x923f82a4 + (a h block 3) + (e h block 3) + (word block 6)) := by
  refine (eWord_succ h ((schedule block).map UInt32.toBitVec) 6).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 3) + ((e h block 3) + bitVecBigSigma1 (e h block 6) + bitVecChoice (e h block 6) (e h block 5) (e h block 4) + 0x923f82a4 + (word block 6)) = (((~~~(e h block 6)) &&& (e h block 4)) + ((e h block 5) &&& (e h block 6)) + (((e h block 6)).rotateLeft 21 ^^^ ((e h block 6)).rotateLeft 26 ^^^ ((e h block 6)).rotateLeft 7) + 0x923f82a4 + (a h block 3) + (e h block 3) + (word block 6))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]
  generalize (a h block 3) = v0
  generalize (e h block 3) = v1
  generalize (e h block 4) = v2
  generalize (e h block 5) = v3
  generalize (e h block 6) = v4
  generalize (word block 6) = v5
  ac_rfl

theorem a08 (h : BitVecState) (block : Array Bool) :
    (a h block 8) = (((~~~(e h block 7)) &&& (e h block 5)) + ((e h block 6) &&& (e h block 7)) + ((((a h block 5) ^^^ (a h block 6)) &&& (a h block 7)) ^^^ ((a h block 5) &&& (a h block 6))) + (((a h block 7)).rotateLeft 10 ^^^ ((a h block 7)).rotateLeft 19 ^^^ ((a h block 7)).rotateLeft 30) + (((e h block 7)).rotateLeft 21 ^^^ ((e h block 7)).rotateLeft 26 ^^^ ((e h block 7)).rotateLeft 7) + 0xab1c5ed5 + (e h block 4) + (word block 7)) := by
  refine (aWord_succ h ((schedule block).map UInt32.toBitVec) 7).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 4) + bitVecBigSigma1 (e h block 7) + bitVecChoice (e h block 7) (e h block 6) (e h block 5) + 0xab1c5ed5 + (word block 7)) + (bitVecBigSigma0 (a h block 7) + bitVecMajority (a h block 7) (a h block 6) (a h block 5)) = (((~~~(e h block 7)) &&& (e h block 5)) + ((e h block 6) &&& (e h block 7)) + ((((a h block 5) ^^^ (a h block 6)) &&& (a h block 7)) ^^^ ((a h block 5) &&& (a h block 6))) + (((a h block 7)).rotateLeft 10 ^^^ ((a h block 7)).rotateLeft 19 ^^^ ((a h block 7)).rotateLeft 30) + (((e h block 7)).rotateLeft 21 ^^^ ((e h block 7)).rotateLeft 26 ^^^ ((e h block 7)).rotateLeft 7) + 0xab1c5ed5 + (e h block 4) + (word block 7))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]
  generalize (a h block 5) = v0
  generalize (a h block 6) = v1
  generalize (a h block 7) = v2
  generalize (e h block 4) = v3
  generalize (e h block 5) = v4
  generalize (e h block 6) = v5
  generalize (e h block 7) = v6
  generalize (word block 7) = v7
  ac_rfl

theorem e08 (h : BitVecState) (block : Array Bool) :
    (e h block 8) = (((~~~(e h block 7)) &&& (e h block 5)) + ((e h block 6) &&& (e h block 7)) + (((e h block 7)).rotateLeft 21 ^^^ ((e h block 7)).rotateLeft 26 ^^^ ((e h block 7)).rotateLeft 7) + 0xab1c5ed5 + (a h block 4) + (e h block 4) + (word block 7)) := by
  refine (eWord_succ h ((schedule block).map UInt32.toBitVec) 7).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 4) + ((e h block 4) + bitVecBigSigma1 (e h block 7) + bitVecChoice (e h block 7) (e h block 6) (e h block 5) + 0xab1c5ed5 + (word block 7)) = (((~~~(e h block 7)) &&& (e h block 5)) + ((e h block 6) &&& (e h block 7)) + (((e h block 7)).rotateLeft 21 ^^^ ((e h block 7)).rotateLeft 26 ^^^ ((e h block 7)).rotateLeft 7) + 0xab1c5ed5 + (a h block 4) + (e h block 4) + (word block 7))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]
  generalize (a h block 4) = v0
  generalize (e h block 4) = v1
  generalize (e h block 5) = v2
  generalize (e h block 6) = v3
  generalize (e h block 7) = v4
  generalize (word block 7) = v5
  ac_rfl

theorem a09 (h : BitVecState) (block : Array Bool) :
    (a h block 9) = (((~~~(e h block 8)) &&& (e h block 6)) + ((e h block 7) &&& (e h block 8)) + ((((a h block 6) ^^^ (a h block 7)) &&& (a h block 8)) ^^^ ((a h block 6) &&& (a h block 7))) + (((a h block 8)).rotateLeft 10 ^^^ ((a h block 8)).rotateLeft 19 ^^^ ((a h block 8)).rotateLeft 30) + (((e h block 8)).rotateLeft 21 ^^^ ((e h block 8)).rotateLeft 26 ^^^ ((e h block 8)).rotateLeft 7) + 0xd807aa98 + (e h block 5) + (word block 8)) := by
  refine (aWord_succ h ((schedule block).map UInt32.toBitVec) 8).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 5) + bitVecBigSigma1 (e h block 8) + bitVecChoice (e h block 8) (e h block 7) (e h block 6) + 0xd807aa98 + (word block 8)) + (bitVecBigSigma0 (a h block 8) + bitVecMajority (a h block 8) (a h block 7) (a h block 6)) = (((~~~(e h block 8)) &&& (e h block 6)) + ((e h block 7) &&& (e h block 8)) + ((((a h block 6) ^^^ (a h block 7)) &&& (a h block 8)) ^^^ ((a h block 6) &&& (a h block 7))) + (((a h block 8)).rotateLeft 10 ^^^ ((a h block 8)).rotateLeft 19 ^^^ ((a h block 8)).rotateLeft 30) + (((e h block 8)).rotateLeft 21 ^^^ ((e h block 8)).rotateLeft 26 ^^^ ((e h block 8)).rotateLeft 7) + 0xd807aa98 + (e h block 5) + (word block 8))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]
  generalize (a h block 6) = v0
  generalize (a h block 7) = v1
  generalize (a h block 8) = v2
  generalize (e h block 5) = v3
  generalize (e h block 6) = v4
  generalize (e h block 7) = v5
  generalize (e h block 8) = v6
  generalize (word block 8) = v7
  ac_rfl

theorem e09 (h : BitVecState) (block : Array Bool) :
    (e h block 9) = (((~~~(e h block 8)) &&& (e h block 6)) + ((e h block 7) &&& (e h block 8)) + (((e h block 8)).rotateLeft 21 ^^^ ((e h block 8)).rotateLeft 26 ^^^ ((e h block 8)).rotateLeft 7) + 0xd807aa98 + (a h block 5) + (e h block 5) + (word block 8)) := by
  refine (eWord_succ h ((schedule block).map UInt32.toBitVec) 8).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 5) + ((e h block 5) + bitVecBigSigma1 (e h block 8) + bitVecChoice (e h block 8) (e h block 7) (e h block 6) + 0xd807aa98 + (word block 8)) = (((~~~(e h block 8)) &&& (e h block 6)) + ((e h block 7) &&& (e h block 8)) + (((e h block 8)).rotateLeft 21 ^^^ ((e h block 8)).rotateLeft 26 ^^^ ((e h block 8)).rotateLeft 7) + 0xd807aa98 + (a h block 5) + (e h block 5) + (word block 8))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]
  generalize (a h block 5) = v0
  generalize (e h block 5) = v1
  generalize (e h block 6) = v2
  generalize (e h block 7) = v3
  generalize (e h block 8) = v4
  generalize (word block 8) = v5
  ac_rfl

theorem a10 (h : BitVecState) (block : Array Bool) :
    (a h block 10) = (((~~~(e h block 9)) &&& (e h block 7)) + ((e h block 8) &&& (e h block 9)) + ((((a h block 7) ^^^ (a h block 8)) &&& (a h block 9)) ^^^ ((a h block 7) &&& (a h block 8))) + (((a h block 9)).rotateLeft 10 ^^^ ((a h block 9)).rotateLeft 19 ^^^ ((a h block 9)).rotateLeft 30) + (((e h block 9)).rotateLeft 21 ^^^ ((e h block 9)).rotateLeft 26 ^^^ ((e h block 9)).rotateLeft 7) + 0x12835b01 + (e h block 6) + (word block 9)) := by
  refine (aWord_succ h ((schedule block).map UInt32.toBitVec) 9).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 6) + bitVecBigSigma1 (e h block 9) + bitVecChoice (e h block 9) (e h block 8) (e h block 7) + 0x12835b01 + (word block 9)) + (bitVecBigSigma0 (a h block 9) + bitVecMajority (a h block 9) (a h block 8) (a h block 7)) = (((~~~(e h block 9)) &&& (e h block 7)) + ((e h block 8) &&& (e h block 9)) + ((((a h block 7) ^^^ (a h block 8)) &&& (a h block 9)) ^^^ ((a h block 7) &&& (a h block 8))) + (((a h block 9)).rotateLeft 10 ^^^ ((a h block 9)).rotateLeft 19 ^^^ ((a h block 9)).rotateLeft 30) + (((e h block 9)).rotateLeft 21 ^^^ ((e h block 9)).rotateLeft 26 ^^^ ((e h block 9)).rotateLeft 7) + 0x12835b01 + (e h block 6) + (word block 9))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]
  generalize (a h block 7) = v0
  generalize (a h block 8) = v1
  generalize (a h block 9) = v2
  generalize (e h block 6) = v3
  generalize (e h block 7) = v4
  generalize (e h block 8) = v5
  generalize (e h block 9) = v6
  generalize (word block 9) = v7
  ac_rfl

theorem e10 (h : BitVecState) (block : Array Bool) :
    (e h block 10) = (((~~~(e h block 9)) &&& (e h block 7)) + ((e h block 8) &&& (e h block 9)) + (((e h block 9)).rotateLeft 21 ^^^ ((e h block 9)).rotateLeft 26 ^^^ ((e h block 9)).rotateLeft 7) + 0x12835b01 + (a h block 6) + (e h block 6) + (word block 9)) := by
  refine (eWord_succ h ((schedule block).map UInt32.toBitVec) 9).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 6) + ((e h block 6) + bitVecBigSigma1 (e h block 9) + bitVecChoice (e h block 9) (e h block 8) (e h block 7) + 0x12835b01 + (word block 9)) = (((~~~(e h block 9)) &&& (e h block 7)) + ((e h block 8) &&& (e h block 9)) + (((e h block 9)).rotateLeft 21 ^^^ ((e h block 9)).rotateLeft 26 ^^^ ((e h block 9)).rotateLeft 7) + 0x12835b01 + (a h block 6) + (e h block 6) + (word block 9))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]
  generalize (a h block 6) = v0
  generalize (e h block 6) = v1
  generalize (e h block 7) = v2
  generalize (e h block 8) = v3
  generalize (e h block 9) = v4
  generalize (word block 9) = v5
  ac_rfl

theorem a11 (h : BitVecState) (block : Array Bool) :
    (a h block 11) = (((~~~(e h block 10)) &&& (e h block 8)) + ((e h block 10) &&& (e h block 9)) + ((((a h block 8) ^^^ (a h block 9)) &&& (a h block 10)) ^^^ ((a h block 8) &&& (a h block 9))) + (((a h block 10)).rotateLeft 10 ^^^ ((a h block 10)).rotateLeft 19 ^^^ ((a h block 10)).rotateLeft 30) + (((e h block 10)).rotateLeft 21 ^^^ ((e h block 10)).rotateLeft 26 ^^^ ((e h block 10)).rotateLeft 7) + 0x243185be + (e h block 7) + (word block 10)) := by
  refine (aWord_succ h ((schedule block).map UInt32.toBitVec) 10).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 7) + bitVecBigSigma1 (e h block 10) + bitVecChoice (e h block 10) (e h block 9) (e h block 8) + 0x243185be + (word block 10)) + (bitVecBigSigma0 (a h block 10) + bitVecMajority (a h block 10) (a h block 9) (a h block 8)) = (((~~~(e h block 10)) &&& (e h block 8)) + ((e h block 10) &&& (e h block 9)) + ((((a h block 8) ^^^ (a h block 9)) &&& (a h block 10)) ^^^ ((a h block 8) &&& (a h block 9))) + (((a h block 10)).rotateLeft 10 ^^^ ((a h block 10)).rotateLeft 19 ^^^ ((a h block 10)).rotateLeft 30) + (((e h block 10)).rotateLeft 21 ^^^ ((e h block 10)).rotateLeft 26 ^^^ ((e h block 10)).rotateLeft 7) + 0x243185be + (e h block 7) + (word block 10))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]
  generalize (a h block 10) = v0
  generalize (a h block 8) = v1
  generalize (a h block 9) = v2
  generalize (e h block 10) = v3
  generalize (e h block 7) = v4
  generalize (e h block 8) = v5
  generalize (e h block 9) = v6
  generalize (word block 10) = v7
  ac_rfl

theorem e11 (h : BitVecState) (block : Array Bool) :
    (e h block 11) = (((~~~(e h block 10)) &&& (e h block 8)) + ((e h block 10) &&& (e h block 9)) + (((e h block 10)).rotateLeft 21 ^^^ ((e h block 10)).rotateLeft 26 ^^^ ((e h block 10)).rotateLeft 7) + 0x243185be + (a h block 7) + (e h block 7) + (word block 10)) := by
  refine (eWord_succ h ((schedule block).map UInt32.toBitVec) 10).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 7) + ((e h block 7) + bitVecBigSigma1 (e h block 10) + bitVecChoice (e h block 10) (e h block 9) (e h block 8) + 0x243185be + (word block 10)) = (((~~~(e h block 10)) &&& (e h block 8)) + ((e h block 10) &&& (e h block 9)) + (((e h block 10)).rotateLeft 21 ^^^ ((e h block 10)).rotateLeft 26 ^^^ ((e h block 10)).rotateLeft 7) + 0x243185be + (a h block 7) + (e h block 7) + (word block 10))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]
  generalize (a h block 7) = v0
  generalize (e h block 10) = v1
  generalize (e h block 7) = v2
  generalize (e h block 8) = v3
  generalize (e h block 9) = v4
  generalize (word block 10) = v5
  ac_rfl

theorem a12 (h : BitVecState) (block : Array Bool) :
    (a h block 12) = (((~~~(e h block 11)) &&& (e h block 9)) + ((e h block 10) &&& (e h block 11)) + ((((a h block 10) ^^^ (a h block 9)) &&& (a h block 11)) ^^^ ((a h block 10) &&& (a h block 9))) + (((a h block 11)).rotateLeft 10 ^^^ ((a h block 11)).rotateLeft 19 ^^^ ((a h block 11)).rotateLeft 30) + (((e h block 11)).rotateLeft 21 ^^^ ((e h block 11)).rotateLeft 26 ^^^ ((e h block 11)).rotateLeft 7) + 0x550c7dc3 + (e h block 8) + (word block 11)) := by
  refine (aWord_succ h ((schedule block).map UInt32.toBitVec) 11).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 8) + bitVecBigSigma1 (e h block 11) + bitVecChoice (e h block 11) (e h block 10) (e h block 9) + 0x550c7dc3 + (word block 11)) + (bitVecBigSigma0 (a h block 11) + bitVecMajority (a h block 11) (a h block 10) (a h block 9)) = (((~~~(e h block 11)) &&& (e h block 9)) + ((e h block 10) &&& (e h block 11)) + ((((a h block 10) ^^^ (a h block 9)) &&& (a h block 11)) ^^^ ((a h block 10) &&& (a h block 9))) + (((a h block 11)).rotateLeft 10 ^^^ ((a h block 11)).rotateLeft 19 ^^^ ((a h block 11)).rotateLeft 30) + (((e h block 11)).rotateLeft 21 ^^^ ((e h block 11)).rotateLeft 26 ^^^ ((e h block 11)).rotateLeft 7) + 0x550c7dc3 + (e h block 8) + (word block 11))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]
  generalize (a h block 10) = v0
  generalize (a h block 11) = v1
  generalize (a h block 9) = v2
  generalize (e h block 10) = v3
  generalize (e h block 11) = v4
  generalize (e h block 8) = v5
  generalize (e h block 9) = v6
  generalize (word block 11) = v7
  ac_rfl

theorem e12 (h : BitVecState) (block : Array Bool) :
    (e h block 12) = (((~~~(e h block 11)) &&& (e h block 9)) + ((e h block 10) &&& (e h block 11)) + (((e h block 11)).rotateLeft 21 ^^^ ((e h block 11)).rotateLeft 26 ^^^ ((e h block 11)).rotateLeft 7) + 0x550c7dc3 + (a h block 8) + (e h block 8) + (word block 11)) := by
  refine (eWord_succ h ((schedule block).map UInt32.toBitVec) 11).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 8) + ((e h block 8) + bitVecBigSigma1 (e h block 11) + bitVecChoice (e h block 11) (e h block 10) (e h block 9) + 0x550c7dc3 + (word block 11)) = (((~~~(e h block 11)) &&& (e h block 9)) + ((e h block 10) &&& (e h block 11)) + (((e h block 11)).rotateLeft 21 ^^^ ((e h block 11)).rotateLeft 26 ^^^ ((e h block 11)).rotateLeft 7) + 0x550c7dc3 + (a h block 8) + (e h block 8) + (word block 11))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]
  generalize (a h block 8) = v0
  generalize (e h block 10) = v1
  generalize (e h block 11) = v2
  generalize (e h block 8) = v3
  generalize (e h block 9) = v4
  generalize (word block 11) = v5
  ac_rfl

theorem a13 (h : BitVecState) (block : Array Bool) :
    (a h block 13) = (((~~~(e h block 12)) &&& (e h block 10)) + ((e h block 11) &&& (e h block 12)) + ((((a h block 10) ^^^ (a h block 11)) &&& (a h block 12)) ^^^ ((a h block 10) &&& (a h block 11))) + (((a h block 12)).rotateLeft 10 ^^^ ((a h block 12)).rotateLeft 19 ^^^ ((a h block 12)).rotateLeft 30) + (((e h block 12)).rotateLeft 21 ^^^ ((e h block 12)).rotateLeft 26 ^^^ ((e h block 12)).rotateLeft 7) + 0x72be5d74 + (e h block 9) + (word block 12)) := by
  refine (aWord_succ h ((schedule block).map UInt32.toBitVec) 12).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 9) + bitVecBigSigma1 (e h block 12) + bitVecChoice (e h block 12) (e h block 11) (e h block 10) + 0x72be5d74 + (word block 12)) + (bitVecBigSigma0 (a h block 12) + bitVecMajority (a h block 12) (a h block 11) (a h block 10)) = (((~~~(e h block 12)) &&& (e h block 10)) + ((e h block 11) &&& (e h block 12)) + ((((a h block 10) ^^^ (a h block 11)) &&& (a h block 12)) ^^^ ((a h block 10) &&& (a h block 11))) + (((a h block 12)).rotateLeft 10 ^^^ ((a h block 12)).rotateLeft 19 ^^^ ((a h block 12)).rotateLeft 30) + (((e h block 12)).rotateLeft 21 ^^^ ((e h block 12)).rotateLeft 26 ^^^ ((e h block 12)).rotateLeft 7) + 0x72be5d74 + (e h block 9) + (word block 12))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]
  generalize (a h block 10) = v0
  generalize (a h block 11) = v1
  generalize (a h block 12) = v2
  generalize (e h block 10) = v3
  generalize (e h block 11) = v4
  generalize (e h block 12) = v5
  generalize (e h block 9) = v6
  generalize (word block 12) = v7
  ac_rfl

theorem e13 (h : BitVecState) (block : Array Bool) :
    (e h block 13) = (((~~~(e h block 12)) &&& (e h block 10)) + ((e h block 11) &&& (e h block 12)) + (((e h block 12)).rotateLeft 21 ^^^ ((e h block 12)).rotateLeft 26 ^^^ ((e h block 12)).rotateLeft 7) + 0x72be5d74 + (a h block 9) + (e h block 9) + (word block 12)) := by
  refine (eWord_succ h ((schedule block).map UInt32.toBitVec) 12).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 9) + ((e h block 9) + bitVecBigSigma1 (e h block 12) + bitVecChoice (e h block 12) (e h block 11) (e h block 10) + 0x72be5d74 + (word block 12)) = (((~~~(e h block 12)) &&& (e h block 10)) + ((e h block 11) &&& (e h block 12)) + (((e h block 12)).rotateLeft 21 ^^^ ((e h block 12)).rotateLeft 26 ^^^ ((e h block 12)).rotateLeft 7) + 0x72be5d74 + (a h block 9) + (e h block 9) + (word block 12))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]
  generalize (a h block 9) = v0
  generalize (e h block 10) = v1
  generalize (e h block 11) = v2
  generalize (e h block 12) = v3
  generalize (e h block 9) = v4
  generalize (word block 12) = v5
  ac_rfl

theorem a14 (h : BitVecState) (block : Array Bool) :
    (a h block 14) = (((~~~(e h block 13)) &&& (e h block 11)) + ((e h block 12) &&& (e h block 13)) + ((((a h block 11) ^^^ (a h block 12)) &&& (a h block 13)) ^^^ ((a h block 11) &&& (a h block 12))) + (((a h block 13)).rotateLeft 10 ^^^ ((a h block 13)).rotateLeft 19 ^^^ ((a h block 13)).rotateLeft 30) + (((e h block 13)).rotateLeft 21 ^^^ ((e h block 13)).rotateLeft 26 ^^^ ((e h block 13)).rotateLeft 7) + 0x80deb1fe + (e h block 10) + (word block 13)) := by
  refine (aWord_succ h ((schedule block).map UInt32.toBitVec) 13).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 10) + bitVecBigSigma1 (e h block 13) + bitVecChoice (e h block 13) (e h block 12) (e h block 11) + 0x80deb1fe + (word block 13)) + (bitVecBigSigma0 (a h block 13) + bitVecMajority (a h block 13) (a h block 12) (a h block 11)) = (((~~~(e h block 13)) &&& (e h block 11)) + ((e h block 12) &&& (e h block 13)) + ((((a h block 11) ^^^ (a h block 12)) &&& (a h block 13)) ^^^ ((a h block 11) &&& (a h block 12))) + (((a h block 13)).rotateLeft 10 ^^^ ((a h block 13)).rotateLeft 19 ^^^ ((a h block 13)).rotateLeft 30) + (((e h block 13)).rotateLeft 21 ^^^ ((e h block 13)).rotateLeft 26 ^^^ ((e h block 13)).rotateLeft 7) + 0x80deb1fe + (e h block 10) + (word block 13))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]
  generalize (a h block 11) = v0
  generalize (a h block 12) = v1
  generalize (a h block 13) = v2
  generalize (e h block 10) = v3
  generalize (e h block 11) = v4
  generalize (e h block 12) = v5
  generalize (e h block 13) = v6
  generalize (word block 13) = v7
  ac_rfl

theorem e14 (h : BitVecState) (block : Array Bool) :
    (e h block 14) = (((~~~(e h block 13)) &&& (e h block 11)) + ((e h block 12) &&& (e h block 13)) + (((e h block 13)).rotateLeft 21 ^^^ ((e h block 13)).rotateLeft 26 ^^^ ((e h block 13)).rotateLeft 7) + 0x80deb1fe + (a h block 10) + (e h block 10) + (word block 13)) := by
  refine (eWord_succ h ((schedule block).map UInt32.toBitVec) 13).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 10) + ((e h block 10) + bitVecBigSigma1 (e h block 13) + bitVecChoice (e h block 13) (e h block 12) (e h block 11) + 0x80deb1fe + (word block 13)) = (((~~~(e h block 13)) &&& (e h block 11)) + ((e h block 12) &&& (e h block 13)) + (((e h block 13)).rotateLeft 21 ^^^ ((e h block 13)).rotateLeft 26 ^^^ ((e h block 13)).rotateLeft 7) + 0x80deb1fe + (a h block 10) + (e h block 10) + (word block 13))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]
  generalize (a h block 10) = v0
  generalize (e h block 10) = v1
  generalize (e h block 11) = v2
  generalize (e h block 12) = v3
  generalize (e h block 13) = v4
  generalize (word block 13) = v5
  ac_rfl

theorem a15 (h : BitVecState) (block : Array Bool) :
    (a h block 15) = (((~~~(e h block 14)) &&& (e h block 12)) + ((e h block 13) &&& (e h block 14)) + ((((a h block 12) ^^^ (a h block 13)) &&& (a h block 14)) ^^^ ((a h block 12) &&& (a h block 13))) + (((a h block 14)).rotateLeft 10 ^^^ ((a h block 14)).rotateLeft 19 ^^^ ((a h block 14)).rotateLeft 30) + (((e h block 14)).rotateLeft 21 ^^^ ((e h block 14)).rotateLeft 26 ^^^ ((e h block 14)).rotateLeft 7) + 0x9bdc06a7 + (e h block 11) + (word block 14)) := by
  refine (aWord_succ h ((schedule block).map UInt32.toBitVec) 14).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 11) + bitVecBigSigma1 (e h block 14) + bitVecChoice (e h block 14) (e h block 13) (e h block 12) + 0x9bdc06a7 + (word block 14)) + (bitVecBigSigma0 (a h block 14) + bitVecMajority (a h block 14) (a h block 13) (a h block 12)) = (((~~~(e h block 14)) &&& (e h block 12)) + ((e h block 13) &&& (e h block 14)) + ((((a h block 12) ^^^ (a h block 13)) &&& (a h block 14)) ^^^ ((a h block 12) &&& (a h block 13))) + (((a h block 14)).rotateLeft 10 ^^^ ((a h block 14)).rotateLeft 19 ^^^ ((a h block 14)).rotateLeft 30) + (((e h block 14)).rotateLeft 21 ^^^ ((e h block 14)).rotateLeft 26 ^^^ ((e h block 14)).rotateLeft 7) + 0x9bdc06a7 + (e h block 11) + (word block 14))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]
  generalize (a h block 12) = v0
  generalize (a h block 13) = v1
  generalize (a h block 14) = v2
  generalize (e h block 11) = v3
  generalize (e h block 12) = v4
  generalize (e h block 13) = v5
  generalize (e h block 14) = v6
  generalize (word block 14) = v7
  ac_rfl

theorem e15 (h : BitVecState) (block : Array Bool) :
    (e h block 15) = (((~~~(e h block 14)) &&& (e h block 12)) + ((e h block 13) &&& (e h block 14)) + (((e h block 14)).rotateLeft 21 ^^^ ((e h block 14)).rotateLeft 26 ^^^ ((e h block 14)).rotateLeft 7) + 0x9bdc06a7 + (a h block 11) + (e h block 11) + (word block 14)) := by
  refine (eWord_succ h ((schedule block).map UInt32.toBitVec) 14).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 11) + ((e h block 11) + bitVecBigSigma1 (e h block 14) + bitVecChoice (e h block 14) (e h block 13) (e h block 12) + 0x9bdc06a7 + (word block 14)) = (((~~~(e h block 14)) &&& (e h block 12)) + ((e h block 13) &&& (e h block 14)) + (((e h block 14)).rotateLeft 21 ^^^ ((e h block 14)).rotateLeft 26 ^^^ ((e h block 14)).rotateLeft 7) + 0x9bdc06a7 + (a h block 11) + (e h block 11) + (word block 14))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]
  generalize (a h block 11) = v0
  generalize (e h block 11) = v1
  generalize (e h block 12) = v2
  generalize (e h block 13) = v3
  generalize (e h block 14) = v4
  generalize (word block 14) = v5
  ac_rfl

theorem a16 (h : BitVecState) (block : Array Bool) :
    (a h block 16) = (((~~~(e h block 15)) &&& (e h block 13)) + ((e h block 14) &&& (e h block 15)) + ((((a h block 13) ^^^ (a h block 14)) &&& (a h block 15)) ^^^ ((a h block 13) &&& (a h block 14))) + (((a h block 15)).rotateLeft 10 ^^^ ((a h block 15)).rotateLeft 19 ^^^ ((a h block 15)).rotateLeft 30) + (((e h block 15)).rotateLeft 21 ^^^ ((e h block 15)).rotateLeft 26 ^^^ ((e h block 15)).rotateLeft 7) + 0xc19bf174 + (e h block 12) + (word block 15)) := by
  refine (aWord_succ h ((schedule block).map UInt32.toBitVec) 15).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 12) + bitVecBigSigma1 (e h block 15) + bitVecChoice (e h block 15) (e h block 14) (e h block 13) + 0xc19bf174 + (word block 15)) + (bitVecBigSigma0 (a h block 15) + bitVecMajority (a h block 15) (a h block 14) (a h block 13)) = (((~~~(e h block 15)) &&& (e h block 13)) + ((e h block 14) &&& (e h block 15)) + ((((a h block 13) ^^^ (a h block 14)) &&& (a h block 15)) ^^^ ((a h block 13) &&& (a h block 14))) + (((a h block 15)).rotateLeft 10 ^^^ ((a h block 15)).rotateLeft 19 ^^^ ((a h block 15)).rotateLeft 30) + (((e h block 15)).rotateLeft 21 ^^^ ((e h block 15)).rotateLeft 26 ^^^ ((e h block 15)).rotateLeft 7) + 0xc19bf174 + (e h block 12) + (word block 15))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]
  generalize (a h block 13) = v0
  generalize (a h block 14) = v1
  generalize (a h block 15) = v2
  generalize (e h block 12) = v3
  generalize (e h block 13) = v4
  generalize (e h block 14) = v5
  generalize (e h block 15) = v6
  generalize (word block 15) = v7
  ac_rfl

theorem e16 (h : BitVecState) (block : Array Bool) :
    (e h block 16) = (((~~~(e h block 15)) &&& (e h block 13)) + ((e h block 14) &&& (e h block 15)) + (((e h block 15)).rotateLeft 21 ^^^ ((e h block 15)).rotateLeft 26 ^^^ ((e h block 15)).rotateLeft 7) + 0xc19bf174 + (a h block 12) + (e h block 12) + (word block 15)) := by
  refine (eWord_succ h ((schedule block).map UInt32.toBitVec) 15).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 12) + ((e h block 12) + bitVecBigSigma1 (e h block 15) + bitVecChoice (e h block 15) (e h block 14) (e h block 13) + 0xc19bf174 + (word block 15)) = (((~~~(e h block 15)) &&& (e h block 13)) + ((e h block 14) &&& (e h block 15)) + (((e h block 15)).rotateLeft 21 ^^^ ((e h block 15)).rotateLeft 26 ^^^ ((e h block 15)).rotateLeft 7) + 0xc19bf174 + (a h block 12) + (e h block 12) + (word block 15))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]
  generalize (a h block 12) = v0
  generalize (e h block 12) = v1
  generalize (e h block 13) = v2
  generalize (e h block 14) = v3
  generalize (e h block 15) = v4
  generalize (word block 15) = v5
  ac_rfl

theorem a17 (h : BitVecState) (block : Array Bool) :
    (a h block 17) = (((~~~(e h block 16)) &&& (e h block 14)) + ((e h block 15) &&& (e h block 16)) + ((((a h block 14) ^^^ (a h block 15)) &&& (a h block 16)) ^^^ ((a h block 14) &&& (a h block 15))) + (((a h block 16)).rotateLeft 10 ^^^ ((a h block 16)).rotateLeft 19 ^^^ ((a h block 16)).rotateLeft 30) + (((e h block 16)).rotateLeft 21 ^^^ ((e h block 16)).rotateLeft 26 ^^^ ((e h block 16)).rotateLeft 7) + 0xe49b69c1 + (e h block 13) + (word block 16)) := by
  refine (aWord_succ h ((schedule block).map UInt32.toBitVec) 16).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 13) + bitVecBigSigma1 (e h block 16) + bitVecChoice (e h block 16) (e h block 15) (e h block 14) + 0xe49b69c1 + (word block 16)) + (bitVecBigSigma0 (a h block 16) + bitVecMajority (a h block 16) (a h block 15) (a h block 14)) = (((~~~(e h block 16)) &&& (e h block 14)) + ((e h block 15) &&& (e h block 16)) + ((((a h block 14) ^^^ (a h block 15)) &&& (a h block 16)) ^^^ ((a h block 14) &&& (a h block 15))) + (((a h block 16)).rotateLeft 10 ^^^ ((a h block 16)).rotateLeft 19 ^^^ ((a h block 16)).rotateLeft 30) + (((e h block 16)).rotateLeft 21 ^^^ ((e h block 16)).rotateLeft 26 ^^^ ((e h block 16)).rotateLeft 7) + 0xe49b69c1 + (e h block 13) + (word block 16))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]
  generalize (a h block 14) = v0
  generalize (a h block 15) = v1
  generalize (a h block 16) = v2
  generalize (e h block 13) = v3
  generalize (e h block 14) = v4
  generalize (e h block 15) = v5
  generalize (e h block 16) = v6
  generalize (word block 16) = v7
  ac_rfl

theorem e17 (h : BitVecState) (block : Array Bool) :
    (e h block 17) = (((~~~(e h block 16)) &&& (e h block 14)) + ((e h block 15) &&& (e h block 16)) + (((e h block 16)).rotateLeft 21 ^^^ ((e h block 16)).rotateLeft 26 ^^^ ((e h block 16)).rotateLeft 7) + 0xe49b69c1 + (a h block 13) + (e h block 13) + (word block 16)) := by
  refine (eWord_succ h ((schedule block).map UInt32.toBitVec) 16).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 13) + ((e h block 13) + bitVecBigSigma1 (e h block 16) + bitVecChoice (e h block 16) (e h block 15) (e h block 14) + 0xe49b69c1 + (word block 16)) = (((~~~(e h block 16)) &&& (e h block 14)) + ((e h block 15) &&& (e h block 16)) + (((e h block 16)).rotateLeft 21 ^^^ ((e h block 16)).rotateLeft 26 ^^^ ((e h block 16)).rotateLeft 7) + 0xe49b69c1 + (a h block 13) + (e h block 13) + (word block 16))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]
  generalize (a h block 13) = v0
  generalize (e h block 13) = v1
  generalize (e h block 14) = v2
  generalize (e h block 15) = v3
  generalize (e h block 16) = v4
  generalize (word block 16) = v5
  ac_rfl

theorem a18 (h : BitVecState) (block : Array Bool) :
    (a h block 18) = (((~~~(e h block 17)) &&& (e h block 15)) + ((e h block 16) &&& (e h block 17)) + ((((a h block 15) ^^^ (a h block 16)) &&& (a h block 17)) ^^^ ((a h block 15) &&& (a h block 16))) + (((a h block 17)).rotateLeft 10 ^^^ ((a h block 17)).rotateLeft 19 ^^^ ((a h block 17)).rotateLeft 30) + (((e h block 17)).rotateLeft 21 ^^^ ((e h block 17)).rotateLeft 26 ^^^ ((e h block 17)).rotateLeft 7) + 0xefbe4786 + (e h block 14) + (word block 17)) := by
  refine (aWord_succ h ((schedule block).map UInt32.toBitVec) 17).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 14) + bitVecBigSigma1 (e h block 17) + bitVecChoice (e h block 17) (e h block 16) (e h block 15) + 0xefbe4786 + (word block 17)) + (bitVecBigSigma0 (a h block 17) + bitVecMajority (a h block 17) (a h block 16) (a h block 15)) = (((~~~(e h block 17)) &&& (e h block 15)) + ((e h block 16) &&& (e h block 17)) + ((((a h block 15) ^^^ (a h block 16)) &&& (a h block 17)) ^^^ ((a h block 15) &&& (a h block 16))) + (((a h block 17)).rotateLeft 10 ^^^ ((a h block 17)).rotateLeft 19 ^^^ ((a h block 17)).rotateLeft 30) + (((e h block 17)).rotateLeft 21 ^^^ ((e h block 17)).rotateLeft 26 ^^^ ((e h block 17)).rotateLeft 7) + 0xefbe4786 + (e h block 14) + (word block 17))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]
  generalize (a h block 15) = v0
  generalize (a h block 16) = v1
  generalize (a h block 17) = v2
  generalize (e h block 14) = v3
  generalize (e h block 15) = v4
  generalize (e h block 16) = v5
  generalize (e h block 17) = v6
  generalize (word block 17) = v7
  ac_rfl

theorem e18 (h : BitVecState) (block : Array Bool) :
    (e h block 18) = (((~~~(e h block 17)) &&& (e h block 15)) + ((e h block 16) &&& (e h block 17)) + (((e h block 17)).rotateLeft 21 ^^^ ((e h block 17)).rotateLeft 26 ^^^ ((e h block 17)).rotateLeft 7) + 0xefbe4786 + (a h block 14) + (e h block 14) + (word block 17)) := by
  refine (eWord_succ h ((schedule block).map UInt32.toBitVec) 17).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 14) + ((e h block 14) + bitVecBigSigma1 (e h block 17) + bitVecChoice (e h block 17) (e h block 16) (e h block 15) + 0xefbe4786 + (word block 17)) = (((~~~(e h block 17)) &&& (e h block 15)) + ((e h block 16) &&& (e h block 17)) + (((e h block 17)).rotateLeft 21 ^^^ ((e h block 17)).rotateLeft 26 ^^^ ((e h block 17)).rotateLeft 7) + 0xefbe4786 + (a h block 14) + (e h block 14) + (word block 17))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]
  generalize (a h block 14) = v0
  generalize (e h block 14) = v1
  generalize (e h block 15) = v2
  generalize (e h block 16) = v3
  generalize (e h block 17) = v4
  generalize (word block 17) = v5
  ac_rfl

theorem a19 (h : BitVecState) (block : Array Bool) :
    (a h block 19) = (((~~~(e h block 18)) &&& (e h block 16)) + ((e h block 17) &&& (e h block 18)) + ((((a h block 16) ^^^ (a h block 17)) &&& (a h block 18)) ^^^ ((a h block 16) &&& (a h block 17))) + (((a h block 18)).rotateLeft 10 ^^^ ((a h block 18)).rotateLeft 19 ^^^ ((a h block 18)).rotateLeft 30) + (((e h block 18)).rotateLeft 21 ^^^ ((e h block 18)).rotateLeft 26 ^^^ ((e h block 18)).rotateLeft 7) + 0xfc19dc6 + (e h block 15) + (word block 18)) := by
  refine (aWord_succ h ((schedule block).map UInt32.toBitVec) 18).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 15) + bitVecBigSigma1 (e h block 18) + bitVecChoice (e h block 18) (e h block 17) (e h block 16) + 0xfc19dc6 + (word block 18)) + (bitVecBigSigma0 (a h block 18) + bitVecMajority (a h block 18) (a h block 17) (a h block 16)) = (((~~~(e h block 18)) &&& (e h block 16)) + ((e h block 17) &&& (e h block 18)) + ((((a h block 16) ^^^ (a h block 17)) &&& (a h block 18)) ^^^ ((a h block 16) &&& (a h block 17))) + (((a h block 18)).rotateLeft 10 ^^^ ((a h block 18)).rotateLeft 19 ^^^ ((a h block 18)).rotateLeft 30) + (((e h block 18)).rotateLeft 21 ^^^ ((e h block 18)).rotateLeft 26 ^^^ ((e h block 18)).rotateLeft 7) + 0xfc19dc6 + (e h block 15) + (word block 18))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]
  generalize (a h block 16) = v0
  generalize (a h block 17) = v1
  generalize (a h block 18) = v2
  generalize (e h block 15) = v3
  generalize (e h block 16) = v4
  generalize (e h block 17) = v5
  generalize (e h block 18) = v6
  generalize (word block 18) = v7
  ac_rfl

theorem e19 (h : BitVecState) (block : Array Bool) :
    (e h block 19) = (((~~~(e h block 18)) &&& (e h block 16)) + ((e h block 17) &&& (e h block 18)) + (((e h block 18)).rotateLeft 21 ^^^ ((e h block 18)).rotateLeft 26 ^^^ ((e h block 18)).rotateLeft 7) + 0xfc19dc6 + (a h block 15) + (e h block 15) + (word block 18)) := by
  refine (eWord_succ h ((schedule block).map UInt32.toBitVec) 18).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 15) + ((e h block 15) + bitVecBigSigma1 (e h block 18) + bitVecChoice (e h block 18) (e h block 17) (e h block 16) + 0xfc19dc6 + (word block 18)) = (((~~~(e h block 18)) &&& (e h block 16)) + ((e h block 17) &&& (e h block 18)) + (((e h block 18)).rotateLeft 21 ^^^ ((e h block 18)).rotateLeft 26 ^^^ ((e h block 18)).rotateLeft 7) + 0xfc19dc6 + (a h block 15) + (e h block 15) + (word block 18))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]
  generalize (a h block 15) = v0
  generalize (e h block 15) = v1
  generalize (e h block 16) = v2
  generalize (e h block 17) = v3
  generalize (e h block 18) = v4
  generalize (word block 18) = v5
  ac_rfl

theorem a20 (h : BitVecState) (block : Array Bool) :
    (a h block 20) = (((~~~(e h block 19)) &&& (e h block 17)) + ((e h block 18) &&& (e h block 19)) + ((((a h block 17) ^^^ (a h block 18)) &&& (a h block 19)) ^^^ ((a h block 17) &&& (a h block 18))) + (((a h block 19)).rotateLeft 10 ^^^ ((a h block 19)).rotateLeft 19 ^^^ ((a h block 19)).rotateLeft 30) + (((e h block 19)).rotateLeft 21 ^^^ ((e h block 19)).rotateLeft 26 ^^^ ((e h block 19)).rotateLeft 7) + 0x240ca1cc + (e h block 16) + (word block 19)) := by
  refine (aWord_succ h ((schedule block).map UInt32.toBitVec) 19).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 16) + bitVecBigSigma1 (e h block 19) + bitVecChoice (e h block 19) (e h block 18) (e h block 17) + 0x240ca1cc + (word block 19)) + (bitVecBigSigma0 (a h block 19) + bitVecMajority (a h block 19) (a h block 18) (a h block 17)) = (((~~~(e h block 19)) &&& (e h block 17)) + ((e h block 18) &&& (e h block 19)) + ((((a h block 17) ^^^ (a h block 18)) &&& (a h block 19)) ^^^ ((a h block 17) &&& (a h block 18))) + (((a h block 19)).rotateLeft 10 ^^^ ((a h block 19)).rotateLeft 19 ^^^ ((a h block 19)).rotateLeft 30) + (((e h block 19)).rotateLeft 21 ^^^ ((e h block 19)).rotateLeft 26 ^^^ ((e h block 19)).rotateLeft 7) + 0x240ca1cc + (e h block 16) + (word block 19))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]
  generalize (a h block 17) = v0
  generalize (a h block 18) = v1
  generalize (a h block 19) = v2
  generalize (e h block 16) = v3
  generalize (e h block 17) = v4
  generalize (e h block 18) = v5
  generalize (e h block 19) = v6
  generalize (word block 19) = v7
  ac_rfl

theorem e20 (h : BitVecState) (block : Array Bool) :
    (e h block 20) = (((~~~(e h block 19)) &&& (e h block 17)) + ((e h block 18) &&& (e h block 19)) + (((e h block 19)).rotateLeft 21 ^^^ ((e h block 19)).rotateLeft 26 ^^^ ((e h block 19)).rotateLeft 7) + 0x240ca1cc + (a h block 16) + (e h block 16) + (word block 19)) := by
  refine (eWord_succ h ((schedule block).map UInt32.toBitVec) 19).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 16) + ((e h block 16) + bitVecBigSigma1 (e h block 19) + bitVecChoice (e h block 19) (e h block 18) (e h block 17) + 0x240ca1cc + (word block 19)) = (((~~~(e h block 19)) &&& (e h block 17)) + ((e h block 18) &&& (e h block 19)) + (((e h block 19)).rotateLeft 21 ^^^ ((e h block 19)).rotateLeft 26 ^^^ ((e h block 19)).rotateLeft 7) + 0x240ca1cc + (a h block 16) + (e h block 16) + (word block 19))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]
  generalize (a h block 16) = v0
  generalize (e h block 16) = v1
  generalize (e h block 17) = v2
  generalize (e h block 18) = v3
  generalize (e h block 19) = v4
  generalize (word block 19) = v5
  ac_rfl

theorem a21 (h : BitVecState) (block : Array Bool) :
    (a h block 21) = (((~~~(e h block 20)) &&& (e h block 18)) + ((e h block 19) &&& (e h block 20)) + ((((a h block 18) ^^^ (a h block 19)) &&& (a h block 20)) ^^^ ((a h block 18) &&& (a h block 19))) + (((a h block 20)).rotateLeft 10 ^^^ ((a h block 20)).rotateLeft 19 ^^^ ((a h block 20)).rotateLeft 30) + (((e h block 20)).rotateLeft 21 ^^^ ((e h block 20)).rotateLeft 26 ^^^ ((e h block 20)).rotateLeft 7) + 0x2de92c6f + (e h block 17) + (word block 20)) := by
  refine (aWord_succ h ((schedule block).map UInt32.toBitVec) 20).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 17) + bitVecBigSigma1 (e h block 20) + bitVecChoice (e h block 20) (e h block 19) (e h block 18) + 0x2de92c6f + (word block 20)) + (bitVecBigSigma0 (a h block 20) + bitVecMajority (a h block 20) (a h block 19) (a h block 18)) = (((~~~(e h block 20)) &&& (e h block 18)) + ((e h block 19) &&& (e h block 20)) + ((((a h block 18) ^^^ (a h block 19)) &&& (a h block 20)) ^^^ ((a h block 18) &&& (a h block 19))) + (((a h block 20)).rotateLeft 10 ^^^ ((a h block 20)).rotateLeft 19 ^^^ ((a h block 20)).rotateLeft 30) + (((e h block 20)).rotateLeft 21 ^^^ ((e h block 20)).rotateLeft 26 ^^^ ((e h block 20)).rotateLeft 7) + 0x2de92c6f + (e h block 17) + (word block 20))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]
  generalize (a h block 18) = v0
  generalize (a h block 19) = v1
  generalize (a h block 20) = v2
  generalize (e h block 17) = v3
  generalize (e h block 18) = v4
  generalize (e h block 19) = v5
  generalize (e h block 20) = v6
  generalize (word block 20) = v7
  ac_rfl

theorem e21 (h : BitVecState) (block : Array Bool) :
    (e h block 21) = (((~~~(e h block 20)) &&& (e h block 18)) + ((e h block 19) &&& (e h block 20)) + (((e h block 20)).rotateLeft 21 ^^^ ((e h block 20)).rotateLeft 26 ^^^ ((e h block 20)).rotateLeft 7) + 0x2de92c6f + (a h block 17) + (e h block 17) + (word block 20)) := by
  refine (eWord_succ h ((schedule block).map UInt32.toBitVec) 20).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 17) + ((e h block 17) + bitVecBigSigma1 (e h block 20) + bitVecChoice (e h block 20) (e h block 19) (e h block 18) + 0x2de92c6f + (word block 20)) = (((~~~(e h block 20)) &&& (e h block 18)) + ((e h block 19) &&& (e h block 20)) + (((e h block 20)).rotateLeft 21 ^^^ ((e h block 20)).rotateLeft 26 ^^^ ((e h block 20)).rotateLeft 7) + 0x2de92c6f + (a h block 17) + (e h block 17) + (word block 20))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]
  generalize (a h block 17) = v0
  generalize (e h block 17) = v1
  generalize (e h block 18) = v2
  generalize (e h block 19) = v3
  generalize (e h block 20) = v4
  generalize (word block 20) = v5
  ac_rfl

theorem a22 (h : BitVecState) (block : Array Bool) :
    (a h block 22) = (((~~~(e h block 21)) &&& (e h block 19)) + ((e h block 20) &&& (e h block 21)) + ((((a h block 19) ^^^ (a h block 20)) &&& (a h block 21)) ^^^ ((a h block 19) &&& (a h block 20))) + (((a h block 21)).rotateLeft 10 ^^^ ((a h block 21)).rotateLeft 19 ^^^ ((a h block 21)).rotateLeft 30) + (((e h block 21)).rotateLeft 21 ^^^ ((e h block 21)).rotateLeft 26 ^^^ ((e h block 21)).rotateLeft 7) + 0x4a7484aa + (e h block 18) + (word block 21)) := by
  refine (aWord_succ h ((schedule block).map UInt32.toBitVec) 21).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 18) + bitVecBigSigma1 (e h block 21) + bitVecChoice (e h block 21) (e h block 20) (e h block 19) + 0x4a7484aa + (word block 21)) + (bitVecBigSigma0 (a h block 21) + bitVecMajority (a h block 21) (a h block 20) (a h block 19)) = (((~~~(e h block 21)) &&& (e h block 19)) + ((e h block 20) &&& (e h block 21)) + ((((a h block 19) ^^^ (a h block 20)) &&& (a h block 21)) ^^^ ((a h block 19) &&& (a h block 20))) + (((a h block 21)).rotateLeft 10 ^^^ ((a h block 21)).rotateLeft 19 ^^^ ((a h block 21)).rotateLeft 30) + (((e h block 21)).rotateLeft 21 ^^^ ((e h block 21)).rotateLeft 26 ^^^ ((e h block 21)).rotateLeft 7) + 0x4a7484aa + (e h block 18) + (word block 21))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]
  generalize (a h block 19) = v0
  generalize (a h block 20) = v1
  generalize (a h block 21) = v2
  generalize (e h block 18) = v3
  generalize (e h block 19) = v4
  generalize (e h block 20) = v5
  generalize (e h block 21) = v6
  generalize (word block 21) = v7
  ac_rfl

theorem e22 (h : BitVecState) (block : Array Bool) :
    (e h block 22) = (((~~~(e h block 21)) &&& (e h block 19)) + ((e h block 20) &&& (e h block 21)) + (((e h block 21)).rotateLeft 21 ^^^ ((e h block 21)).rotateLeft 26 ^^^ ((e h block 21)).rotateLeft 7) + 0x4a7484aa + (a h block 18) + (e h block 18) + (word block 21)) := by
  refine (eWord_succ h ((schedule block).map UInt32.toBitVec) 21).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 18) + ((e h block 18) + bitVecBigSigma1 (e h block 21) + bitVecChoice (e h block 21) (e h block 20) (e h block 19) + 0x4a7484aa + (word block 21)) = (((~~~(e h block 21)) &&& (e h block 19)) + ((e h block 20) &&& (e h block 21)) + (((e h block 21)).rotateLeft 21 ^^^ ((e h block 21)).rotateLeft 26 ^^^ ((e h block 21)).rotateLeft 7) + 0x4a7484aa + (a h block 18) + (e h block 18) + (word block 21))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]
  generalize (a h block 18) = v0
  generalize (e h block 18) = v1
  generalize (e h block 19) = v2
  generalize (e h block 20) = v3
  generalize (e h block 21) = v4
  generalize (word block 21) = v5
  ac_rfl

theorem a23 (h : BitVecState) (block : Array Bool) :
    (a h block 23) = (((~~~(e h block 22)) &&& (e h block 20)) + ((e h block 21) &&& (e h block 22)) + ((((a h block 20) ^^^ (a h block 21)) &&& (a h block 22)) ^^^ ((a h block 20) &&& (a h block 21))) + (((a h block 22)).rotateLeft 10 ^^^ ((a h block 22)).rotateLeft 19 ^^^ ((a h block 22)).rotateLeft 30) + (((e h block 22)).rotateLeft 21 ^^^ ((e h block 22)).rotateLeft 26 ^^^ ((e h block 22)).rotateLeft 7) + 0x5cb0a9dc + (e h block 19) + (word block 22)) := by
  refine (aWord_succ h ((schedule block).map UInt32.toBitVec) 22).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 19) + bitVecBigSigma1 (e h block 22) + bitVecChoice (e h block 22) (e h block 21) (e h block 20) + 0x5cb0a9dc + (word block 22)) + (bitVecBigSigma0 (a h block 22) + bitVecMajority (a h block 22) (a h block 21) (a h block 20)) = (((~~~(e h block 22)) &&& (e h block 20)) + ((e h block 21) &&& (e h block 22)) + ((((a h block 20) ^^^ (a h block 21)) &&& (a h block 22)) ^^^ ((a h block 20) &&& (a h block 21))) + (((a h block 22)).rotateLeft 10 ^^^ ((a h block 22)).rotateLeft 19 ^^^ ((a h block 22)).rotateLeft 30) + (((e h block 22)).rotateLeft 21 ^^^ ((e h block 22)).rotateLeft 26 ^^^ ((e h block 22)).rotateLeft 7) + 0x5cb0a9dc + (e h block 19) + (word block 22))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]
  generalize (a h block 20) = v0
  generalize (a h block 21) = v1
  generalize (a h block 22) = v2
  generalize (e h block 19) = v3
  generalize (e h block 20) = v4
  generalize (e h block 21) = v5
  generalize (e h block 22) = v6
  generalize (word block 22) = v7
  ac_rfl

theorem e23 (h : BitVecState) (block : Array Bool) :
    (e h block 23) = (((~~~(e h block 22)) &&& (e h block 20)) + ((e h block 21) &&& (e h block 22)) + (((e h block 22)).rotateLeft 21 ^^^ ((e h block 22)).rotateLeft 26 ^^^ ((e h block 22)).rotateLeft 7) + 0x5cb0a9dc + (a h block 19) + (e h block 19) + (word block 22)) := by
  refine (eWord_succ h ((schedule block).map UInt32.toBitVec) 22).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 19) + ((e h block 19) + bitVecBigSigma1 (e h block 22) + bitVecChoice (e h block 22) (e h block 21) (e h block 20) + 0x5cb0a9dc + (word block 22)) = (((~~~(e h block 22)) &&& (e h block 20)) + ((e h block 21) &&& (e h block 22)) + (((e h block 22)).rotateLeft 21 ^^^ ((e h block 22)).rotateLeft 26 ^^^ ((e h block 22)).rotateLeft 7) + 0x5cb0a9dc + (a h block 19) + (e h block 19) + (word block 22))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]
  generalize (a h block 19) = v0
  generalize (e h block 19) = v1
  generalize (e h block 20) = v2
  generalize (e h block 21) = v3
  generalize (e h block 22) = v4
  generalize (word block 22) = v5
  ac_rfl

theorem a24 (h : BitVecState) (block : Array Bool) :
    (a h block 24) = (((~~~(e h block 23)) &&& (e h block 21)) + ((e h block 22) &&& (e h block 23)) + ((((a h block 21) ^^^ (a h block 22)) &&& (a h block 23)) ^^^ ((a h block 21) &&& (a h block 22))) + (((a h block 23)).rotateLeft 10 ^^^ ((a h block 23)).rotateLeft 19 ^^^ ((a h block 23)).rotateLeft 30) + (((e h block 23)).rotateLeft 21 ^^^ ((e h block 23)).rotateLeft 26 ^^^ ((e h block 23)).rotateLeft 7) + 0x76f988da + (e h block 20) + (word block 23)) := by
  refine (aWord_succ h ((schedule block).map UInt32.toBitVec) 23).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 20) + bitVecBigSigma1 (e h block 23) + bitVecChoice (e h block 23) (e h block 22) (e h block 21) + 0x76f988da + (word block 23)) + (bitVecBigSigma0 (a h block 23) + bitVecMajority (a h block 23) (a h block 22) (a h block 21)) = (((~~~(e h block 23)) &&& (e h block 21)) + ((e h block 22) &&& (e h block 23)) + ((((a h block 21) ^^^ (a h block 22)) &&& (a h block 23)) ^^^ ((a h block 21) &&& (a h block 22))) + (((a h block 23)).rotateLeft 10 ^^^ ((a h block 23)).rotateLeft 19 ^^^ ((a h block 23)).rotateLeft 30) + (((e h block 23)).rotateLeft 21 ^^^ ((e h block 23)).rotateLeft 26 ^^^ ((e h block 23)).rotateLeft 7) + 0x76f988da + (e h block 20) + (word block 23))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]
  generalize (a h block 21) = v0
  generalize (a h block 22) = v1
  generalize (a h block 23) = v2
  generalize (e h block 20) = v3
  generalize (e h block 21) = v4
  generalize (e h block 22) = v5
  generalize (e h block 23) = v6
  generalize (word block 23) = v7
  ac_rfl

theorem e24 (h : BitVecState) (block : Array Bool) :
    (e h block 24) = (((~~~(e h block 23)) &&& (e h block 21)) + ((e h block 22) &&& (e h block 23)) + (((e h block 23)).rotateLeft 21 ^^^ ((e h block 23)).rotateLeft 26 ^^^ ((e h block 23)).rotateLeft 7) + 0x76f988da + (a h block 20) + (e h block 20) + (word block 23)) := by
  refine (eWord_succ h ((schedule block).map UInt32.toBitVec) 23).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 20) + ((e h block 20) + bitVecBigSigma1 (e h block 23) + bitVecChoice (e h block 23) (e h block 22) (e h block 21) + 0x76f988da + (word block 23)) = (((~~~(e h block 23)) &&& (e h block 21)) + ((e h block 22) &&& (e h block 23)) + (((e h block 23)).rotateLeft 21 ^^^ ((e h block 23)).rotateLeft 26 ^^^ ((e h block 23)).rotateLeft 7) + 0x76f988da + (a h block 20) + (e h block 20) + (word block 23))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]
  generalize (a h block 20) = v0
  generalize (e h block 20) = v1
  generalize (e h block 21) = v2
  generalize (e h block 22) = v3
  generalize (e h block 23) = v4
  generalize (word block 23) = v5
  ac_rfl

theorem a25 (h : BitVecState) (block : Array Bool) :
    (a h block 25) = (((~~~(e h block 24)) &&& (e h block 22)) + ((e h block 23) &&& (e h block 24)) + ((((a h block 22) ^^^ (a h block 23)) &&& (a h block 24)) ^^^ ((a h block 22) &&& (a h block 23))) + (((a h block 24)).rotateLeft 10 ^^^ ((a h block 24)).rotateLeft 19 ^^^ ((a h block 24)).rotateLeft 30) + (((e h block 24)).rotateLeft 21 ^^^ ((e h block 24)).rotateLeft 26 ^^^ ((e h block 24)).rotateLeft 7) + 0x983e5152 + (e h block 21) + (word block 24)) := by
  refine (aWord_succ h ((schedule block).map UInt32.toBitVec) 24).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 21) + bitVecBigSigma1 (e h block 24) + bitVecChoice (e h block 24) (e h block 23) (e h block 22) + 0x983e5152 + (word block 24)) + (bitVecBigSigma0 (a h block 24) + bitVecMajority (a h block 24) (a h block 23) (a h block 22)) = (((~~~(e h block 24)) &&& (e h block 22)) + ((e h block 23) &&& (e h block 24)) + ((((a h block 22) ^^^ (a h block 23)) &&& (a h block 24)) ^^^ ((a h block 22) &&& (a h block 23))) + (((a h block 24)).rotateLeft 10 ^^^ ((a h block 24)).rotateLeft 19 ^^^ ((a h block 24)).rotateLeft 30) + (((e h block 24)).rotateLeft 21 ^^^ ((e h block 24)).rotateLeft 26 ^^^ ((e h block 24)).rotateLeft 7) + 0x983e5152 + (e h block 21) + (word block 24))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]
  generalize (a h block 22) = v0
  generalize (a h block 23) = v1
  generalize (a h block 24) = v2
  generalize (e h block 21) = v3
  generalize (e h block 22) = v4
  generalize (e h block 23) = v5
  generalize (e h block 24) = v6
  generalize (word block 24) = v7
  ac_rfl

theorem e25 (h : BitVecState) (block : Array Bool) :
    (e h block 25) = (((~~~(e h block 24)) &&& (e h block 22)) + ((e h block 23) &&& (e h block 24)) + (((e h block 24)).rotateLeft 21 ^^^ ((e h block 24)).rotateLeft 26 ^^^ ((e h block 24)).rotateLeft 7) + 0x983e5152 + (a h block 21) + (e h block 21) + (word block 24)) := by
  refine (eWord_succ h ((schedule block).map UInt32.toBitVec) 24).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 21) + ((e h block 21) + bitVecBigSigma1 (e h block 24) + bitVecChoice (e h block 24) (e h block 23) (e h block 22) + 0x983e5152 + (word block 24)) = (((~~~(e h block 24)) &&& (e h block 22)) + ((e h block 23) &&& (e h block 24)) + (((e h block 24)).rotateLeft 21 ^^^ ((e h block 24)).rotateLeft 26 ^^^ ((e h block 24)).rotateLeft 7) + 0x983e5152 + (a h block 21) + (e h block 21) + (word block 24))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]
  generalize (a h block 21) = v0
  generalize (e h block 21) = v1
  generalize (e h block 22) = v2
  generalize (e h block 23) = v3
  generalize (e h block 24) = v4
  generalize (word block 24) = v5
  ac_rfl

theorem a26 (h : BitVecState) (block : Array Bool) :
    (a h block 26) = (((~~~(e h block 25)) &&& (e h block 23)) + ((e h block 24) &&& (e h block 25)) + ((((a h block 23) ^^^ (a h block 24)) &&& (a h block 25)) ^^^ ((a h block 23) &&& (a h block 24))) + (((a h block 25)).rotateLeft 10 ^^^ ((a h block 25)).rotateLeft 19 ^^^ ((a h block 25)).rotateLeft 30) + (((e h block 25)).rotateLeft 21 ^^^ ((e h block 25)).rotateLeft 26 ^^^ ((e h block 25)).rotateLeft 7) + 0xa831c66d + (e h block 22) + (word block 25)) := by
  refine (aWord_succ h ((schedule block).map UInt32.toBitVec) 25).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 22) + bitVecBigSigma1 (e h block 25) + bitVecChoice (e h block 25) (e h block 24) (e h block 23) + 0xa831c66d + (word block 25)) + (bitVecBigSigma0 (a h block 25) + bitVecMajority (a h block 25) (a h block 24) (a h block 23)) = (((~~~(e h block 25)) &&& (e h block 23)) + ((e h block 24) &&& (e h block 25)) + ((((a h block 23) ^^^ (a h block 24)) &&& (a h block 25)) ^^^ ((a h block 23) &&& (a h block 24))) + (((a h block 25)).rotateLeft 10 ^^^ ((a h block 25)).rotateLeft 19 ^^^ ((a h block 25)).rotateLeft 30) + (((e h block 25)).rotateLeft 21 ^^^ ((e h block 25)).rotateLeft 26 ^^^ ((e h block 25)).rotateLeft 7) + 0xa831c66d + (e h block 22) + (word block 25))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]
  generalize (a h block 23) = v0
  generalize (a h block 24) = v1
  generalize (a h block 25) = v2
  generalize (e h block 22) = v3
  generalize (e h block 23) = v4
  generalize (e h block 24) = v5
  generalize (e h block 25) = v6
  generalize (word block 25) = v7
  ac_rfl

theorem e26 (h : BitVecState) (block : Array Bool) :
    (e h block 26) = (((~~~(e h block 25)) &&& (e h block 23)) + ((e h block 24) &&& (e h block 25)) + (((e h block 25)).rotateLeft 21 ^^^ ((e h block 25)).rotateLeft 26 ^^^ ((e h block 25)).rotateLeft 7) + 0xa831c66d + (a h block 22) + (e h block 22) + (word block 25)) := by
  refine (eWord_succ h ((schedule block).map UInt32.toBitVec) 25).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 22) + ((e h block 22) + bitVecBigSigma1 (e h block 25) + bitVecChoice (e h block 25) (e h block 24) (e h block 23) + 0xa831c66d + (word block 25)) = (((~~~(e h block 25)) &&& (e h block 23)) + ((e h block 24) &&& (e h block 25)) + (((e h block 25)).rotateLeft 21 ^^^ ((e h block 25)).rotateLeft 26 ^^^ ((e h block 25)).rotateLeft 7) + 0xa831c66d + (a h block 22) + (e h block 22) + (word block 25))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]
  generalize (a h block 22) = v0
  generalize (e h block 22) = v1
  generalize (e h block 23) = v2
  generalize (e h block 24) = v3
  generalize (e h block 25) = v4
  generalize (word block 25) = v5
  ac_rfl

theorem a27 (h : BitVecState) (block : Array Bool) :
    (a h block 27) = (((~~~(e h block 26)) &&& (e h block 24)) + ((e h block 25) &&& (e h block 26)) + ((((a h block 24) ^^^ (a h block 25)) &&& (a h block 26)) ^^^ ((a h block 24) &&& (a h block 25))) + (((a h block 26)).rotateLeft 10 ^^^ ((a h block 26)).rotateLeft 19 ^^^ ((a h block 26)).rotateLeft 30) + (((e h block 26)).rotateLeft 21 ^^^ ((e h block 26)).rotateLeft 26 ^^^ ((e h block 26)).rotateLeft 7) + 0xb00327c8 + (e h block 23) + (word block 26)) := by
  refine (aWord_succ h ((schedule block).map UInt32.toBitVec) 26).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 23) + bitVecBigSigma1 (e h block 26) + bitVecChoice (e h block 26) (e h block 25) (e h block 24) + 0xb00327c8 + (word block 26)) + (bitVecBigSigma0 (a h block 26) + bitVecMajority (a h block 26) (a h block 25) (a h block 24)) = (((~~~(e h block 26)) &&& (e h block 24)) + ((e h block 25) &&& (e h block 26)) + ((((a h block 24) ^^^ (a h block 25)) &&& (a h block 26)) ^^^ ((a h block 24) &&& (a h block 25))) + (((a h block 26)).rotateLeft 10 ^^^ ((a h block 26)).rotateLeft 19 ^^^ ((a h block 26)).rotateLeft 30) + (((e h block 26)).rotateLeft 21 ^^^ ((e h block 26)).rotateLeft 26 ^^^ ((e h block 26)).rotateLeft 7) + 0xb00327c8 + (e h block 23) + (word block 26))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]
  generalize (a h block 24) = v0
  generalize (a h block 25) = v1
  generalize (a h block 26) = v2
  generalize (e h block 23) = v3
  generalize (e h block 24) = v4
  generalize (e h block 25) = v5
  generalize (e h block 26) = v6
  generalize (word block 26) = v7
  ac_rfl

theorem e27 (h : BitVecState) (block : Array Bool) :
    (e h block 27) = (((~~~(e h block 26)) &&& (e h block 24)) + ((e h block 25) &&& (e h block 26)) + (((e h block 26)).rotateLeft 21 ^^^ ((e h block 26)).rotateLeft 26 ^^^ ((e h block 26)).rotateLeft 7) + 0xb00327c8 + (a h block 23) + (e h block 23) + (word block 26)) := by
  refine (eWord_succ h ((schedule block).map UInt32.toBitVec) 26).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 23) + ((e h block 23) + bitVecBigSigma1 (e h block 26) + bitVecChoice (e h block 26) (e h block 25) (e h block 24) + 0xb00327c8 + (word block 26)) = (((~~~(e h block 26)) &&& (e h block 24)) + ((e h block 25) &&& (e h block 26)) + (((e h block 26)).rotateLeft 21 ^^^ ((e h block 26)).rotateLeft 26 ^^^ ((e h block 26)).rotateLeft 7) + 0xb00327c8 + (a h block 23) + (e h block 23) + (word block 26))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]
  generalize (a h block 23) = v0
  generalize (e h block 23) = v1
  generalize (e h block 24) = v2
  generalize (e h block 25) = v3
  generalize (e h block 26) = v4
  generalize (word block 26) = v5
  ac_rfl

theorem a28 (h : BitVecState) (block : Array Bool) :
    (a h block 28) = (((~~~(e h block 27)) &&& (e h block 25)) + ((e h block 26) &&& (e h block 27)) + ((((a h block 25) ^^^ (a h block 26)) &&& (a h block 27)) ^^^ ((a h block 25) &&& (a h block 26))) + (((a h block 27)).rotateLeft 10 ^^^ ((a h block 27)).rotateLeft 19 ^^^ ((a h block 27)).rotateLeft 30) + (((e h block 27)).rotateLeft 21 ^^^ ((e h block 27)).rotateLeft 26 ^^^ ((e h block 27)).rotateLeft 7) + 0xbf597fc7 + (e h block 24) + (word block 27)) := by
  refine (aWord_succ h ((schedule block).map UInt32.toBitVec) 27).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 24) + bitVecBigSigma1 (e h block 27) + bitVecChoice (e h block 27) (e h block 26) (e h block 25) + 0xbf597fc7 + (word block 27)) + (bitVecBigSigma0 (a h block 27) + bitVecMajority (a h block 27) (a h block 26) (a h block 25)) = (((~~~(e h block 27)) &&& (e h block 25)) + ((e h block 26) &&& (e h block 27)) + ((((a h block 25) ^^^ (a h block 26)) &&& (a h block 27)) ^^^ ((a h block 25) &&& (a h block 26))) + (((a h block 27)).rotateLeft 10 ^^^ ((a h block 27)).rotateLeft 19 ^^^ ((a h block 27)).rotateLeft 30) + (((e h block 27)).rotateLeft 21 ^^^ ((e h block 27)).rotateLeft 26 ^^^ ((e h block 27)).rotateLeft 7) + 0xbf597fc7 + (e h block 24) + (word block 27))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]
  generalize (a h block 25) = v0
  generalize (a h block 26) = v1
  generalize (a h block 27) = v2
  generalize (e h block 24) = v3
  generalize (e h block 25) = v4
  generalize (e h block 26) = v5
  generalize (e h block 27) = v6
  generalize (word block 27) = v7
  ac_rfl

theorem e28 (h : BitVecState) (block : Array Bool) :
    (e h block 28) = (((~~~(e h block 27)) &&& (e h block 25)) + ((e h block 26) &&& (e h block 27)) + (((e h block 27)).rotateLeft 21 ^^^ ((e h block 27)).rotateLeft 26 ^^^ ((e h block 27)).rotateLeft 7) + 0xbf597fc7 + (a h block 24) + (e h block 24) + (word block 27)) := by
  refine (eWord_succ h ((schedule block).map UInt32.toBitVec) 27).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 24) + ((e h block 24) + bitVecBigSigma1 (e h block 27) + bitVecChoice (e h block 27) (e h block 26) (e h block 25) + 0xbf597fc7 + (word block 27)) = (((~~~(e h block 27)) &&& (e h block 25)) + ((e h block 26) &&& (e h block 27)) + (((e h block 27)).rotateLeft 21 ^^^ ((e h block 27)).rotateLeft 26 ^^^ ((e h block 27)).rotateLeft 7) + 0xbf597fc7 + (a h block 24) + (e h block 24) + (word block 27))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]
  generalize (a h block 24) = v0
  generalize (e h block 24) = v1
  generalize (e h block 25) = v2
  generalize (e h block 26) = v3
  generalize (e h block 27) = v4
  generalize (word block 27) = v5
  ac_rfl

theorem a29 (h : BitVecState) (block : Array Bool) :
    (a h block 29) = (((~~~(e h block 28)) &&& (e h block 26)) + ((e h block 27) &&& (e h block 28)) + ((((a h block 26) ^^^ (a h block 27)) &&& (a h block 28)) ^^^ ((a h block 26) &&& (a h block 27))) + (((a h block 28)).rotateLeft 10 ^^^ ((a h block 28)).rotateLeft 19 ^^^ ((a h block 28)).rotateLeft 30) + (((e h block 28)).rotateLeft 21 ^^^ ((e h block 28)).rotateLeft 26 ^^^ ((e h block 28)).rotateLeft 7) + 0xc6e00bf3 + (e h block 25) + (word block 28)) := by
  refine (aWord_succ h ((schedule block).map UInt32.toBitVec) 28).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 25) + bitVecBigSigma1 (e h block 28) + bitVecChoice (e h block 28) (e h block 27) (e h block 26) + 0xc6e00bf3 + (word block 28)) + (bitVecBigSigma0 (a h block 28) + bitVecMajority (a h block 28) (a h block 27) (a h block 26)) = (((~~~(e h block 28)) &&& (e h block 26)) + ((e h block 27) &&& (e h block 28)) + ((((a h block 26) ^^^ (a h block 27)) &&& (a h block 28)) ^^^ ((a h block 26) &&& (a h block 27))) + (((a h block 28)).rotateLeft 10 ^^^ ((a h block 28)).rotateLeft 19 ^^^ ((a h block 28)).rotateLeft 30) + (((e h block 28)).rotateLeft 21 ^^^ ((e h block 28)).rotateLeft 26 ^^^ ((e h block 28)).rotateLeft 7) + 0xc6e00bf3 + (e h block 25) + (word block 28))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]
  generalize (a h block 26) = v0
  generalize (a h block 27) = v1
  generalize (a h block 28) = v2
  generalize (e h block 25) = v3
  generalize (e h block 26) = v4
  generalize (e h block 27) = v5
  generalize (e h block 28) = v6
  generalize (word block 28) = v7
  ac_rfl

theorem e29 (h : BitVecState) (block : Array Bool) :
    (e h block 29) = (((~~~(e h block 28)) &&& (e h block 26)) + ((e h block 27) &&& (e h block 28)) + (((e h block 28)).rotateLeft 21 ^^^ ((e h block 28)).rotateLeft 26 ^^^ ((e h block 28)).rotateLeft 7) + 0xc6e00bf3 + (a h block 25) + (e h block 25) + (word block 28)) := by
  refine (eWord_succ h ((schedule block).map UInt32.toBitVec) 28).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 25) + ((e h block 25) + bitVecBigSigma1 (e h block 28) + bitVecChoice (e h block 28) (e h block 27) (e h block 26) + 0xc6e00bf3 + (word block 28)) = (((~~~(e h block 28)) &&& (e h block 26)) + ((e h block 27) &&& (e h block 28)) + (((e h block 28)).rotateLeft 21 ^^^ ((e h block 28)).rotateLeft 26 ^^^ ((e h block 28)).rotateLeft 7) + 0xc6e00bf3 + (a h block 25) + (e h block 25) + (word block 28))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]
  generalize (a h block 25) = v0
  generalize (e h block 25) = v1
  generalize (e h block 26) = v2
  generalize (e h block 27) = v3
  generalize (e h block 28) = v4
  generalize (word block 28) = v5
  ac_rfl

theorem a30 (h : BitVecState) (block : Array Bool) :
    (a h block 30) = (((~~~(e h block 29)) &&& (e h block 27)) + ((e h block 28) &&& (e h block 29)) + ((((a h block 27) ^^^ (a h block 28)) &&& (a h block 29)) ^^^ ((a h block 27) &&& (a h block 28))) + (((a h block 29)).rotateLeft 10 ^^^ ((a h block 29)).rotateLeft 19 ^^^ ((a h block 29)).rotateLeft 30) + (((e h block 29)).rotateLeft 21 ^^^ ((e h block 29)).rotateLeft 26 ^^^ ((e h block 29)).rotateLeft 7) + 0xd5a79147 + (e h block 26) + (word block 29)) := by
  refine (aWord_succ h ((schedule block).map UInt32.toBitVec) 29).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 26) + bitVecBigSigma1 (e h block 29) + bitVecChoice (e h block 29) (e h block 28) (e h block 27) + 0xd5a79147 + (word block 29)) + (bitVecBigSigma0 (a h block 29) + bitVecMajority (a h block 29) (a h block 28) (a h block 27)) = (((~~~(e h block 29)) &&& (e h block 27)) + ((e h block 28) &&& (e h block 29)) + ((((a h block 27) ^^^ (a h block 28)) &&& (a h block 29)) ^^^ ((a h block 27) &&& (a h block 28))) + (((a h block 29)).rotateLeft 10 ^^^ ((a h block 29)).rotateLeft 19 ^^^ ((a h block 29)).rotateLeft 30) + (((e h block 29)).rotateLeft 21 ^^^ ((e h block 29)).rotateLeft 26 ^^^ ((e h block 29)).rotateLeft 7) + 0xd5a79147 + (e h block 26) + (word block 29))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]
  generalize (a h block 27) = v0
  generalize (a h block 28) = v1
  generalize (a h block 29) = v2
  generalize (e h block 26) = v3
  generalize (e h block 27) = v4
  generalize (e h block 28) = v5
  generalize (e h block 29) = v6
  generalize (word block 29) = v7
  ac_rfl

theorem e30 (h : BitVecState) (block : Array Bool) :
    (e h block 30) = (((~~~(e h block 29)) &&& (e h block 27)) + ((e h block 28) &&& (e h block 29)) + (((e h block 29)).rotateLeft 21 ^^^ ((e h block 29)).rotateLeft 26 ^^^ ((e h block 29)).rotateLeft 7) + 0xd5a79147 + (a h block 26) + (e h block 26) + (word block 29)) := by
  refine (eWord_succ h ((schedule block).map UInt32.toBitVec) 29).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 26) + ((e h block 26) + bitVecBigSigma1 (e h block 29) + bitVecChoice (e h block 29) (e h block 28) (e h block 27) + 0xd5a79147 + (word block 29)) = (((~~~(e h block 29)) &&& (e h block 27)) + ((e h block 28) &&& (e h block 29)) + (((e h block 29)).rotateLeft 21 ^^^ ((e h block 29)).rotateLeft 26 ^^^ ((e h block 29)).rotateLeft 7) + 0xd5a79147 + (a h block 26) + (e h block 26) + (word block 29))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]
  generalize (a h block 26) = v0
  generalize (e h block 26) = v1
  generalize (e h block 27) = v2
  generalize (e h block 28) = v3
  generalize (e h block 29) = v4
  generalize (word block 29) = v5
  ac_rfl

theorem a31 (h : BitVecState) (block : Array Bool) :
    (a h block 31) = (((~~~(e h block 30)) &&& (e h block 28)) + ((e h block 29) &&& (e h block 30)) + ((((a h block 28) ^^^ (a h block 29)) &&& (a h block 30)) ^^^ ((a h block 28) &&& (a h block 29))) + (((a h block 30)).rotateLeft 10 ^^^ ((a h block 30)).rotateLeft 19 ^^^ ((a h block 30)).rotateLeft 30) + (((e h block 30)).rotateLeft 21 ^^^ ((e h block 30)).rotateLeft 26 ^^^ ((e h block 30)).rotateLeft 7) + 0x6ca6351 + (e h block 27) + (word block 30)) := by
  refine (aWord_succ h ((schedule block).map UInt32.toBitVec) 30).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 27) + bitVecBigSigma1 (e h block 30) + bitVecChoice (e h block 30) (e h block 29) (e h block 28) + 0x6ca6351 + (word block 30)) + (bitVecBigSigma0 (a h block 30) + bitVecMajority (a h block 30) (a h block 29) (a h block 28)) = (((~~~(e h block 30)) &&& (e h block 28)) + ((e h block 29) &&& (e h block 30)) + ((((a h block 28) ^^^ (a h block 29)) &&& (a h block 30)) ^^^ ((a h block 28) &&& (a h block 29))) + (((a h block 30)).rotateLeft 10 ^^^ ((a h block 30)).rotateLeft 19 ^^^ ((a h block 30)).rotateLeft 30) + (((e h block 30)).rotateLeft 21 ^^^ ((e h block 30)).rotateLeft 26 ^^^ ((e h block 30)).rotateLeft 7) + 0x6ca6351 + (e h block 27) + (word block 30))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]
  generalize (a h block 28) = v0
  generalize (a h block 29) = v1
  generalize (a h block 30) = v2
  generalize (e h block 27) = v3
  generalize (e h block 28) = v4
  generalize (e h block 29) = v5
  generalize (e h block 30) = v6
  generalize (word block 30) = v7
  ac_rfl

theorem e31 (h : BitVecState) (block : Array Bool) :
    (e h block 31) = (((~~~(e h block 30)) &&& (e h block 28)) + ((e h block 29) &&& (e h block 30)) + (((e h block 30)).rotateLeft 21 ^^^ ((e h block 30)).rotateLeft 26 ^^^ ((e h block 30)).rotateLeft 7) + 0x6ca6351 + (a h block 27) + (e h block 27) + (word block 30)) := by
  refine (eWord_succ h ((schedule block).map UInt32.toBitVec) 30).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 27) + ((e h block 27) + bitVecBigSigma1 (e h block 30) + bitVecChoice (e h block 30) (e h block 29) (e h block 28) + 0x6ca6351 + (word block 30)) = (((~~~(e h block 30)) &&& (e h block 28)) + ((e h block 29) &&& (e h block 30)) + (((e h block 30)).rotateLeft 21 ^^^ ((e h block 30)).rotateLeft 26 ^^^ ((e h block 30)).rotateLeft 7) + 0x6ca6351 + (a h block 27) + (e h block 27) + (word block 30))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]
  generalize (a h block 27) = v0
  generalize (e h block 27) = v1
  generalize (e h block 28) = v2
  generalize (e h block 29) = v3
  generalize (e h block 30) = v4
  generalize (word block 30) = v5
  ac_rfl

theorem a32 (h : BitVecState) (block : Array Bool) :
    (a h block 32) = (((~~~(e h block 31)) &&& (e h block 29)) + ((e h block 30) &&& (e h block 31)) + ((((a h block 29) ^^^ (a h block 30)) &&& (a h block 31)) ^^^ ((a h block 29) &&& (a h block 30))) + (((a h block 31)).rotateLeft 10 ^^^ ((a h block 31)).rotateLeft 19 ^^^ ((a h block 31)).rotateLeft 30) + (((e h block 31)).rotateLeft 21 ^^^ ((e h block 31)).rotateLeft 26 ^^^ ((e h block 31)).rotateLeft 7) + 0x14292967 + (e h block 28) + (word block 31)) := by
  refine (aWord_succ h ((schedule block).map UInt32.toBitVec) 31).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 28) + bitVecBigSigma1 (e h block 31) + bitVecChoice (e h block 31) (e h block 30) (e h block 29) + 0x14292967 + (word block 31)) + (bitVecBigSigma0 (a h block 31) + bitVecMajority (a h block 31) (a h block 30) (a h block 29)) = (((~~~(e h block 31)) &&& (e h block 29)) + ((e h block 30) &&& (e h block 31)) + ((((a h block 29) ^^^ (a h block 30)) &&& (a h block 31)) ^^^ ((a h block 29) &&& (a h block 30))) + (((a h block 31)).rotateLeft 10 ^^^ ((a h block 31)).rotateLeft 19 ^^^ ((a h block 31)).rotateLeft 30) + (((e h block 31)).rotateLeft 21 ^^^ ((e h block 31)).rotateLeft 26 ^^^ ((e h block 31)).rotateLeft 7) + 0x14292967 + (e h block 28) + (word block 31))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]
  generalize (a h block 29) = v0
  generalize (a h block 30) = v1
  generalize (a h block 31) = v2
  generalize (e h block 28) = v3
  generalize (e h block 29) = v4
  generalize (e h block 30) = v5
  generalize (e h block 31) = v6
  generalize (word block 31) = v7
  ac_rfl

theorem e32 (h : BitVecState) (block : Array Bool) :
    (e h block 32) = (((~~~(e h block 31)) &&& (e h block 29)) + ((e h block 30) &&& (e h block 31)) + (((e h block 31)).rotateLeft 21 ^^^ ((e h block 31)).rotateLeft 26 ^^^ ((e h block 31)).rotateLeft 7) + 0x14292967 + (a h block 28) + (e h block 28) + (word block 31)) := by
  refine (eWord_succ h ((schedule block).map UInt32.toBitVec) 31).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 28) + ((e h block 28) + bitVecBigSigma1 (e h block 31) + bitVecChoice (e h block 31) (e h block 30) (e h block 29) + 0x14292967 + (word block 31)) = (((~~~(e h block 31)) &&& (e h block 29)) + ((e h block 30) &&& (e h block 31)) + (((e h block 31)).rotateLeft 21 ^^^ ((e h block 31)).rotateLeft 26 ^^^ ((e h block 31)).rotateLeft 7) + 0x14292967 + (a h block 28) + (e h block 28) + (word block 31))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]
  generalize (a h block 28) = v0
  generalize (e h block 28) = v1
  generalize (e h block 29) = v2
  generalize (e h block 30) = v3
  generalize (e h block 31) = v4
  generalize (word block 31) = v5
  ac_rfl

theorem a33 (h : BitVecState) (block : Array Bool) :
    (a h block 33) = (((~~~(e h block 32)) &&& (e h block 30)) + ((e h block 31) &&& (e h block 32)) + ((((a h block 30) ^^^ (a h block 31)) &&& (a h block 32)) ^^^ ((a h block 30) &&& (a h block 31))) + (((a h block 32)).rotateLeft 10 ^^^ ((a h block 32)).rotateLeft 19 ^^^ ((a h block 32)).rotateLeft 30) + (((e h block 32)).rotateLeft 21 ^^^ ((e h block 32)).rotateLeft 26 ^^^ ((e h block 32)).rotateLeft 7) + 0x27b70a85 + (e h block 29) + (word block 32)) := by
  refine (aWord_succ h ((schedule block).map UInt32.toBitVec) 32).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 29) + bitVecBigSigma1 (e h block 32) + bitVecChoice (e h block 32) (e h block 31) (e h block 30) + 0x27b70a85 + (word block 32)) + (bitVecBigSigma0 (a h block 32) + bitVecMajority (a h block 32) (a h block 31) (a h block 30)) = (((~~~(e h block 32)) &&& (e h block 30)) + ((e h block 31) &&& (e h block 32)) + ((((a h block 30) ^^^ (a h block 31)) &&& (a h block 32)) ^^^ ((a h block 30) &&& (a h block 31))) + (((a h block 32)).rotateLeft 10 ^^^ ((a h block 32)).rotateLeft 19 ^^^ ((a h block 32)).rotateLeft 30) + (((e h block 32)).rotateLeft 21 ^^^ ((e h block 32)).rotateLeft 26 ^^^ ((e h block 32)).rotateLeft 7) + 0x27b70a85 + (e h block 29) + (word block 32))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]
  generalize (a h block 30) = v0
  generalize (a h block 31) = v1
  generalize (a h block 32) = v2
  generalize (e h block 29) = v3
  generalize (e h block 30) = v4
  generalize (e h block 31) = v5
  generalize (e h block 32) = v6
  generalize (word block 32) = v7
  ac_rfl

theorem e33 (h : BitVecState) (block : Array Bool) :
    (e h block 33) = (((~~~(e h block 32)) &&& (e h block 30)) + ((e h block 31) &&& (e h block 32)) + (((e h block 32)).rotateLeft 21 ^^^ ((e h block 32)).rotateLeft 26 ^^^ ((e h block 32)).rotateLeft 7) + 0x27b70a85 + (a h block 29) + (e h block 29) + (word block 32)) := by
  refine (eWord_succ h ((schedule block).map UInt32.toBitVec) 32).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 29) + ((e h block 29) + bitVecBigSigma1 (e h block 32) + bitVecChoice (e h block 32) (e h block 31) (e h block 30) + 0x27b70a85 + (word block 32)) = (((~~~(e h block 32)) &&& (e h block 30)) + ((e h block 31) &&& (e h block 32)) + (((e h block 32)).rotateLeft 21 ^^^ ((e h block 32)).rotateLeft 26 ^^^ ((e h block 32)).rotateLeft 7) + 0x27b70a85 + (a h block 29) + (e h block 29) + (word block 32))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]
  generalize (a h block 29) = v0
  generalize (e h block 29) = v1
  generalize (e h block 30) = v2
  generalize (e h block 31) = v3
  generalize (e h block 32) = v4
  generalize (word block 32) = v5
  ac_rfl

theorem a34 (h : BitVecState) (block : Array Bool) :
    (a h block 34) = (((~~~(e h block 33)) &&& (e h block 31)) + ((e h block 32) &&& (e h block 33)) + ((((a h block 31) ^^^ (a h block 32)) &&& (a h block 33)) ^^^ ((a h block 31) &&& (a h block 32))) + (((a h block 33)).rotateLeft 10 ^^^ ((a h block 33)).rotateLeft 19 ^^^ ((a h block 33)).rotateLeft 30) + (((e h block 33)).rotateLeft 21 ^^^ ((e h block 33)).rotateLeft 26 ^^^ ((e h block 33)).rotateLeft 7) + 0x2e1b2138 + (e h block 30) + (word block 33)) := by
  refine (aWord_succ h ((schedule block).map UInt32.toBitVec) 33).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 30) + bitVecBigSigma1 (e h block 33) + bitVecChoice (e h block 33) (e h block 32) (e h block 31) + 0x2e1b2138 + (word block 33)) + (bitVecBigSigma0 (a h block 33) + bitVecMajority (a h block 33) (a h block 32) (a h block 31)) = (((~~~(e h block 33)) &&& (e h block 31)) + ((e h block 32) &&& (e h block 33)) + ((((a h block 31) ^^^ (a h block 32)) &&& (a h block 33)) ^^^ ((a h block 31) &&& (a h block 32))) + (((a h block 33)).rotateLeft 10 ^^^ ((a h block 33)).rotateLeft 19 ^^^ ((a h block 33)).rotateLeft 30) + (((e h block 33)).rotateLeft 21 ^^^ ((e h block 33)).rotateLeft 26 ^^^ ((e h block 33)).rotateLeft 7) + 0x2e1b2138 + (e h block 30) + (word block 33))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]
  generalize (a h block 31) = v0
  generalize (a h block 32) = v1
  generalize (a h block 33) = v2
  generalize (e h block 30) = v3
  generalize (e h block 31) = v4
  generalize (e h block 32) = v5
  generalize (e h block 33) = v6
  generalize (word block 33) = v7
  ac_rfl

theorem e34 (h : BitVecState) (block : Array Bool) :
    (e h block 34) = (((~~~(e h block 33)) &&& (e h block 31)) + ((e h block 32) &&& (e h block 33)) + (((e h block 33)).rotateLeft 21 ^^^ ((e h block 33)).rotateLeft 26 ^^^ ((e h block 33)).rotateLeft 7) + 0x2e1b2138 + (a h block 30) + (e h block 30) + (word block 33)) := by
  refine (eWord_succ h ((schedule block).map UInt32.toBitVec) 33).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 30) + ((e h block 30) + bitVecBigSigma1 (e h block 33) + bitVecChoice (e h block 33) (e h block 32) (e h block 31) + 0x2e1b2138 + (word block 33)) = (((~~~(e h block 33)) &&& (e h block 31)) + ((e h block 32) &&& (e h block 33)) + (((e h block 33)).rotateLeft 21 ^^^ ((e h block 33)).rotateLeft 26 ^^^ ((e h block 33)).rotateLeft 7) + 0x2e1b2138 + (a h block 30) + (e h block 30) + (word block 33))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]
  generalize (a h block 30) = v0
  generalize (e h block 30) = v1
  generalize (e h block 31) = v2
  generalize (e h block 32) = v3
  generalize (e h block 33) = v4
  generalize (word block 33) = v5
  ac_rfl

theorem a35 (h : BitVecState) (block : Array Bool) :
    (a h block 35) = (((~~~(e h block 34)) &&& (e h block 32)) + ((e h block 33) &&& (e h block 34)) + ((((a h block 32) ^^^ (a h block 33)) &&& (a h block 34)) ^^^ ((a h block 32) &&& (a h block 33))) + (((a h block 34)).rotateLeft 10 ^^^ ((a h block 34)).rotateLeft 19 ^^^ ((a h block 34)).rotateLeft 30) + (((e h block 34)).rotateLeft 21 ^^^ ((e h block 34)).rotateLeft 26 ^^^ ((e h block 34)).rotateLeft 7) + 0x4d2c6dfc + (e h block 31) + (word block 34)) := by
  refine (aWord_succ h ((schedule block).map UInt32.toBitVec) 34).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 31) + bitVecBigSigma1 (e h block 34) + bitVecChoice (e h block 34) (e h block 33) (e h block 32) + 0x4d2c6dfc + (word block 34)) + (bitVecBigSigma0 (a h block 34) + bitVecMajority (a h block 34) (a h block 33) (a h block 32)) = (((~~~(e h block 34)) &&& (e h block 32)) + ((e h block 33) &&& (e h block 34)) + ((((a h block 32) ^^^ (a h block 33)) &&& (a h block 34)) ^^^ ((a h block 32) &&& (a h block 33))) + (((a h block 34)).rotateLeft 10 ^^^ ((a h block 34)).rotateLeft 19 ^^^ ((a h block 34)).rotateLeft 30) + (((e h block 34)).rotateLeft 21 ^^^ ((e h block 34)).rotateLeft 26 ^^^ ((e h block 34)).rotateLeft 7) + 0x4d2c6dfc + (e h block 31) + (word block 34))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]
  generalize (a h block 32) = v0
  generalize (a h block 33) = v1
  generalize (a h block 34) = v2
  generalize (e h block 31) = v3
  generalize (e h block 32) = v4
  generalize (e h block 33) = v5
  generalize (e h block 34) = v6
  generalize (word block 34) = v7
  ac_rfl

theorem e35 (h : BitVecState) (block : Array Bool) :
    (e h block 35) = (((~~~(e h block 34)) &&& (e h block 32)) + ((e h block 33) &&& (e h block 34)) + (((e h block 34)).rotateLeft 21 ^^^ ((e h block 34)).rotateLeft 26 ^^^ ((e h block 34)).rotateLeft 7) + 0x4d2c6dfc + (a h block 31) + (e h block 31) + (word block 34)) := by
  refine (eWord_succ h ((schedule block).map UInt32.toBitVec) 34).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 31) + ((e h block 31) + bitVecBigSigma1 (e h block 34) + bitVecChoice (e h block 34) (e h block 33) (e h block 32) + 0x4d2c6dfc + (word block 34)) = (((~~~(e h block 34)) &&& (e h block 32)) + ((e h block 33) &&& (e h block 34)) + (((e h block 34)).rotateLeft 21 ^^^ ((e h block 34)).rotateLeft 26 ^^^ ((e h block 34)).rotateLeft 7) + 0x4d2c6dfc + (a h block 31) + (e h block 31) + (word block 34))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]
  generalize (a h block 31) = v0
  generalize (e h block 31) = v1
  generalize (e h block 32) = v2
  generalize (e h block 33) = v3
  generalize (e h block 34) = v4
  generalize (word block 34) = v5
  ac_rfl

theorem a36 (h : BitVecState) (block : Array Bool) :
    (a h block 36) = (((~~~(e h block 35)) &&& (e h block 33)) + ((e h block 34) &&& (e h block 35)) + ((((a h block 33) ^^^ (a h block 34)) &&& (a h block 35)) ^^^ ((a h block 33) &&& (a h block 34))) + (((a h block 35)).rotateLeft 10 ^^^ ((a h block 35)).rotateLeft 19 ^^^ ((a h block 35)).rotateLeft 30) + (((e h block 35)).rotateLeft 21 ^^^ ((e h block 35)).rotateLeft 26 ^^^ ((e h block 35)).rotateLeft 7) + 0x53380d13 + (e h block 32) + (word block 35)) := by
  refine (aWord_succ h ((schedule block).map UInt32.toBitVec) 35).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 32) + bitVecBigSigma1 (e h block 35) + bitVecChoice (e h block 35) (e h block 34) (e h block 33) + 0x53380d13 + (word block 35)) + (bitVecBigSigma0 (a h block 35) + bitVecMajority (a h block 35) (a h block 34) (a h block 33)) = (((~~~(e h block 35)) &&& (e h block 33)) + ((e h block 34) &&& (e h block 35)) + ((((a h block 33) ^^^ (a h block 34)) &&& (a h block 35)) ^^^ ((a h block 33) &&& (a h block 34))) + (((a h block 35)).rotateLeft 10 ^^^ ((a h block 35)).rotateLeft 19 ^^^ ((a h block 35)).rotateLeft 30) + (((e h block 35)).rotateLeft 21 ^^^ ((e h block 35)).rotateLeft 26 ^^^ ((e h block 35)).rotateLeft 7) + 0x53380d13 + (e h block 32) + (word block 35))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]
  generalize (a h block 33) = v0
  generalize (a h block 34) = v1
  generalize (a h block 35) = v2
  generalize (e h block 32) = v3
  generalize (e h block 33) = v4
  generalize (e h block 34) = v5
  generalize (e h block 35) = v6
  generalize (word block 35) = v7
  ac_rfl

theorem e36 (h : BitVecState) (block : Array Bool) :
    (e h block 36) = (((~~~(e h block 35)) &&& (e h block 33)) + ((e h block 34) &&& (e h block 35)) + (((e h block 35)).rotateLeft 21 ^^^ ((e h block 35)).rotateLeft 26 ^^^ ((e h block 35)).rotateLeft 7) + 0x53380d13 + (a h block 32) + (e h block 32) + (word block 35)) := by
  refine (eWord_succ h ((schedule block).map UInt32.toBitVec) 35).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 32) + ((e h block 32) + bitVecBigSigma1 (e h block 35) + bitVecChoice (e h block 35) (e h block 34) (e h block 33) + 0x53380d13 + (word block 35)) = (((~~~(e h block 35)) &&& (e h block 33)) + ((e h block 34) &&& (e h block 35)) + (((e h block 35)).rotateLeft 21 ^^^ ((e h block 35)).rotateLeft 26 ^^^ ((e h block 35)).rotateLeft 7) + 0x53380d13 + (a h block 32) + (e h block 32) + (word block 35))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]
  generalize (a h block 32) = v0
  generalize (e h block 32) = v1
  generalize (e h block 33) = v2
  generalize (e h block 34) = v3
  generalize (e h block 35) = v4
  generalize (word block 35) = v5
  ac_rfl

theorem a37 (h : BitVecState) (block : Array Bool) :
    (a h block 37) = (((~~~(e h block 36)) &&& (e h block 34)) + ((e h block 35) &&& (e h block 36)) + ((((a h block 34) ^^^ (a h block 35)) &&& (a h block 36)) ^^^ ((a h block 34) &&& (a h block 35))) + (((a h block 36)).rotateLeft 10 ^^^ ((a h block 36)).rotateLeft 19 ^^^ ((a h block 36)).rotateLeft 30) + (((e h block 36)).rotateLeft 21 ^^^ ((e h block 36)).rotateLeft 26 ^^^ ((e h block 36)).rotateLeft 7) + 0x650a7354 + (e h block 33) + (word block 36)) := by
  refine (aWord_succ h ((schedule block).map UInt32.toBitVec) 36).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 33) + bitVecBigSigma1 (e h block 36) + bitVecChoice (e h block 36) (e h block 35) (e h block 34) + 0x650a7354 + (word block 36)) + (bitVecBigSigma0 (a h block 36) + bitVecMajority (a h block 36) (a h block 35) (a h block 34)) = (((~~~(e h block 36)) &&& (e h block 34)) + ((e h block 35) &&& (e h block 36)) + ((((a h block 34) ^^^ (a h block 35)) &&& (a h block 36)) ^^^ ((a h block 34) &&& (a h block 35))) + (((a h block 36)).rotateLeft 10 ^^^ ((a h block 36)).rotateLeft 19 ^^^ ((a h block 36)).rotateLeft 30) + (((e h block 36)).rotateLeft 21 ^^^ ((e h block 36)).rotateLeft 26 ^^^ ((e h block 36)).rotateLeft 7) + 0x650a7354 + (e h block 33) + (word block 36))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]
  generalize (a h block 34) = v0
  generalize (a h block 35) = v1
  generalize (a h block 36) = v2
  generalize (e h block 33) = v3
  generalize (e h block 34) = v4
  generalize (e h block 35) = v5
  generalize (e h block 36) = v6
  generalize (word block 36) = v7
  ac_rfl

theorem e37 (h : BitVecState) (block : Array Bool) :
    (e h block 37) = (((~~~(e h block 36)) &&& (e h block 34)) + ((e h block 35) &&& (e h block 36)) + (((e h block 36)).rotateLeft 21 ^^^ ((e h block 36)).rotateLeft 26 ^^^ ((e h block 36)).rotateLeft 7) + 0x650a7354 + (a h block 33) + (e h block 33) + (word block 36)) := by
  refine (eWord_succ h ((schedule block).map UInt32.toBitVec) 36).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 33) + ((e h block 33) + bitVecBigSigma1 (e h block 36) + bitVecChoice (e h block 36) (e h block 35) (e h block 34) + 0x650a7354 + (word block 36)) = (((~~~(e h block 36)) &&& (e h block 34)) + ((e h block 35) &&& (e h block 36)) + (((e h block 36)).rotateLeft 21 ^^^ ((e h block 36)).rotateLeft 26 ^^^ ((e h block 36)).rotateLeft 7) + 0x650a7354 + (a h block 33) + (e h block 33) + (word block 36))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]
  generalize (a h block 33) = v0
  generalize (e h block 33) = v1
  generalize (e h block 34) = v2
  generalize (e h block 35) = v3
  generalize (e h block 36) = v4
  generalize (word block 36) = v5
  ac_rfl

theorem a38 (h : BitVecState) (block : Array Bool) :
    (a h block 38) = (((~~~(e h block 37)) &&& (e h block 35)) + ((e h block 36) &&& (e h block 37)) + ((((a h block 35) ^^^ (a h block 36)) &&& (a h block 37)) ^^^ ((a h block 35) &&& (a h block 36))) + (((a h block 37)).rotateLeft 10 ^^^ ((a h block 37)).rotateLeft 19 ^^^ ((a h block 37)).rotateLeft 30) + (((e h block 37)).rotateLeft 21 ^^^ ((e h block 37)).rotateLeft 26 ^^^ ((e h block 37)).rotateLeft 7) + 0x766a0abb + (e h block 34) + (word block 37)) := by
  refine (aWord_succ h ((schedule block).map UInt32.toBitVec) 37).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 34) + bitVecBigSigma1 (e h block 37) + bitVecChoice (e h block 37) (e h block 36) (e h block 35) + 0x766a0abb + (word block 37)) + (bitVecBigSigma0 (a h block 37) + bitVecMajority (a h block 37) (a h block 36) (a h block 35)) = (((~~~(e h block 37)) &&& (e h block 35)) + ((e h block 36) &&& (e h block 37)) + ((((a h block 35) ^^^ (a h block 36)) &&& (a h block 37)) ^^^ ((a h block 35) &&& (a h block 36))) + (((a h block 37)).rotateLeft 10 ^^^ ((a h block 37)).rotateLeft 19 ^^^ ((a h block 37)).rotateLeft 30) + (((e h block 37)).rotateLeft 21 ^^^ ((e h block 37)).rotateLeft 26 ^^^ ((e h block 37)).rotateLeft 7) + 0x766a0abb + (e h block 34) + (word block 37))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]
  generalize (a h block 35) = v0
  generalize (a h block 36) = v1
  generalize (a h block 37) = v2
  generalize (e h block 34) = v3
  generalize (e h block 35) = v4
  generalize (e h block 36) = v5
  generalize (e h block 37) = v6
  generalize (word block 37) = v7
  ac_rfl

theorem e38 (h : BitVecState) (block : Array Bool) :
    (e h block 38) = (((~~~(e h block 37)) &&& (e h block 35)) + ((e h block 36) &&& (e h block 37)) + (((e h block 37)).rotateLeft 21 ^^^ ((e h block 37)).rotateLeft 26 ^^^ ((e h block 37)).rotateLeft 7) + 0x766a0abb + (a h block 34) + (e h block 34) + (word block 37)) := by
  refine (eWord_succ h ((schedule block).map UInt32.toBitVec) 37).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 34) + ((e h block 34) + bitVecBigSigma1 (e h block 37) + bitVecChoice (e h block 37) (e h block 36) (e h block 35) + 0x766a0abb + (word block 37)) = (((~~~(e h block 37)) &&& (e h block 35)) + ((e h block 36) &&& (e h block 37)) + (((e h block 37)).rotateLeft 21 ^^^ ((e h block 37)).rotateLeft 26 ^^^ ((e h block 37)).rotateLeft 7) + 0x766a0abb + (a h block 34) + (e h block 34) + (word block 37))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]
  generalize (a h block 34) = v0
  generalize (e h block 34) = v1
  generalize (e h block 35) = v2
  generalize (e h block 36) = v3
  generalize (e h block 37) = v4
  generalize (word block 37) = v5
  ac_rfl

theorem a39 (h : BitVecState) (block : Array Bool) :
    (a h block 39) = (((~~~(e h block 38)) &&& (e h block 36)) + ((e h block 37) &&& (e h block 38)) + ((((a h block 36) ^^^ (a h block 37)) &&& (a h block 38)) ^^^ ((a h block 36) &&& (a h block 37))) + (((a h block 38)).rotateLeft 10 ^^^ ((a h block 38)).rotateLeft 19 ^^^ ((a h block 38)).rotateLeft 30) + (((e h block 38)).rotateLeft 21 ^^^ ((e h block 38)).rotateLeft 26 ^^^ ((e h block 38)).rotateLeft 7) + 0x81c2c92e + (e h block 35) + (word block 38)) := by
  refine (aWord_succ h ((schedule block).map UInt32.toBitVec) 38).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 35) + bitVecBigSigma1 (e h block 38) + bitVecChoice (e h block 38) (e h block 37) (e h block 36) + 0x81c2c92e + (word block 38)) + (bitVecBigSigma0 (a h block 38) + bitVecMajority (a h block 38) (a h block 37) (a h block 36)) = (((~~~(e h block 38)) &&& (e h block 36)) + ((e h block 37) &&& (e h block 38)) + ((((a h block 36) ^^^ (a h block 37)) &&& (a h block 38)) ^^^ ((a h block 36) &&& (a h block 37))) + (((a h block 38)).rotateLeft 10 ^^^ ((a h block 38)).rotateLeft 19 ^^^ ((a h block 38)).rotateLeft 30) + (((e h block 38)).rotateLeft 21 ^^^ ((e h block 38)).rotateLeft 26 ^^^ ((e h block 38)).rotateLeft 7) + 0x81c2c92e + (e h block 35) + (word block 38))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]
  generalize (a h block 36) = v0
  generalize (a h block 37) = v1
  generalize (a h block 38) = v2
  generalize (e h block 35) = v3
  generalize (e h block 36) = v4
  generalize (e h block 37) = v5
  generalize (e h block 38) = v6
  generalize (word block 38) = v7
  ac_rfl

theorem e39 (h : BitVecState) (block : Array Bool) :
    (e h block 39) = (((~~~(e h block 38)) &&& (e h block 36)) + ((e h block 37) &&& (e h block 38)) + (((e h block 38)).rotateLeft 21 ^^^ ((e h block 38)).rotateLeft 26 ^^^ ((e h block 38)).rotateLeft 7) + 0x81c2c92e + (a h block 35) + (e h block 35) + (word block 38)) := by
  refine (eWord_succ h ((schedule block).map UInt32.toBitVec) 38).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 35) + ((e h block 35) + bitVecBigSigma1 (e h block 38) + bitVecChoice (e h block 38) (e h block 37) (e h block 36) + 0x81c2c92e + (word block 38)) = (((~~~(e h block 38)) &&& (e h block 36)) + ((e h block 37) &&& (e h block 38)) + (((e h block 38)).rotateLeft 21 ^^^ ((e h block 38)).rotateLeft 26 ^^^ ((e h block 38)).rotateLeft 7) + 0x81c2c92e + (a h block 35) + (e h block 35) + (word block 38))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]
  generalize (a h block 35) = v0
  generalize (e h block 35) = v1
  generalize (e h block 36) = v2
  generalize (e h block 37) = v3
  generalize (e h block 38) = v4
  generalize (word block 38) = v5
  ac_rfl

theorem a40 (h : BitVecState) (block : Array Bool) :
    (a h block 40) = (((~~~(e h block 39)) &&& (e h block 37)) + ((e h block 38) &&& (e h block 39)) + ((((a h block 37) ^^^ (a h block 38)) &&& (a h block 39)) ^^^ ((a h block 37) &&& (a h block 38))) + (((a h block 39)).rotateLeft 10 ^^^ ((a h block 39)).rotateLeft 19 ^^^ ((a h block 39)).rotateLeft 30) + (((e h block 39)).rotateLeft 21 ^^^ ((e h block 39)).rotateLeft 26 ^^^ ((e h block 39)).rotateLeft 7) + 0x92722c85 + (e h block 36) + (word block 39)) := by
  refine (aWord_succ h ((schedule block).map UInt32.toBitVec) 39).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 36) + bitVecBigSigma1 (e h block 39) + bitVecChoice (e h block 39) (e h block 38) (e h block 37) + 0x92722c85 + (word block 39)) + (bitVecBigSigma0 (a h block 39) + bitVecMajority (a h block 39) (a h block 38) (a h block 37)) = (((~~~(e h block 39)) &&& (e h block 37)) + ((e h block 38) &&& (e h block 39)) + ((((a h block 37) ^^^ (a h block 38)) &&& (a h block 39)) ^^^ ((a h block 37) &&& (a h block 38))) + (((a h block 39)).rotateLeft 10 ^^^ ((a h block 39)).rotateLeft 19 ^^^ ((a h block 39)).rotateLeft 30) + (((e h block 39)).rotateLeft 21 ^^^ ((e h block 39)).rotateLeft 26 ^^^ ((e h block 39)).rotateLeft 7) + 0x92722c85 + (e h block 36) + (word block 39))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]
  generalize (a h block 37) = v0
  generalize (a h block 38) = v1
  generalize (a h block 39) = v2
  generalize (e h block 36) = v3
  generalize (e h block 37) = v4
  generalize (e h block 38) = v5
  generalize (e h block 39) = v6
  generalize (word block 39) = v7
  ac_rfl

theorem e40 (h : BitVecState) (block : Array Bool) :
    (e h block 40) = (((~~~(e h block 39)) &&& (e h block 37)) + ((e h block 38) &&& (e h block 39)) + (((e h block 39)).rotateLeft 21 ^^^ ((e h block 39)).rotateLeft 26 ^^^ ((e h block 39)).rotateLeft 7) + 0x92722c85 + (a h block 36) + (e h block 36) + (word block 39)) := by
  refine (eWord_succ h ((schedule block).map UInt32.toBitVec) 39).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 36) + ((e h block 36) + bitVecBigSigma1 (e h block 39) + bitVecChoice (e h block 39) (e h block 38) (e h block 37) + 0x92722c85 + (word block 39)) = (((~~~(e h block 39)) &&& (e h block 37)) + ((e h block 38) &&& (e h block 39)) + (((e h block 39)).rotateLeft 21 ^^^ ((e h block 39)).rotateLeft 26 ^^^ ((e h block 39)).rotateLeft 7) + 0x92722c85 + (a h block 36) + (e h block 36) + (word block 39))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]
  generalize (a h block 36) = v0
  generalize (e h block 36) = v1
  generalize (e h block 37) = v2
  generalize (e h block 38) = v3
  generalize (e h block 39) = v4
  generalize (word block 39) = v5
  ac_rfl

theorem a41 (h : BitVecState) (block : Array Bool) :
    (a h block 41) = (((~~~(e h block 40)) &&& (e h block 38)) + ((e h block 39) &&& (e h block 40)) + ((((a h block 38) ^^^ (a h block 39)) &&& (a h block 40)) ^^^ ((a h block 38) &&& (a h block 39))) + (((a h block 40)).rotateLeft 10 ^^^ ((a h block 40)).rotateLeft 19 ^^^ ((a h block 40)).rotateLeft 30) + (((e h block 40)).rotateLeft 21 ^^^ ((e h block 40)).rotateLeft 26 ^^^ ((e h block 40)).rotateLeft 7) + 0xa2bfe8a1 + (e h block 37) + (word block 40)) := by
  refine (aWord_succ h ((schedule block).map UInt32.toBitVec) 40).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 37) + bitVecBigSigma1 (e h block 40) + bitVecChoice (e h block 40) (e h block 39) (e h block 38) + 0xa2bfe8a1 + (word block 40)) + (bitVecBigSigma0 (a h block 40) + bitVecMajority (a h block 40) (a h block 39) (a h block 38)) = (((~~~(e h block 40)) &&& (e h block 38)) + ((e h block 39) &&& (e h block 40)) + ((((a h block 38) ^^^ (a h block 39)) &&& (a h block 40)) ^^^ ((a h block 38) &&& (a h block 39))) + (((a h block 40)).rotateLeft 10 ^^^ ((a h block 40)).rotateLeft 19 ^^^ ((a h block 40)).rotateLeft 30) + (((e h block 40)).rotateLeft 21 ^^^ ((e h block 40)).rotateLeft 26 ^^^ ((e h block 40)).rotateLeft 7) + 0xa2bfe8a1 + (e h block 37) + (word block 40))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]
  generalize (a h block 38) = v0
  generalize (a h block 39) = v1
  generalize (a h block 40) = v2
  generalize (e h block 37) = v3
  generalize (e h block 38) = v4
  generalize (e h block 39) = v5
  generalize (e h block 40) = v6
  generalize (word block 40) = v7
  ac_rfl

theorem e41 (h : BitVecState) (block : Array Bool) :
    (e h block 41) = (((~~~(e h block 40)) &&& (e h block 38)) + ((e h block 39) &&& (e h block 40)) + (((e h block 40)).rotateLeft 21 ^^^ ((e h block 40)).rotateLeft 26 ^^^ ((e h block 40)).rotateLeft 7) + 0xa2bfe8a1 + (a h block 37) + (e h block 37) + (word block 40)) := by
  refine (eWord_succ h ((schedule block).map UInt32.toBitVec) 40).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 37) + ((e h block 37) + bitVecBigSigma1 (e h block 40) + bitVecChoice (e h block 40) (e h block 39) (e h block 38) + 0xa2bfe8a1 + (word block 40)) = (((~~~(e h block 40)) &&& (e h block 38)) + ((e h block 39) &&& (e h block 40)) + (((e h block 40)).rotateLeft 21 ^^^ ((e h block 40)).rotateLeft 26 ^^^ ((e h block 40)).rotateLeft 7) + 0xa2bfe8a1 + (a h block 37) + (e h block 37) + (word block 40))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]
  generalize (a h block 37) = v0
  generalize (e h block 37) = v1
  generalize (e h block 38) = v2
  generalize (e h block 39) = v3
  generalize (e h block 40) = v4
  generalize (word block 40) = v5
  ac_rfl

theorem a42 (h : BitVecState) (block : Array Bool) :
    (a h block 42) = (((~~~(e h block 41)) &&& (e h block 39)) + ((e h block 40) &&& (e h block 41)) + ((((a h block 39) ^^^ (a h block 40)) &&& (a h block 41)) ^^^ ((a h block 39) &&& (a h block 40))) + (((a h block 41)).rotateLeft 10 ^^^ ((a h block 41)).rotateLeft 19 ^^^ ((a h block 41)).rotateLeft 30) + (((e h block 41)).rotateLeft 21 ^^^ ((e h block 41)).rotateLeft 26 ^^^ ((e h block 41)).rotateLeft 7) + 0xa81a664b + (e h block 38) + (word block 41)) := by
  refine (aWord_succ h ((schedule block).map UInt32.toBitVec) 41).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 38) + bitVecBigSigma1 (e h block 41) + bitVecChoice (e h block 41) (e h block 40) (e h block 39) + 0xa81a664b + (word block 41)) + (bitVecBigSigma0 (a h block 41) + bitVecMajority (a h block 41) (a h block 40) (a h block 39)) = (((~~~(e h block 41)) &&& (e h block 39)) + ((e h block 40) &&& (e h block 41)) + ((((a h block 39) ^^^ (a h block 40)) &&& (a h block 41)) ^^^ ((a h block 39) &&& (a h block 40))) + (((a h block 41)).rotateLeft 10 ^^^ ((a h block 41)).rotateLeft 19 ^^^ ((a h block 41)).rotateLeft 30) + (((e h block 41)).rotateLeft 21 ^^^ ((e h block 41)).rotateLeft 26 ^^^ ((e h block 41)).rotateLeft 7) + 0xa81a664b + (e h block 38) + (word block 41))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]
  generalize (a h block 39) = v0
  generalize (a h block 40) = v1
  generalize (a h block 41) = v2
  generalize (e h block 38) = v3
  generalize (e h block 39) = v4
  generalize (e h block 40) = v5
  generalize (e h block 41) = v6
  generalize (word block 41) = v7
  ac_rfl

theorem e42 (h : BitVecState) (block : Array Bool) :
    (e h block 42) = (((~~~(e h block 41)) &&& (e h block 39)) + ((e h block 40) &&& (e h block 41)) + (((e h block 41)).rotateLeft 21 ^^^ ((e h block 41)).rotateLeft 26 ^^^ ((e h block 41)).rotateLeft 7) + 0xa81a664b + (a h block 38) + (e h block 38) + (word block 41)) := by
  refine (eWord_succ h ((schedule block).map UInt32.toBitVec) 41).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 38) + ((e h block 38) + bitVecBigSigma1 (e h block 41) + bitVecChoice (e h block 41) (e h block 40) (e h block 39) + 0xa81a664b + (word block 41)) = (((~~~(e h block 41)) &&& (e h block 39)) + ((e h block 40) &&& (e h block 41)) + (((e h block 41)).rotateLeft 21 ^^^ ((e h block 41)).rotateLeft 26 ^^^ ((e h block 41)).rotateLeft 7) + 0xa81a664b + (a h block 38) + (e h block 38) + (word block 41))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]
  generalize (a h block 38) = v0
  generalize (e h block 38) = v1
  generalize (e h block 39) = v2
  generalize (e h block 40) = v3
  generalize (e h block 41) = v4
  generalize (word block 41) = v5
  ac_rfl

theorem a43 (h : BitVecState) (block : Array Bool) :
    (a h block 43) = (((~~~(e h block 42)) &&& (e h block 40)) + ((e h block 41) &&& (e h block 42)) + ((((a h block 40) ^^^ (a h block 41)) &&& (a h block 42)) ^^^ ((a h block 40) &&& (a h block 41))) + (((a h block 42)).rotateLeft 10 ^^^ ((a h block 42)).rotateLeft 19 ^^^ ((a h block 42)).rotateLeft 30) + (((e h block 42)).rotateLeft 21 ^^^ ((e h block 42)).rotateLeft 26 ^^^ ((e h block 42)).rotateLeft 7) + 0xc24b8b70 + (e h block 39) + (word block 42)) := by
  refine (aWord_succ h ((schedule block).map UInt32.toBitVec) 42).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 39) + bitVecBigSigma1 (e h block 42) + bitVecChoice (e h block 42) (e h block 41) (e h block 40) + 0xc24b8b70 + (word block 42)) + (bitVecBigSigma0 (a h block 42) + bitVecMajority (a h block 42) (a h block 41) (a h block 40)) = (((~~~(e h block 42)) &&& (e h block 40)) + ((e h block 41) &&& (e h block 42)) + ((((a h block 40) ^^^ (a h block 41)) &&& (a h block 42)) ^^^ ((a h block 40) &&& (a h block 41))) + (((a h block 42)).rotateLeft 10 ^^^ ((a h block 42)).rotateLeft 19 ^^^ ((a h block 42)).rotateLeft 30) + (((e h block 42)).rotateLeft 21 ^^^ ((e h block 42)).rotateLeft 26 ^^^ ((e h block 42)).rotateLeft 7) + 0xc24b8b70 + (e h block 39) + (word block 42))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]
  generalize (a h block 40) = v0
  generalize (a h block 41) = v1
  generalize (a h block 42) = v2
  generalize (e h block 39) = v3
  generalize (e h block 40) = v4
  generalize (e h block 41) = v5
  generalize (e h block 42) = v6
  generalize (word block 42) = v7
  ac_rfl

theorem e43 (h : BitVecState) (block : Array Bool) :
    (e h block 43) = (((~~~(e h block 42)) &&& (e h block 40)) + ((e h block 41) &&& (e h block 42)) + (((e h block 42)).rotateLeft 21 ^^^ ((e h block 42)).rotateLeft 26 ^^^ ((e h block 42)).rotateLeft 7) + 0xc24b8b70 + (a h block 39) + (e h block 39) + (word block 42)) := by
  refine (eWord_succ h ((schedule block).map UInt32.toBitVec) 42).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 39) + ((e h block 39) + bitVecBigSigma1 (e h block 42) + bitVecChoice (e h block 42) (e h block 41) (e h block 40) + 0xc24b8b70 + (word block 42)) = (((~~~(e h block 42)) &&& (e h block 40)) + ((e h block 41) &&& (e h block 42)) + (((e h block 42)).rotateLeft 21 ^^^ ((e h block 42)).rotateLeft 26 ^^^ ((e h block 42)).rotateLeft 7) + 0xc24b8b70 + (a h block 39) + (e h block 39) + (word block 42))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]
  generalize (a h block 39) = v0
  generalize (e h block 39) = v1
  generalize (e h block 40) = v2
  generalize (e h block 41) = v3
  generalize (e h block 42) = v4
  generalize (word block 42) = v5
  ac_rfl

theorem a44 (h : BitVecState) (block : Array Bool) :
    (a h block 44) = (((~~~(e h block 43)) &&& (e h block 41)) + ((e h block 42) &&& (e h block 43)) + ((((a h block 41) ^^^ (a h block 42)) &&& (a h block 43)) ^^^ ((a h block 41) &&& (a h block 42))) + (((a h block 43)).rotateLeft 10 ^^^ ((a h block 43)).rotateLeft 19 ^^^ ((a h block 43)).rotateLeft 30) + (((e h block 43)).rotateLeft 21 ^^^ ((e h block 43)).rotateLeft 26 ^^^ ((e h block 43)).rotateLeft 7) + 0xc76c51a3 + (e h block 40) + (word block 43)) := by
  refine (aWord_succ h ((schedule block).map UInt32.toBitVec) 43).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 40) + bitVecBigSigma1 (e h block 43) + bitVecChoice (e h block 43) (e h block 42) (e h block 41) + 0xc76c51a3 + (word block 43)) + (bitVecBigSigma0 (a h block 43) + bitVecMajority (a h block 43) (a h block 42) (a h block 41)) = (((~~~(e h block 43)) &&& (e h block 41)) + ((e h block 42) &&& (e h block 43)) + ((((a h block 41) ^^^ (a h block 42)) &&& (a h block 43)) ^^^ ((a h block 41) &&& (a h block 42))) + (((a h block 43)).rotateLeft 10 ^^^ ((a h block 43)).rotateLeft 19 ^^^ ((a h block 43)).rotateLeft 30) + (((e h block 43)).rotateLeft 21 ^^^ ((e h block 43)).rotateLeft 26 ^^^ ((e h block 43)).rotateLeft 7) + 0xc76c51a3 + (e h block 40) + (word block 43))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]
  generalize (a h block 41) = v0
  generalize (a h block 42) = v1
  generalize (a h block 43) = v2
  generalize (e h block 40) = v3
  generalize (e h block 41) = v4
  generalize (e h block 42) = v5
  generalize (e h block 43) = v6
  generalize (word block 43) = v7
  ac_rfl

theorem e44 (h : BitVecState) (block : Array Bool) :
    (e h block 44) = (((~~~(e h block 43)) &&& (e h block 41)) + ((e h block 42) &&& (e h block 43)) + (((e h block 43)).rotateLeft 21 ^^^ ((e h block 43)).rotateLeft 26 ^^^ ((e h block 43)).rotateLeft 7) + 0xc76c51a3 + (a h block 40) + (e h block 40) + (word block 43)) := by
  refine (eWord_succ h ((schedule block).map UInt32.toBitVec) 43).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 40) + ((e h block 40) + bitVecBigSigma1 (e h block 43) + bitVecChoice (e h block 43) (e h block 42) (e h block 41) + 0xc76c51a3 + (word block 43)) = (((~~~(e h block 43)) &&& (e h block 41)) + ((e h block 42) &&& (e h block 43)) + (((e h block 43)).rotateLeft 21 ^^^ ((e h block 43)).rotateLeft 26 ^^^ ((e h block 43)).rotateLeft 7) + 0xc76c51a3 + (a h block 40) + (e h block 40) + (word block 43))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]
  generalize (a h block 40) = v0
  generalize (e h block 40) = v1
  generalize (e h block 41) = v2
  generalize (e h block 42) = v3
  generalize (e h block 43) = v4
  generalize (word block 43) = v5
  ac_rfl

theorem a45 (h : BitVecState) (block : Array Bool) :
    (a h block 45) = (((~~~(e h block 44)) &&& (e h block 42)) + ((e h block 43) &&& (e h block 44)) + ((((a h block 42) ^^^ (a h block 43)) &&& (a h block 44)) ^^^ ((a h block 42) &&& (a h block 43))) + (((a h block 44)).rotateLeft 10 ^^^ ((a h block 44)).rotateLeft 19 ^^^ ((a h block 44)).rotateLeft 30) + (((e h block 44)).rotateLeft 21 ^^^ ((e h block 44)).rotateLeft 26 ^^^ ((e h block 44)).rotateLeft 7) + 0xd192e819 + (e h block 41) + (word block 44)) := by
  refine (aWord_succ h ((schedule block).map UInt32.toBitVec) 44).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 41) + bitVecBigSigma1 (e h block 44) + bitVecChoice (e h block 44) (e h block 43) (e h block 42) + 0xd192e819 + (word block 44)) + (bitVecBigSigma0 (a h block 44) + bitVecMajority (a h block 44) (a h block 43) (a h block 42)) = (((~~~(e h block 44)) &&& (e h block 42)) + ((e h block 43) &&& (e h block 44)) + ((((a h block 42) ^^^ (a h block 43)) &&& (a h block 44)) ^^^ ((a h block 42) &&& (a h block 43))) + (((a h block 44)).rotateLeft 10 ^^^ ((a h block 44)).rotateLeft 19 ^^^ ((a h block 44)).rotateLeft 30) + (((e h block 44)).rotateLeft 21 ^^^ ((e h block 44)).rotateLeft 26 ^^^ ((e h block 44)).rotateLeft 7) + 0xd192e819 + (e h block 41) + (word block 44))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]
  generalize (a h block 42) = v0
  generalize (a h block 43) = v1
  generalize (a h block 44) = v2
  generalize (e h block 41) = v3
  generalize (e h block 42) = v4
  generalize (e h block 43) = v5
  generalize (e h block 44) = v6
  generalize (word block 44) = v7
  ac_rfl

theorem e45 (h : BitVecState) (block : Array Bool) :
    (e h block 45) = (((~~~(e h block 44)) &&& (e h block 42)) + ((e h block 43) &&& (e h block 44)) + (((e h block 44)).rotateLeft 21 ^^^ ((e h block 44)).rotateLeft 26 ^^^ ((e h block 44)).rotateLeft 7) + 0xd192e819 + (a h block 41) + (e h block 41) + (word block 44)) := by
  refine (eWord_succ h ((schedule block).map UInt32.toBitVec) 44).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 41) + ((e h block 41) + bitVecBigSigma1 (e h block 44) + bitVecChoice (e h block 44) (e h block 43) (e h block 42) + 0xd192e819 + (word block 44)) = (((~~~(e h block 44)) &&& (e h block 42)) + ((e h block 43) &&& (e h block 44)) + (((e h block 44)).rotateLeft 21 ^^^ ((e h block 44)).rotateLeft 26 ^^^ ((e h block 44)).rotateLeft 7) + 0xd192e819 + (a h block 41) + (e h block 41) + (word block 44))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]
  generalize (a h block 41) = v0
  generalize (e h block 41) = v1
  generalize (e h block 42) = v2
  generalize (e h block 43) = v3
  generalize (e h block 44) = v4
  generalize (word block 44) = v5
  ac_rfl

theorem a46 (h : BitVecState) (block : Array Bool) :
    (a h block 46) = (((~~~(e h block 45)) &&& (e h block 43)) + ((e h block 44) &&& (e h block 45)) + ((((a h block 43) ^^^ (a h block 44)) &&& (a h block 45)) ^^^ ((a h block 43) &&& (a h block 44))) + (((a h block 45)).rotateLeft 10 ^^^ ((a h block 45)).rotateLeft 19 ^^^ ((a h block 45)).rotateLeft 30) + (((e h block 45)).rotateLeft 21 ^^^ ((e h block 45)).rotateLeft 26 ^^^ ((e h block 45)).rotateLeft 7) + 0xd6990624 + (e h block 42) + (word block 45)) := by
  refine (aWord_succ h ((schedule block).map UInt32.toBitVec) 45).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 42) + bitVecBigSigma1 (e h block 45) + bitVecChoice (e h block 45) (e h block 44) (e h block 43) + 0xd6990624 + (word block 45)) + (bitVecBigSigma0 (a h block 45) + bitVecMajority (a h block 45) (a h block 44) (a h block 43)) = (((~~~(e h block 45)) &&& (e h block 43)) + ((e h block 44) &&& (e h block 45)) + ((((a h block 43) ^^^ (a h block 44)) &&& (a h block 45)) ^^^ ((a h block 43) &&& (a h block 44))) + (((a h block 45)).rotateLeft 10 ^^^ ((a h block 45)).rotateLeft 19 ^^^ ((a h block 45)).rotateLeft 30) + (((e h block 45)).rotateLeft 21 ^^^ ((e h block 45)).rotateLeft 26 ^^^ ((e h block 45)).rotateLeft 7) + 0xd6990624 + (e h block 42) + (word block 45))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]
  generalize (a h block 43) = v0
  generalize (a h block 44) = v1
  generalize (a h block 45) = v2
  generalize (e h block 42) = v3
  generalize (e h block 43) = v4
  generalize (e h block 44) = v5
  generalize (e h block 45) = v6
  generalize (word block 45) = v7
  ac_rfl

theorem e46 (h : BitVecState) (block : Array Bool) :
    (e h block 46) = (((~~~(e h block 45)) &&& (e h block 43)) + ((e h block 44) &&& (e h block 45)) + (((e h block 45)).rotateLeft 21 ^^^ ((e h block 45)).rotateLeft 26 ^^^ ((e h block 45)).rotateLeft 7) + 0xd6990624 + (a h block 42) + (e h block 42) + (word block 45)) := by
  refine (eWord_succ h ((schedule block).map UInt32.toBitVec) 45).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 42) + ((e h block 42) + bitVecBigSigma1 (e h block 45) + bitVecChoice (e h block 45) (e h block 44) (e h block 43) + 0xd6990624 + (word block 45)) = (((~~~(e h block 45)) &&& (e h block 43)) + ((e h block 44) &&& (e h block 45)) + (((e h block 45)).rotateLeft 21 ^^^ ((e h block 45)).rotateLeft 26 ^^^ ((e h block 45)).rotateLeft 7) + 0xd6990624 + (a h block 42) + (e h block 42) + (word block 45))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]
  generalize (a h block 42) = v0
  generalize (e h block 42) = v1
  generalize (e h block 43) = v2
  generalize (e h block 44) = v3
  generalize (e h block 45) = v4
  generalize (word block 45) = v5
  ac_rfl

theorem a47 (h : BitVecState) (block : Array Bool) :
    (a h block 47) = (((~~~(e h block 46)) &&& (e h block 44)) + ((e h block 45) &&& (e h block 46)) + ((((a h block 44) ^^^ (a h block 45)) &&& (a h block 46)) ^^^ ((a h block 44) &&& (a h block 45))) + (((a h block 46)).rotateLeft 10 ^^^ ((a h block 46)).rotateLeft 19 ^^^ ((a h block 46)).rotateLeft 30) + (((e h block 46)).rotateLeft 21 ^^^ ((e h block 46)).rotateLeft 26 ^^^ ((e h block 46)).rotateLeft 7) + 0xf40e3585 + (e h block 43) + (word block 46)) := by
  refine (aWord_succ h ((schedule block).map UInt32.toBitVec) 46).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 43) + bitVecBigSigma1 (e h block 46) + bitVecChoice (e h block 46) (e h block 45) (e h block 44) + 0xf40e3585 + (word block 46)) + (bitVecBigSigma0 (a h block 46) + bitVecMajority (a h block 46) (a h block 45) (a h block 44)) = (((~~~(e h block 46)) &&& (e h block 44)) + ((e h block 45) &&& (e h block 46)) + ((((a h block 44) ^^^ (a h block 45)) &&& (a h block 46)) ^^^ ((a h block 44) &&& (a h block 45))) + (((a h block 46)).rotateLeft 10 ^^^ ((a h block 46)).rotateLeft 19 ^^^ ((a h block 46)).rotateLeft 30) + (((e h block 46)).rotateLeft 21 ^^^ ((e h block 46)).rotateLeft 26 ^^^ ((e h block 46)).rotateLeft 7) + 0xf40e3585 + (e h block 43) + (word block 46))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]
  generalize (a h block 44) = v0
  generalize (a h block 45) = v1
  generalize (a h block 46) = v2
  generalize (e h block 43) = v3
  generalize (e h block 44) = v4
  generalize (e h block 45) = v5
  generalize (e h block 46) = v6
  generalize (word block 46) = v7
  ac_rfl

theorem e47 (h : BitVecState) (block : Array Bool) :
    (e h block 47) = (((~~~(e h block 46)) &&& (e h block 44)) + ((e h block 45) &&& (e h block 46)) + (((e h block 46)).rotateLeft 21 ^^^ ((e h block 46)).rotateLeft 26 ^^^ ((e h block 46)).rotateLeft 7) + 0xf40e3585 + (a h block 43) + (e h block 43) + (word block 46)) := by
  refine (eWord_succ h ((schedule block).map UInt32.toBitVec) 46).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 43) + ((e h block 43) + bitVecBigSigma1 (e h block 46) + bitVecChoice (e h block 46) (e h block 45) (e h block 44) + 0xf40e3585 + (word block 46)) = (((~~~(e h block 46)) &&& (e h block 44)) + ((e h block 45) &&& (e h block 46)) + (((e h block 46)).rotateLeft 21 ^^^ ((e h block 46)).rotateLeft 26 ^^^ ((e h block 46)).rotateLeft 7) + 0xf40e3585 + (a h block 43) + (e h block 43) + (word block 46))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]
  generalize (a h block 43) = v0
  generalize (e h block 43) = v1
  generalize (e h block 44) = v2
  generalize (e h block 45) = v3
  generalize (e h block 46) = v4
  generalize (word block 46) = v5
  ac_rfl

theorem a48 (h : BitVecState) (block : Array Bool) :
    (a h block 48) = (((~~~(e h block 47)) &&& (e h block 45)) + ((e h block 46) &&& (e h block 47)) + ((((a h block 45) ^^^ (a h block 46)) &&& (a h block 47)) ^^^ ((a h block 45) &&& (a h block 46))) + (((a h block 47)).rotateLeft 10 ^^^ ((a h block 47)).rotateLeft 19 ^^^ ((a h block 47)).rotateLeft 30) + (((e h block 47)).rotateLeft 21 ^^^ ((e h block 47)).rotateLeft 26 ^^^ ((e h block 47)).rotateLeft 7) + 0x106aa070 + (e h block 44) + (word block 47)) := by
  refine (aWord_succ h ((schedule block).map UInt32.toBitVec) 47).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 44) + bitVecBigSigma1 (e h block 47) + bitVecChoice (e h block 47) (e h block 46) (e h block 45) + 0x106aa070 + (word block 47)) + (bitVecBigSigma0 (a h block 47) + bitVecMajority (a h block 47) (a h block 46) (a h block 45)) = (((~~~(e h block 47)) &&& (e h block 45)) + ((e h block 46) &&& (e h block 47)) + ((((a h block 45) ^^^ (a h block 46)) &&& (a h block 47)) ^^^ ((a h block 45) &&& (a h block 46))) + (((a h block 47)).rotateLeft 10 ^^^ ((a h block 47)).rotateLeft 19 ^^^ ((a h block 47)).rotateLeft 30) + (((e h block 47)).rotateLeft 21 ^^^ ((e h block 47)).rotateLeft 26 ^^^ ((e h block 47)).rotateLeft 7) + 0x106aa070 + (e h block 44) + (word block 47))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]
  generalize (a h block 45) = v0
  generalize (a h block 46) = v1
  generalize (a h block 47) = v2
  generalize (e h block 44) = v3
  generalize (e h block 45) = v4
  generalize (e h block 46) = v5
  generalize (e h block 47) = v6
  generalize (word block 47) = v7
  ac_rfl

theorem e48 (h : BitVecState) (block : Array Bool) :
    (e h block 48) = (((~~~(e h block 47)) &&& (e h block 45)) + ((e h block 46) &&& (e h block 47)) + (((e h block 47)).rotateLeft 21 ^^^ ((e h block 47)).rotateLeft 26 ^^^ ((e h block 47)).rotateLeft 7) + 0x106aa070 + (a h block 44) + (e h block 44) + (word block 47)) := by
  refine (eWord_succ h ((schedule block).map UInt32.toBitVec) 47).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 44) + ((e h block 44) + bitVecBigSigma1 (e h block 47) + bitVecChoice (e h block 47) (e h block 46) (e h block 45) + 0x106aa070 + (word block 47)) = (((~~~(e h block 47)) &&& (e h block 45)) + ((e h block 46) &&& (e h block 47)) + (((e h block 47)).rotateLeft 21 ^^^ ((e h block 47)).rotateLeft 26 ^^^ ((e h block 47)).rotateLeft 7) + 0x106aa070 + (a h block 44) + (e h block 44) + (word block 47))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]
  generalize (a h block 44) = v0
  generalize (e h block 44) = v1
  generalize (e h block 45) = v2
  generalize (e h block 46) = v3
  generalize (e h block 47) = v4
  generalize (word block 47) = v5
  ac_rfl

theorem a49 (h : BitVecState) (block : Array Bool) :
    (a h block 49) = (((~~~(e h block 48)) &&& (e h block 46)) + ((e h block 47) &&& (e h block 48)) + ((((a h block 46) ^^^ (a h block 47)) &&& (a h block 48)) ^^^ ((a h block 46) &&& (a h block 47))) + (((a h block 48)).rotateLeft 10 ^^^ ((a h block 48)).rotateLeft 19 ^^^ ((a h block 48)).rotateLeft 30) + (((e h block 48)).rotateLeft 21 ^^^ ((e h block 48)).rotateLeft 26 ^^^ ((e h block 48)).rotateLeft 7) + 0x19a4c116 + (e h block 45) + (word block 48)) := by
  refine (aWord_succ h ((schedule block).map UInt32.toBitVec) 48).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 45) + bitVecBigSigma1 (e h block 48) + bitVecChoice (e h block 48) (e h block 47) (e h block 46) + 0x19a4c116 + (word block 48)) + (bitVecBigSigma0 (a h block 48) + bitVecMajority (a h block 48) (a h block 47) (a h block 46)) = (((~~~(e h block 48)) &&& (e h block 46)) + ((e h block 47) &&& (e h block 48)) + ((((a h block 46) ^^^ (a h block 47)) &&& (a h block 48)) ^^^ ((a h block 46) &&& (a h block 47))) + (((a h block 48)).rotateLeft 10 ^^^ ((a h block 48)).rotateLeft 19 ^^^ ((a h block 48)).rotateLeft 30) + (((e h block 48)).rotateLeft 21 ^^^ ((e h block 48)).rotateLeft 26 ^^^ ((e h block 48)).rotateLeft 7) + 0x19a4c116 + (e h block 45) + (word block 48))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]
  generalize (a h block 46) = v0
  generalize (a h block 47) = v1
  generalize (a h block 48) = v2
  generalize (e h block 45) = v3
  generalize (e h block 46) = v4
  generalize (e h block 47) = v5
  generalize (e h block 48) = v6
  generalize (word block 48) = v7
  ac_rfl

theorem e49 (h : BitVecState) (block : Array Bool) :
    (e h block 49) = (((~~~(e h block 48)) &&& (e h block 46)) + ((e h block 47) &&& (e h block 48)) + (((e h block 48)).rotateLeft 21 ^^^ ((e h block 48)).rotateLeft 26 ^^^ ((e h block 48)).rotateLeft 7) + 0x19a4c116 + (a h block 45) + (e h block 45) + (word block 48)) := by
  refine (eWord_succ h ((schedule block).map UInt32.toBitVec) 48).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 45) + ((e h block 45) + bitVecBigSigma1 (e h block 48) + bitVecChoice (e h block 48) (e h block 47) (e h block 46) + 0x19a4c116 + (word block 48)) = (((~~~(e h block 48)) &&& (e h block 46)) + ((e h block 47) &&& (e h block 48)) + (((e h block 48)).rotateLeft 21 ^^^ ((e h block 48)).rotateLeft 26 ^^^ ((e h block 48)).rotateLeft 7) + 0x19a4c116 + (a h block 45) + (e h block 45) + (word block 48))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]
  generalize (a h block 45) = v0
  generalize (e h block 45) = v1
  generalize (e h block 46) = v2
  generalize (e h block 47) = v3
  generalize (e h block 48) = v4
  generalize (word block 48) = v5
  ac_rfl

theorem a50 (h : BitVecState) (block : Array Bool) :
    (a h block 50) = (((~~~(e h block 49)) &&& (e h block 47)) + ((e h block 48) &&& (e h block 49)) + ((((a h block 47) ^^^ (a h block 48)) &&& (a h block 49)) ^^^ ((a h block 47) &&& (a h block 48))) + (((a h block 49)).rotateLeft 10 ^^^ ((a h block 49)).rotateLeft 19 ^^^ ((a h block 49)).rotateLeft 30) + (((e h block 49)).rotateLeft 21 ^^^ ((e h block 49)).rotateLeft 26 ^^^ ((e h block 49)).rotateLeft 7) + 0x1e376c08 + (e h block 46) + (word block 49)) := by
  refine (aWord_succ h ((schedule block).map UInt32.toBitVec) 49).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 46) + bitVecBigSigma1 (e h block 49) + bitVecChoice (e h block 49) (e h block 48) (e h block 47) + 0x1e376c08 + (word block 49)) + (bitVecBigSigma0 (a h block 49) + bitVecMajority (a h block 49) (a h block 48) (a h block 47)) = (((~~~(e h block 49)) &&& (e h block 47)) + ((e h block 48) &&& (e h block 49)) + ((((a h block 47) ^^^ (a h block 48)) &&& (a h block 49)) ^^^ ((a h block 47) &&& (a h block 48))) + (((a h block 49)).rotateLeft 10 ^^^ ((a h block 49)).rotateLeft 19 ^^^ ((a h block 49)).rotateLeft 30) + (((e h block 49)).rotateLeft 21 ^^^ ((e h block 49)).rotateLeft 26 ^^^ ((e h block 49)).rotateLeft 7) + 0x1e376c08 + (e h block 46) + (word block 49))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]
  generalize (a h block 47) = v0
  generalize (a h block 48) = v1
  generalize (a h block 49) = v2
  generalize (e h block 46) = v3
  generalize (e h block 47) = v4
  generalize (e h block 48) = v5
  generalize (e h block 49) = v6
  generalize (word block 49) = v7
  ac_rfl

theorem e50 (h : BitVecState) (block : Array Bool) :
    (e h block 50) = (((~~~(e h block 49)) &&& (e h block 47)) + ((e h block 48) &&& (e h block 49)) + (((e h block 49)).rotateLeft 21 ^^^ ((e h block 49)).rotateLeft 26 ^^^ ((e h block 49)).rotateLeft 7) + 0x1e376c08 + (a h block 46) + (e h block 46) + (word block 49)) := by
  refine (eWord_succ h ((schedule block).map UInt32.toBitVec) 49).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 46) + ((e h block 46) + bitVecBigSigma1 (e h block 49) + bitVecChoice (e h block 49) (e h block 48) (e h block 47) + 0x1e376c08 + (word block 49)) = (((~~~(e h block 49)) &&& (e h block 47)) + ((e h block 48) &&& (e h block 49)) + (((e h block 49)).rotateLeft 21 ^^^ ((e h block 49)).rotateLeft 26 ^^^ ((e h block 49)).rotateLeft 7) + 0x1e376c08 + (a h block 46) + (e h block 46) + (word block 49))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]
  generalize (a h block 46) = v0
  generalize (e h block 46) = v1
  generalize (e h block 47) = v2
  generalize (e h block 48) = v3
  generalize (e h block 49) = v4
  generalize (word block 49) = v5
  ac_rfl

theorem a51 (h : BitVecState) (block : Array Bool) :
    (a h block 51) = (((~~~(e h block 50)) &&& (e h block 48)) + ((e h block 49) &&& (e h block 50)) + ((((a h block 48) ^^^ (a h block 49)) &&& (a h block 50)) ^^^ ((a h block 48) &&& (a h block 49))) + (((a h block 50)).rotateLeft 10 ^^^ ((a h block 50)).rotateLeft 19 ^^^ ((a h block 50)).rotateLeft 30) + (((e h block 50)).rotateLeft 21 ^^^ ((e h block 50)).rotateLeft 26 ^^^ ((e h block 50)).rotateLeft 7) + 0x2748774c + (e h block 47) + (word block 50)) := by
  refine (aWord_succ h ((schedule block).map UInt32.toBitVec) 50).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 47) + bitVecBigSigma1 (e h block 50) + bitVecChoice (e h block 50) (e h block 49) (e h block 48) + 0x2748774c + (word block 50)) + (bitVecBigSigma0 (a h block 50) + bitVecMajority (a h block 50) (a h block 49) (a h block 48)) = (((~~~(e h block 50)) &&& (e h block 48)) + ((e h block 49) &&& (e h block 50)) + ((((a h block 48) ^^^ (a h block 49)) &&& (a h block 50)) ^^^ ((a h block 48) &&& (a h block 49))) + (((a h block 50)).rotateLeft 10 ^^^ ((a h block 50)).rotateLeft 19 ^^^ ((a h block 50)).rotateLeft 30) + (((e h block 50)).rotateLeft 21 ^^^ ((e h block 50)).rotateLeft 26 ^^^ ((e h block 50)).rotateLeft 7) + 0x2748774c + (e h block 47) + (word block 50))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]
  generalize (a h block 48) = v0
  generalize (a h block 49) = v1
  generalize (a h block 50) = v2
  generalize (e h block 47) = v3
  generalize (e h block 48) = v4
  generalize (e h block 49) = v5
  generalize (e h block 50) = v6
  generalize (word block 50) = v7
  ac_rfl

theorem e51 (h : BitVecState) (block : Array Bool) :
    (e h block 51) = (((~~~(e h block 50)) &&& (e h block 48)) + ((e h block 49) &&& (e h block 50)) + (((e h block 50)).rotateLeft 21 ^^^ ((e h block 50)).rotateLeft 26 ^^^ ((e h block 50)).rotateLeft 7) + 0x2748774c + (a h block 47) + (e h block 47) + (word block 50)) := by
  refine (eWord_succ h ((schedule block).map UInt32.toBitVec) 50).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 47) + ((e h block 47) + bitVecBigSigma1 (e h block 50) + bitVecChoice (e h block 50) (e h block 49) (e h block 48) + 0x2748774c + (word block 50)) = (((~~~(e h block 50)) &&& (e h block 48)) + ((e h block 49) &&& (e h block 50)) + (((e h block 50)).rotateLeft 21 ^^^ ((e h block 50)).rotateLeft 26 ^^^ ((e h block 50)).rotateLeft 7) + 0x2748774c + (a h block 47) + (e h block 47) + (word block 50))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]
  generalize (a h block 47) = v0
  generalize (e h block 47) = v1
  generalize (e h block 48) = v2
  generalize (e h block 49) = v3
  generalize (e h block 50) = v4
  generalize (word block 50) = v5
  ac_rfl

theorem a52 (h : BitVecState) (block : Array Bool) :
    (a h block 52) = (((~~~(e h block 51)) &&& (e h block 49)) + ((e h block 50) &&& (e h block 51)) + ((((a h block 49) ^^^ (a h block 50)) &&& (a h block 51)) ^^^ ((a h block 49) &&& (a h block 50))) + (((a h block 51)).rotateLeft 10 ^^^ ((a h block 51)).rotateLeft 19 ^^^ ((a h block 51)).rotateLeft 30) + (((e h block 51)).rotateLeft 21 ^^^ ((e h block 51)).rotateLeft 26 ^^^ ((e h block 51)).rotateLeft 7) + 0x34b0bcb5 + (e h block 48) + (word block 51)) := by
  refine (aWord_succ h ((schedule block).map UInt32.toBitVec) 51).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 48) + bitVecBigSigma1 (e h block 51) + bitVecChoice (e h block 51) (e h block 50) (e h block 49) + 0x34b0bcb5 + (word block 51)) + (bitVecBigSigma0 (a h block 51) + bitVecMajority (a h block 51) (a h block 50) (a h block 49)) = (((~~~(e h block 51)) &&& (e h block 49)) + ((e h block 50) &&& (e h block 51)) + ((((a h block 49) ^^^ (a h block 50)) &&& (a h block 51)) ^^^ ((a h block 49) &&& (a h block 50))) + (((a h block 51)).rotateLeft 10 ^^^ ((a h block 51)).rotateLeft 19 ^^^ ((a h block 51)).rotateLeft 30) + (((e h block 51)).rotateLeft 21 ^^^ ((e h block 51)).rotateLeft 26 ^^^ ((e h block 51)).rotateLeft 7) + 0x34b0bcb5 + (e h block 48) + (word block 51))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]
  generalize (a h block 49) = v0
  generalize (a h block 50) = v1
  generalize (a h block 51) = v2
  generalize (e h block 48) = v3
  generalize (e h block 49) = v4
  generalize (e h block 50) = v5
  generalize (e h block 51) = v6
  generalize (word block 51) = v7
  ac_rfl

theorem e52 (h : BitVecState) (block : Array Bool) :
    (e h block 52) = (((~~~(e h block 51)) &&& (e h block 49)) + ((e h block 50) &&& (e h block 51)) + (((e h block 51)).rotateLeft 21 ^^^ ((e h block 51)).rotateLeft 26 ^^^ ((e h block 51)).rotateLeft 7) + 0x34b0bcb5 + (a h block 48) + (e h block 48) + (word block 51)) := by
  refine (eWord_succ h ((schedule block).map UInt32.toBitVec) 51).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 48) + ((e h block 48) + bitVecBigSigma1 (e h block 51) + bitVecChoice (e h block 51) (e h block 50) (e h block 49) + 0x34b0bcb5 + (word block 51)) = (((~~~(e h block 51)) &&& (e h block 49)) + ((e h block 50) &&& (e h block 51)) + (((e h block 51)).rotateLeft 21 ^^^ ((e h block 51)).rotateLeft 26 ^^^ ((e h block 51)).rotateLeft 7) + 0x34b0bcb5 + (a h block 48) + (e h block 48) + (word block 51))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]
  generalize (a h block 48) = v0
  generalize (e h block 48) = v1
  generalize (e h block 49) = v2
  generalize (e h block 50) = v3
  generalize (e h block 51) = v4
  generalize (word block 51) = v5
  ac_rfl

theorem a53 (h : BitVecState) (block : Array Bool) :
    (a h block 53) = (((~~~(e h block 52)) &&& (e h block 50)) + ((e h block 51) &&& (e h block 52)) + ((((a h block 50) ^^^ (a h block 51)) &&& (a h block 52)) ^^^ ((a h block 50) &&& (a h block 51))) + (((a h block 52)).rotateLeft 10 ^^^ ((a h block 52)).rotateLeft 19 ^^^ ((a h block 52)).rotateLeft 30) + (((e h block 52)).rotateLeft 21 ^^^ ((e h block 52)).rotateLeft 26 ^^^ ((e h block 52)).rotateLeft 7) + 0x391c0cb3 + (e h block 49) + (word block 52)) := by
  refine (aWord_succ h ((schedule block).map UInt32.toBitVec) 52).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 49) + bitVecBigSigma1 (e h block 52) + bitVecChoice (e h block 52) (e h block 51) (e h block 50) + 0x391c0cb3 + (word block 52)) + (bitVecBigSigma0 (a h block 52) + bitVecMajority (a h block 52) (a h block 51) (a h block 50)) = (((~~~(e h block 52)) &&& (e h block 50)) + ((e h block 51) &&& (e h block 52)) + ((((a h block 50) ^^^ (a h block 51)) &&& (a h block 52)) ^^^ ((a h block 50) &&& (a h block 51))) + (((a h block 52)).rotateLeft 10 ^^^ ((a h block 52)).rotateLeft 19 ^^^ ((a h block 52)).rotateLeft 30) + (((e h block 52)).rotateLeft 21 ^^^ ((e h block 52)).rotateLeft 26 ^^^ ((e h block 52)).rotateLeft 7) + 0x391c0cb3 + (e h block 49) + (word block 52))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]
  generalize (a h block 50) = v0
  generalize (a h block 51) = v1
  generalize (a h block 52) = v2
  generalize (e h block 49) = v3
  generalize (e h block 50) = v4
  generalize (e h block 51) = v5
  generalize (e h block 52) = v6
  generalize (word block 52) = v7
  ac_rfl

theorem e53 (h : BitVecState) (block : Array Bool) :
    (e h block 53) = (((~~~(e h block 52)) &&& (e h block 50)) + ((e h block 51) &&& (e h block 52)) + (((e h block 52)).rotateLeft 21 ^^^ ((e h block 52)).rotateLeft 26 ^^^ ((e h block 52)).rotateLeft 7) + 0x391c0cb3 + (a h block 49) + (e h block 49) + (word block 52)) := by
  refine (eWord_succ h ((schedule block).map UInt32.toBitVec) 52).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 49) + ((e h block 49) + bitVecBigSigma1 (e h block 52) + bitVecChoice (e h block 52) (e h block 51) (e h block 50) + 0x391c0cb3 + (word block 52)) = (((~~~(e h block 52)) &&& (e h block 50)) + ((e h block 51) &&& (e h block 52)) + (((e h block 52)).rotateLeft 21 ^^^ ((e h block 52)).rotateLeft 26 ^^^ ((e h block 52)).rotateLeft 7) + 0x391c0cb3 + (a h block 49) + (e h block 49) + (word block 52))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]
  generalize (a h block 49) = v0
  generalize (e h block 49) = v1
  generalize (e h block 50) = v2
  generalize (e h block 51) = v3
  generalize (e h block 52) = v4
  generalize (word block 52) = v5
  ac_rfl

theorem a54 (h : BitVecState) (block : Array Bool) :
    (a h block 54) = (((~~~(e h block 53)) &&& (e h block 51)) + ((e h block 52) &&& (e h block 53)) + ((((a h block 51) ^^^ (a h block 52)) &&& (a h block 53)) ^^^ ((a h block 51) &&& (a h block 52))) + (((a h block 53)).rotateLeft 10 ^^^ ((a h block 53)).rotateLeft 19 ^^^ ((a h block 53)).rotateLeft 30) + (((e h block 53)).rotateLeft 21 ^^^ ((e h block 53)).rotateLeft 26 ^^^ ((e h block 53)).rotateLeft 7) + 0x4ed8aa4a + (e h block 50) + (word block 53)) := by
  refine (aWord_succ h ((schedule block).map UInt32.toBitVec) 53).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 50) + bitVecBigSigma1 (e h block 53) + bitVecChoice (e h block 53) (e h block 52) (e h block 51) + 0x4ed8aa4a + (word block 53)) + (bitVecBigSigma0 (a h block 53) + bitVecMajority (a h block 53) (a h block 52) (a h block 51)) = (((~~~(e h block 53)) &&& (e h block 51)) + ((e h block 52) &&& (e h block 53)) + ((((a h block 51) ^^^ (a h block 52)) &&& (a h block 53)) ^^^ ((a h block 51) &&& (a h block 52))) + (((a h block 53)).rotateLeft 10 ^^^ ((a h block 53)).rotateLeft 19 ^^^ ((a h block 53)).rotateLeft 30) + (((e h block 53)).rotateLeft 21 ^^^ ((e h block 53)).rotateLeft 26 ^^^ ((e h block 53)).rotateLeft 7) + 0x4ed8aa4a + (e h block 50) + (word block 53))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]
  generalize (a h block 51) = v0
  generalize (a h block 52) = v1
  generalize (a h block 53) = v2
  generalize (e h block 50) = v3
  generalize (e h block 51) = v4
  generalize (e h block 52) = v5
  generalize (e h block 53) = v6
  generalize (word block 53) = v7
  ac_rfl

theorem e54 (h : BitVecState) (block : Array Bool) :
    (e h block 54) = (((~~~(e h block 53)) &&& (e h block 51)) + ((e h block 52) &&& (e h block 53)) + (((e h block 53)).rotateLeft 21 ^^^ ((e h block 53)).rotateLeft 26 ^^^ ((e h block 53)).rotateLeft 7) + 0x4ed8aa4a + (a h block 50) + (e h block 50) + (word block 53)) := by
  refine (eWord_succ h ((schedule block).map UInt32.toBitVec) 53).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 50) + ((e h block 50) + bitVecBigSigma1 (e h block 53) + bitVecChoice (e h block 53) (e h block 52) (e h block 51) + 0x4ed8aa4a + (word block 53)) = (((~~~(e h block 53)) &&& (e h block 51)) + ((e h block 52) &&& (e h block 53)) + (((e h block 53)).rotateLeft 21 ^^^ ((e h block 53)).rotateLeft 26 ^^^ ((e h block 53)).rotateLeft 7) + 0x4ed8aa4a + (a h block 50) + (e h block 50) + (word block 53))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]
  generalize (a h block 50) = v0
  generalize (e h block 50) = v1
  generalize (e h block 51) = v2
  generalize (e h block 52) = v3
  generalize (e h block 53) = v4
  generalize (word block 53) = v5
  ac_rfl

theorem a55 (h : BitVecState) (block : Array Bool) :
    (a h block 55) = (((~~~(e h block 54)) &&& (e h block 52)) + ((e h block 53) &&& (e h block 54)) + ((((a h block 52) ^^^ (a h block 53)) &&& (a h block 54)) ^^^ ((a h block 52) &&& (a h block 53))) + (((a h block 54)).rotateLeft 10 ^^^ ((a h block 54)).rotateLeft 19 ^^^ ((a h block 54)).rotateLeft 30) + (((e h block 54)).rotateLeft 21 ^^^ ((e h block 54)).rotateLeft 26 ^^^ ((e h block 54)).rotateLeft 7) + 0x5b9cca4f + (e h block 51) + (word block 54)) := by
  refine (aWord_succ h ((schedule block).map UInt32.toBitVec) 54).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 51) + bitVecBigSigma1 (e h block 54) + bitVecChoice (e h block 54) (e h block 53) (e h block 52) + 0x5b9cca4f + (word block 54)) + (bitVecBigSigma0 (a h block 54) + bitVecMajority (a h block 54) (a h block 53) (a h block 52)) = (((~~~(e h block 54)) &&& (e h block 52)) + ((e h block 53) &&& (e h block 54)) + ((((a h block 52) ^^^ (a h block 53)) &&& (a h block 54)) ^^^ ((a h block 52) &&& (a h block 53))) + (((a h block 54)).rotateLeft 10 ^^^ ((a h block 54)).rotateLeft 19 ^^^ ((a h block 54)).rotateLeft 30) + (((e h block 54)).rotateLeft 21 ^^^ ((e h block 54)).rotateLeft 26 ^^^ ((e h block 54)).rotateLeft 7) + 0x5b9cca4f + (e h block 51) + (word block 54))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]
  generalize (a h block 52) = v0
  generalize (a h block 53) = v1
  generalize (a h block 54) = v2
  generalize (e h block 51) = v3
  generalize (e h block 52) = v4
  generalize (e h block 53) = v5
  generalize (e h block 54) = v6
  generalize (word block 54) = v7
  ac_rfl

theorem e55 (h : BitVecState) (block : Array Bool) :
    (e h block 55) = (((~~~(e h block 54)) &&& (e h block 52)) + ((e h block 53) &&& (e h block 54)) + (((e h block 54)).rotateLeft 21 ^^^ ((e h block 54)).rotateLeft 26 ^^^ ((e h block 54)).rotateLeft 7) + 0x5b9cca4f + (a h block 51) + (e h block 51) + (word block 54)) := by
  refine (eWord_succ h ((schedule block).map UInt32.toBitVec) 54).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 51) + ((e h block 51) + bitVecBigSigma1 (e h block 54) + bitVecChoice (e h block 54) (e h block 53) (e h block 52) + 0x5b9cca4f + (word block 54)) = (((~~~(e h block 54)) &&& (e h block 52)) + ((e h block 53) &&& (e h block 54)) + (((e h block 54)).rotateLeft 21 ^^^ ((e h block 54)).rotateLeft 26 ^^^ ((e h block 54)).rotateLeft 7) + 0x5b9cca4f + (a h block 51) + (e h block 51) + (word block 54))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]
  generalize (a h block 51) = v0
  generalize (e h block 51) = v1
  generalize (e h block 52) = v2
  generalize (e h block 53) = v3
  generalize (e h block 54) = v4
  generalize (word block 54) = v5
  ac_rfl

theorem a56 (h : BitVecState) (block : Array Bool) :
    (a h block 56) = (((~~~(e h block 55)) &&& (e h block 53)) + ((e h block 54) &&& (e h block 55)) + ((((a h block 53) ^^^ (a h block 54)) &&& (a h block 55)) ^^^ ((a h block 53) &&& (a h block 54))) + (((a h block 55)).rotateLeft 10 ^^^ ((a h block 55)).rotateLeft 19 ^^^ ((a h block 55)).rotateLeft 30) + (((e h block 55)).rotateLeft 21 ^^^ ((e h block 55)).rotateLeft 26 ^^^ ((e h block 55)).rotateLeft 7) + 0x682e6ff3 + (e h block 52) + (word block 55)) := by
  refine (aWord_succ h ((schedule block).map UInt32.toBitVec) 55).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 52) + bitVecBigSigma1 (e h block 55) + bitVecChoice (e h block 55) (e h block 54) (e h block 53) + 0x682e6ff3 + (word block 55)) + (bitVecBigSigma0 (a h block 55) + bitVecMajority (a h block 55) (a h block 54) (a h block 53)) = (((~~~(e h block 55)) &&& (e h block 53)) + ((e h block 54) &&& (e h block 55)) + ((((a h block 53) ^^^ (a h block 54)) &&& (a h block 55)) ^^^ ((a h block 53) &&& (a h block 54))) + (((a h block 55)).rotateLeft 10 ^^^ ((a h block 55)).rotateLeft 19 ^^^ ((a h block 55)).rotateLeft 30) + (((e h block 55)).rotateLeft 21 ^^^ ((e h block 55)).rotateLeft 26 ^^^ ((e h block 55)).rotateLeft 7) + 0x682e6ff3 + (e h block 52) + (word block 55))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]
  generalize (a h block 53) = v0
  generalize (a h block 54) = v1
  generalize (a h block 55) = v2
  generalize (e h block 52) = v3
  generalize (e h block 53) = v4
  generalize (e h block 54) = v5
  generalize (e h block 55) = v6
  generalize (word block 55) = v7
  ac_rfl

theorem e56 (h : BitVecState) (block : Array Bool) :
    (e h block 56) = (((~~~(e h block 55)) &&& (e h block 53)) + ((e h block 54) &&& (e h block 55)) + (((e h block 55)).rotateLeft 21 ^^^ ((e h block 55)).rotateLeft 26 ^^^ ((e h block 55)).rotateLeft 7) + 0x682e6ff3 + (a h block 52) + (e h block 52) + (word block 55)) := by
  refine (eWord_succ h ((schedule block).map UInt32.toBitVec) 55).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 52) + ((e h block 52) + bitVecBigSigma1 (e h block 55) + bitVecChoice (e h block 55) (e h block 54) (e h block 53) + 0x682e6ff3 + (word block 55)) = (((~~~(e h block 55)) &&& (e h block 53)) + ((e h block 54) &&& (e h block 55)) + (((e h block 55)).rotateLeft 21 ^^^ ((e h block 55)).rotateLeft 26 ^^^ ((e h block 55)).rotateLeft 7) + 0x682e6ff3 + (a h block 52) + (e h block 52) + (word block 55))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]
  generalize (a h block 52) = v0
  generalize (e h block 52) = v1
  generalize (e h block 53) = v2
  generalize (e h block 54) = v3
  generalize (e h block 55) = v4
  generalize (word block 55) = v5
  ac_rfl

theorem a57 (h : BitVecState) (block : Array Bool) :
    (a h block 57) = (((~~~(e h block 56)) &&& (e h block 54)) + ((e h block 55) &&& (e h block 56)) + ((((a h block 54) ^^^ (a h block 55)) &&& (a h block 56)) ^^^ ((a h block 54) &&& (a h block 55))) + (((a h block 56)).rotateLeft 10 ^^^ ((a h block 56)).rotateLeft 19 ^^^ ((a h block 56)).rotateLeft 30) + (((e h block 56)).rotateLeft 21 ^^^ ((e h block 56)).rotateLeft 26 ^^^ ((e h block 56)).rotateLeft 7) + 0x748f82ee + (e h block 53) + (word block 56)) := by
  refine (aWord_succ h ((schedule block).map UInt32.toBitVec) 56).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 53) + bitVecBigSigma1 (e h block 56) + bitVecChoice (e h block 56) (e h block 55) (e h block 54) + 0x748f82ee + (word block 56)) + (bitVecBigSigma0 (a h block 56) + bitVecMajority (a h block 56) (a h block 55) (a h block 54)) = (((~~~(e h block 56)) &&& (e h block 54)) + ((e h block 55) &&& (e h block 56)) + ((((a h block 54) ^^^ (a h block 55)) &&& (a h block 56)) ^^^ ((a h block 54) &&& (a h block 55))) + (((a h block 56)).rotateLeft 10 ^^^ ((a h block 56)).rotateLeft 19 ^^^ ((a h block 56)).rotateLeft 30) + (((e h block 56)).rotateLeft 21 ^^^ ((e h block 56)).rotateLeft 26 ^^^ ((e h block 56)).rotateLeft 7) + 0x748f82ee + (e h block 53) + (word block 56))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]
  generalize (a h block 54) = v0
  generalize (a h block 55) = v1
  generalize (a h block 56) = v2
  generalize (e h block 53) = v3
  generalize (e h block 54) = v4
  generalize (e h block 55) = v5
  generalize (e h block 56) = v6
  generalize (word block 56) = v7
  ac_rfl

theorem e57 (h : BitVecState) (block : Array Bool) :
    (e h block 57) = (((~~~(e h block 56)) &&& (e h block 54)) + ((e h block 55) &&& (e h block 56)) + (((e h block 56)).rotateLeft 21 ^^^ ((e h block 56)).rotateLeft 26 ^^^ ((e h block 56)).rotateLeft 7) + 0x748f82ee + (a h block 53) + (e h block 53) + (word block 56)) := by
  refine (eWord_succ h ((schedule block).map UInt32.toBitVec) 56).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 53) + ((e h block 53) + bitVecBigSigma1 (e h block 56) + bitVecChoice (e h block 56) (e h block 55) (e h block 54) + 0x748f82ee + (word block 56)) = (((~~~(e h block 56)) &&& (e h block 54)) + ((e h block 55) &&& (e h block 56)) + (((e h block 56)).rotateLeft 21 ^^^ ((e h block 56)).rotateLeft 26 ^^^ ((e h block 56)).rotateLeft 7) + 0x748f82ee + (a h block 53) + (e h block 53) + (word block 56))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]
  generalize (a h block 53) = v0
  generalize (e h block 53) = v1
  generalize (e h block 54) = v2
  generalize (e h block 55) = v3
  generalize (e h block 56) = v4
  generalize (word block 56) = v5
  ac_rfl

theorem a58 (h : BitVecState) (block : Array Bool) :
    (a h block 58) = (((~~~(e h block 57)) &&& (e h block 55)) + ((e h block 56) &&& (e h block 57)) + ((((a h block 55) ^^^ (a h block 56)) &&& (a h block 57)) ^^^ ((a h block 55) &&& (a h block 56))) + (((a h block 57)).rotateLeft 10 ^^^ ((a h block 57)).rotateLeft 19 ^^^ ((a h block 57)).rotateLeft 30) + (((e h block 57)).rotateLeft 21 ^^^ ((e h block 57)).rotateLeft 26 ^^^ ((e h block 57)).rotateLeft 7) + 0x78a5636f + (e h block 54) + (word block 57)) := by
  refine (aWord_succ h ((schedule block).map UInt32.toBitVec) 57).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 54) + bitVecBigSigma1 (e h block 57) + bitVecChoice (e h block 57) (e h block 56) (e h block 55) + 0x78a5636f + (word block 57)) + (bitVecBigSigma0 (a h block 57) + bitVecMajority (a h block 57) (a h block 56) (a h block 55)) = (((~~~(e h block 57)) &&& (e h block 55)) + ((e h block 56) &&& (e h block 57)) + ((((a h block 55) ^^^ (a h block 56)) &&& (a h block 57)) ^^^ ((a h block 55) &&& (a h block 56))) + (((a h block 57)).rotateLeft 10 ^^^ ((a h block 57)).rotateLeft 19 ^^^ ((a h block 57)).rotateLeft 30) + (((e h block 57)).rotateLeft 21 ^^^ ((e h block 57)).rotateLeft 26 ^^^ ((e h block 57)).rotateLeft 7) + 0x78a5636f + (e h block 54) + (word block 57))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]
  generalize (a h block 55) = v0
  generalize (a h block 56) = v1
  generalize (a h block 57) = v2
  generalize (e h block 54) = v3
  generalize (e h block 55) = v4
  generalize (e h block 56) = v5
  generalize (e h block 57) = v6
  generalize (word block 57) = v7
  ac_rfl

theorem e58 (h : BitVecState) (block : Array Bool) :
    (e h block 58) = (((~~~(e h block 57)) &&& (e h block 55)) + ((e h block 56) &&& (e h block 57)) + (((e h block 57)).rotateLeft 21 ^^^ ((e h block 57)).rotateLeft 26 ^^^ ((e h block 57)).rotateLeft 7) + 0x78a5636f + (a h block 54) + (e h block 54) + (word block 57)) := by
  refine (eWord_succ h ((schedule block).map UInt32.toBitVec) 57).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 54) + ((e h block 54) + bitVecBigSigma1 (e h block 57) + bitVecChoice (e h block 57) (e h block 56) (e h block 55) + 0x78a5636f + (word block 57)) = (((~~~(e h block 57)) &&& (e h block 55)) + ((e h block 56) &&& (e h block 57)) + (((e h block 57)).rotateLeft 21 ^^^ ((e h block 57)).rotateLeft 26 ^^^ ((e h block 57)).rotateLeft 7) + 0x78a5636f + (a h block 54) + (e h block 54) + (word block 57))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]
  generalize (a h block 54) = v0
  generalize (e h block 54) = v1
  generalize (e h block 55) = v2
  generalize (e h block 56) = v3
  generalize (e h block 57) = v4
  generalize (word block 57) = v5
  ac_rfl

theorem a59 (h : BitVecState) (block : Array Bool) :
    (a h block 59) = (((~~~(e h block 58)) &&& (e h block 56)) + ((e h block 57) &&& (e h block 58)) + ((((a h block 56) ^^^ (a h block 57)) &&& (a h block 58)) ^^^ ((a h block 56) &&& (a h block 57))) + (((a h block 58)).rotateLeft 10 ^^^ ((a h block 58)).rotateLeft 19 ^^^ ((a h block 58)).rotateLeft 30) + (((e h block 58)).rotateLeft 21 ^^^ ((e h block 58)).rotateLeft 26 ^^^ ((e h block 58)).rotateLeft 7) + 0x84c87814 + (e h block 55) + (word block 58)) := by
  refine (aWord_succ h ((schedule block).map UInt32.toBitVec) 58).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 55) + bitVecBigSigma1 (e h block 58) + bitVecChoice (e h block 58) (e h block 57) (e h block 56) + 0x84c87814 + (word block 58)) + (bitVecBigSigma0 (a h block 58) + bitVecMajority (a h block 58) (a h block 57) (a h block 56)) = (((~~~(e h block 58)) &&& (e h block 56)) + ((e h block 57) &&& (e h block 58)) + ((((a h block 56) ^^^ (a h block 57)) &&& (a h block 58)) ^^^ ((a h block 56) &&& (a h block 57))) + (((a h block 58)).rotateLeft 10 ^^^ ((a h block 58)).rotateLeft 19 ^^^ ((a h block 58)).rotateLeft 30) + (((e h block 58)).rotateLeft 21 ^^^ ((e h block 58)).rotateLeft 26 ^^^ ((e h block 58)).rotateLeft 7) + 0x84c87814 + (e h block 55) + (word block 58))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]
  generalize (a h block 56) = v0
  generalize (a h block 57) = v1
  generalize (a h block 58) = v2
  generalize (e h block 55) = v3
  generalize (e h block 56) = v4
  generalize (e h block 57) = v5
  generalize (e h block 58) = v6
  generalize (word block 58) = v7
  ac_rfl

theorem e59 (h : BitVecState) (block : Array Bool) :
    (e h block 59) = (((~~~(e h block 58)) &&& (e h block 56)) + ((e h block 57) &&& (e h block 58)) + (((e h block 58)).rotateLeft 21 ^^^ ((e h block 58)).rotateLeft 26 ^^^ ((e h block 58)).rotateLeft 7) + 0x84c87814 + (a h block 55) + (e h block 55) + (word block 58)) := by
  refine (eWord_succ h ((schedule block).map UInt32.toBitVec) 58).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 55) + ((e h block 55) + bitVecBigSigma1 (e h block 58) + bitVecChoice (e h block 58) (e h block 57) (e h block 56) + 0x84c87814 + (word block 58)) = (((~~~(e h block 58)) &&& (e h block 56)) + ((e h block 57) &&& (e h block 58)) + (((e h block 58)).rotateLeft 21 ^^^ ((e h block 58)).rotateLeft 26 ^^^ ((e h block 58)).rotateLeft 7) + 0x84c87814 + (a h block 55) + (e h block 55) + (word block 58))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]
  generalize (a h block 55) = v0
  generalize (e h block 55) = v1
  generalize (e h block 56) = v2
  generalize (e h block 57) = v3
  generalize (e h block 58) = v4
  generalize (word block 58) = v5
  ac_rfl

theorem a60 (h : BitVecState) (block : Array Bool) :
    (a h block 60) = (((~~~(e h block 59)) &&& (e h block 57)) + ((e h block 58) &&& (e h block 59)) + ((((a h block 57) ^^^ (a h block 58)) &&& (a h block 59)) ^^^ ((a h block 57) &&& (a h block 58))) + (((a h block 59)).rotateLeft 10 ^^^ ((a h block 59)).rotateLeft 19 ^^^ ((a h block 59)).rotateLeft 30) + (((e h block 59)).rotateLeft 21 ^^^ ((e h block 59)).rotateLeft 26 ^^^ ((e h block 59)).rotateLeft 7) + 0x8cc70208 + (e h block 56) + (word block 59)) := by
  refine (aWord_succ h ((schedule block).map UInt32.toBitVec) 59).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 56) + bitVecBigSigma1 (e h block 59) + bitVecChoice (e h block 59) (e h block 58) (e h block 57) + 0x8cc70208 + (word block 59)) + (bitVecBigSigma0 (a h block 59) + bitVecMajority (a h block 59) (a h block 58) (a h block 57)) = (((~~~(e h block 59)) &&& (e h block 57)) + ((e h block 58) &&& (e h block 59)) + ((((a h block 57) ^^^ (a h block 58)) &&& (a h block 59)) ^^^ ((a h block 57) &&& (a h block 58))) + (((a h block 59)).rotateLeft 10 ^^^ ((a h block 59)).rotateLeft 19 ^^^ ((a h block 59)).rotateLeft 30) + (((e h block 59)).rotateLeft 21 ^^^ ((e h block 59)).rotateLeft 26 ^^^ ((e h block 59)).rotateLeft 7) + 0x8cc70208 + (e h block 56) + (word block 59))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]
  generalize (a h block 57) = v0
  generalize (a h block 58) = v1
  generalize (a h block 59) = v2
  generalize (e h block 56) = v3
  generalize (e h block 57) = v4
  generalize (e h block 58) = v5
  generalize (e h block 59) = v6
  generalize (word block 59) = v7
  ac_rfl

theorem e60 (h : BitVecState) (block : Array Bool) :
    (e h block 60) = (((~~~(e h block 59)) &&& (e h block 57)) + ((e h block 58) &&& (e h block 59)) + (((e h block 59)).rotateLeft 21 ^^^ ((e h block 59)).rotateLeft 26 ^^^ ((e h block 59)).rotateLeft 7) + 0x8cc70208 + (a h block 56) + (e h block 56) + (word block 59)) := by
  refine (eWord_succ h ((schedule block).map UInt32.toBitVec) 59).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 56) + ((e h block 56) + bitVecBigSigma1 (e h block 59) + bitVecChoice (e h block 59) (e h block 58) (e h block 57) + 0x8cc70208 + (word block 59)) = (((~~~(e h block 59)) &&& (e h block 57)) + ((e h block 58) &&& (e h block 59)) + (((e h block 59)).rotateLeft 21 ^^^ ((e h block 59)).rotateLeft 26 ^^^ ((e h block 59)).rotateLeft 7) + 0x8cc70208 + (a h block 56) + (e h block 56) + (word block 59))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]
  generalize (a h block 56) = v0
  generalize (e h block 56) = v1
  generalize (e h block 57) = v2
  generalize (e h block 58) = v3
  generalize (e h block 59) = v4
  generalize (word block 59) = v5
  ac_rfl

theorem a61 (h : BitVecState) (block : Array Bool) :
    (a h block 61) = (((~~~(e h block 60)) &&& (e h block 58)) + ((e h block 59) &&& (e h block 60)) + ((((a h block 58) ^^^ (a h block 59)) &&& (a h block 60)) ^^^ ((a h block 58) &&& (a h block 59))) + (((a h block 60)).rotateLeft 10 ^^^ ((a h block 60)).rotateLeft 19 ^^^ ((a h block 60)).rotateLeft 30) + (((e h block 60)).rotateLeft 21 ^^^ ((e h block 60)).rotateLeft 26 ^^^ ((e h block 60)).rotateLeft 7) + 0x90befffa + (e h block 57) + (word block 60)) := by
  refine (aWord_succ h ((schedule block).map UInt32.toBitVec) 60).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 57) + bitVecBigSigma1 (e h block 60) + bitVecChoice (e h block 60) (e h block 59) (e h block 58) + 0x90befffa + (word block 60)) + (bitVecBigSigma0 (a h block 60) + bitVecMajority (a h block 60) (a h block 59) (a h block 58)) = (((~~~(e h block 60)) &&& (e h block 58)) + ((e h block 59) &&& (e h block 60)) + ((((a h block 58) ^^^ (a h block 59)) &&& (a h block 60)) ^^^ ((a h block 58) &&& (a h block 59))) + (((a h block 60)).rotateLeft 10 ^^^ ((a h block 60)).rotateLeft 19 ^^^ ((a h block 60)).rotateLeft 30) + (((e h block 60)).rotateLeft 21 ^^^ ((e h block 60)).rotateLeft 26 ^^^ ((e h block 60)).rotateLeft 7) + 0x90befffa + (e h block 57) + (word block 60))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]
  generalize (a h block 58) = v0
  generalize (a h block 59) = v1
  generalize (a h block 60) = v2
  generalize (e h block 57) = v3
  generalize (e h block 58) = v4
  generalize (e h block 59) = v5
  generalize (e h block 60) = v6
  generalize (word block 60) = v7
  ac_rfl

theorem e61 (h : BitVecState) (block : Array Bool) :
    (e h block 61) = (((~~~(e h block 60)) &&& (e h block 58)) + ((e h block 59) &&& (e h block 60)) + (((e h block 60)).rotateLeft 21 ^^^ ((e h block 60)).rotateLeft 26 ^^^ ((e h block 60)).rotateLeft 7) + 0x90befffa + (a h block 57) + (e h block 57) + (word block 60)) := by
  refine (eWord_succ h ((schedule block).map UInt32.toBitVec) 60).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 57) + ((e h block 57) + bitVecBigSigma1 (e h block 60) + bitVecChoice (e h block 60) (e h block 59) (e h block 58) + 0x90befffa + (word block 60)) = (((~~~(e h block 60)) &&& (e h block 58)) + ((e h block 59) &&& (e h block 60)) + (((e h block 60)).rotateLeft 21 ^^^ ((e h block 60)).rotateLeft 26 ^^^ ((e h block 60)).rotateLeft 7) + 0x90befffa + (a h block 57) + (e h block 57) + (word block 60))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]
  generalize (a h block 57) = v0
  generalize (e h block 57) = v1
  generalize (e h block 58) = v2
  generalize (e h block 59) = v3
  generalize (e h block 60) = v4
  generalize (word block 60) = v5
  ac_rfl

theorem a62 (h : BitVecState) (block : Array Bool) :
    (a h block 62) = (((~~~(e h block 61)) &&& (e h block 59)) + ((e h block 60) &&& (e h block 61)) + ((((a h block 59) ^^^ (a h block 60)) &&& (a h block 61)) ^^^ ((a h block 59) &&& (a h block 60))) + (((a h block 61)).rotateLeft 10 ^^^ ((a h block 61)).rotateLeft 19 ^^^ ((a h block 61)).rotateLeft 30) + (((e h block 61)).rotateLeft 21 ^^^ ((e h block 61)).rotateLeft 26 ^^^ ((e h block 61)).rotateLeft 7) + 0xa4506ceb + (e h block 58) + (word block 61)) := by
  refine (aWord_succ h ((schedule block).map UInt32.toBitVec) 61).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 58) + bitVecBigSigma1 (e h block 61) + bitVecChoice (e h block 61) (e h block 60) (e h block 59) + 0xa4506ceb + (word block 61)) + (bitVecBigSigma0 (a h block 61) + bitVecMajority (a h block 61) (a h block 60) (a h block 59)) = (((~~~(e h block 61)) &&& (e h block 59)) + ((e h block 60) &&& (e h block 61)) + ((((a h block 59) ^^^ (a h block 60)) &&& (a h block 61)) ^^^ ((a h block 59) &&& (a h block 60))) + (((a h block 61)).rotateLeft 10 ^^^ ((a h block 61)).rotateLeft 19 ^^^ ((a h block 61)).rotateLeft 30) + (((e h block 61)).rotateLeft 21 ^^^ ((e h block 61)).rotateLeft 26 ^^^ ((e h block 61)).rotateLeft 7) + 0xa4506ceb + (e h block 58) + (word block 61))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]
  generalize (a h block 59) = v0
  generalize (a h block 60) = v1
  generalize (a h block 61) = v2
  generalize (e h block 58) = v3
  generalize (e h block 59) = v4
  generalize (e h block 60) = v5
  generalize (e h block 61) = v6
  generalize (word block 61) = v7
  ac_rfl

theorem e62 (h : BitVecState) (block : Array Bool) :
    (e h block 62) = (((~~~(e h block 61)) &&& (e h block 59)) + ((e h block 60) &&& (e h block 61)) + (((e h block 61)).rotateLeft 21 ^^^ ((e h block 61)).rotateLeft 26 ^^^ ((e h block 61)).rotateLeft 7) + 0xa4506ceb + (a h block 58) + (e h block 58) + (word block 61)) := by
  refine (eWord_succ h ((schedule block).map UInt32.toBitVec) 61).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 58) + ((e h block 58) + bitVecBigSigma1 (e h block 61) + bitVecChoice (e h block 61) (e h block 60) (e h block 59) + 0xa4506ceb + (word block 61)) = (((~~~(e h block 61)) &&& (e h block 59)) + ((e h block 60) &&& (e h block 61)) + (((e h block 61)).rotateLeft 21 ^^^ ((e h block 61)).rotateLeft 26 ^^^ ((e h block 61)).rotateLeft 7) + 0xa4506ceb + (a h block 58) + (e h block 58) + (word block 61))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]
  generalize (a h block 58) = v0
  generalize (e h block 58) = v1
  generalize (e h block 59) = v2
  generalize (e h block 60) = v3
  generalize (e h block 61) = v4
  generalize (word block 61) = v5
  ac_rfl

theorem a63 (h : BitVecState) (block : Array Bool) :
    (a h block 63) = (((~~~(e h block 62)) &&& (e h block 60)) + ((e h block 61) &&& (e h block 62)) + ((((a h block 60) ^^^ (a h block 61)) &&& (a h block 62)) ^^^ ((a h block 60) &&& (a h block 61))) + (((a h block 62)).rotateLeft 10 ^^^ ((a h block 62)).rotateLeft 19 ^^^ ((a h block 62)).rotateLeft 30) + (((e h block 62)).rotateLeft 21 ^^^ ((e h block 62)).rotateLeft 26 ^^^ ((e h block 62)).rotateLeft 7) + 0xbef9a3f7 + (e h block 59) + (word block 62)) := by
  refine (aWord_succ h ((schedule block).map UInt32.toBitVec) 62).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 59) + bitVecBigSigma1 (e h block 62) + bitVecChoice (e h block 62) (e h block 61) (e h block 60) + 0xbef9a3f7 + (word block 62)) + (bitVecBigSigma0 (a h block 62) + bitVecMajority (a h block 62) (a h block 61) (a h block 60)) = (((~~~(e h block 62)) &&& (e h block 60)) + ((e h block 61) &&& (e h block 62)) + ((((a h block 60) ^^^ (a h block 61)) &&& (a h block 62)) ^^^ ((a h block 60) &&& (a h block 61))) + (((a h block 62)).rotateLeft 10 ^^^ ((a h block 62)).rotateLeft 19 ^^^ ((a h block 62)).rotateLeft 30) + (((e h block 62)).rotateLeft 21 ^^^ ((e h block 62)).rotateLeft 26 ^^^ ((e h block 62)).rotateLeft 7) + 0xbef9a3f7 + (e h block 59) + (word block 62))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]
  generalize (a h block 60) = v0
  generalize (a h block 61) = v1
  generalize (a h block 62) = v2
  generalize (e h block 59) = v3
  generalize (e h block 60) = v4
  generalize (e h block 61) = v5
  generalize (e h block 62) = v6
  generalize (word block 62) = v7
  ac_rfl

theorem e63 (h : BitVecState) (block : Array Bool) :
    (e h block 63) = (((~~~(e h block 62)) &&& (e h block 60)) + ((e h block 61) &&& (e h block 62)) + (((e h block 62)).rotateLeft 21 ^^^ ((e h block 62)).rotateLeft 26 ^^^ ((e h block 62)).rotateLeft 7) + 0xbef9a3f7 + (a h block 59) + (e h block 59) + (word block 62)) := by
  refine (eWord_succ h ((schedule block).map UInt32.toBitVec) 62).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 59) + ((e h block 59) + bitVecBigSigma1 (e h block 62) + bitVecChoice (e h block 62) (e h block 61) (e h block 60) + 0xbef9a3f7 + (word block 62)) = (((~~~(e h block 62)) &&& (e h block 60)) + ((e h block 61) &&& (e h block 62)) + (((e h block 62)).rotateLeft 21 ^^^ ((e h block 62)).rotateLeft 26 ^^^ ((e h block 62)).rotateLeft 7) + 0xbef9a3f7 + (a h block 59) + (e h block 59) + (word block 62))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]
  generalize (a h block 59) = v0
  generalize (e h block 59) = v1
  generalize (e h block 60) = v2
  generalize (e h block 61) = v3
  generalize (e h block 62) = v4
  generalize (word block 62) = v5
  ac_rfl

theorem a64 (h : BitVecState) (block : Array Bool) :
    (a h block 64) = (((~~~(e h block 63)) &&& (e h block 61)) + ((e h block 62) &&& (e h block 63)) + ((((a h block 61) ^^^ (a h block 62)) &&& (a h block 63)) ^^^ ((a h block 61) &&& (a h block 62))) + (((a h block 63)).rotateLeft 10 ^^^ ((a h block 63)).rotateLeft 19 ^^^ ((a h block 63)).rotateLeft 30) + (((e h block 63)).rotateLeft 21 ^^^ ((e h block 63)).rotateLeft 26 ^^^ ((e h block 63)).rotateLeft 7) + 0xc67178f2 + (e h block 60) + (word block 63)) := by
  refine (aWord_succ h ((schedule block).map UInt32.toBitVec) 63).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change ((e h block 60) + bitVecBigSigma1 (e h block 63) + bitVecChoice (e h block 63) (e h block 62) (e h block 61) + 0xc67178f2 + (word block 63)) + (bitVecBigSigma0 (a h block 63) + bitVecMajority (a h block 63) (a h block 62) (a h block 61)) = (((~~~(e h block 63)) &&& (e h block 61)) + ((e h block 62) &&& (e h block 63)) + ((((a h block 61) ^^^ (a h block 62)) &&& (a h block 63)) ^^^ ((a h block 61) &&& (a h block 62))) + (((a h block 63)).rotateLeft 10 ^^^ ((a h block 63)).rotateLeft 19 ^^^ ((a h block 63)).rotateLeft 30) + (((e h block 63)).rotateLeft 21 ^^^ ((e h block 63)).rotateLeft 26 ^^^ ((e h block 63)).rotateLeft 7) + 0xc67178f2 + (e h block 60) + (word block 63))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and, bitVecBigSigma0, bitVecMajority_eq_and_xor]
  generalize (a h block 61) = v0
  generalize (a h block 62) = v1
  generalize (a h block 63) = v2
  generalize (e h block 60) = v3
  generalize (e h block 61) = v4
  generalize (e h block 62) = v5
  generalize (e h block 63) = v6
  generalize (word block 63) = v7
  ac_rfl

theorem e64 (h : BitVecState) (block : Array Bool) :
    (e h block 64) = (((~~~(e h block 63)) &&& (e h block 61)) + ((e h block 62) &&& (e h block 63)) + (((e h block 63)).rotateLeft 21 ^^^ ((e h block 63)).rotateLeft 26 ^^^ ((e h block 63)).rotateLeft 7) + 0xc67178f2 + (a h block 60) + (e h block 60) + (word block 63)) := by
  refine (eWord_succ h ((schedule block).map UInt32.toBitVec) 63).trans ?_
  simp only [map_toBitVec_getElem!, Nat.reduceAdd]
  change (a h block 60) + ((e h block 60) + bitVecBigSigma1 (e h block 63) + bitVecChoice (e h block 63) (e h block 62) (e h block 61) + 0xc67178f2 + (word block 63)) = (((~~~(e h block 63)) &&& (e h block 61)) + ((e h block 62) &&& (e h block 63)) + (((e h block 63)).rotateLeft 21 ^^^ ((e h block 63)).rotateLeft 26 ^^^ ((e h block 63)).rotateLeft 7) + 0xc67178f2 + (a h block 60) + (e h block 60) + (word block 63))
  simp only [bitVecBigSigma1, bitVecChoice_eq_add_and]
  generalize (a h block 60) = v0
  generalize (e h block 60) = v1
  generalize (e h block 61) = v2
  generalize (e h block 62) = v3
  generalize (e h block 63) = v4
  generalize (word block 63) = v5
  ac_rfl

theorem w16 (block : Array Bool) :
    (word block 16) = ((((word block 1)).rotateLeft 14 ^^^ ((word block 1)).rotateLeft 25 ^^^ ((word block 1) >>> 3)) + (((word block 14)).rotateLeft 13 ^^^ ((word block 14)).rotateLeft 15 ^^^ ((word block 14) >>> 10)) + (word block 0) + (word block 9)) := by
  have hs := schedule_toBitVec_recurrence block 16 (by decide) (by decide)
  simp only [map_toBitVec_getElem!] at hs
  refine hs.trans ?_
  change (word block 0) + bitVecSmallSigma0 (word block 1) + (word block 9) + bitVecSmallSigma1 (word block 14) = ((((word block 1)).rotateLeft 14 ^^^ ((word block 1)).rotateLeft 25 ^^^ ((word block 1) >>> 3)) + (((word block 14)).rotateLeft 13 ^^^ ((word block 14)).rotateLeft 15 ^^^ ((word block 14) >>> 10)) + (word block 0) + (word block 9))
  simp only [bitVecSmallSigma0, bitVecSmallSigma1]
  generalize (word block 0) = v0
  generalize (word block 1) = v1
  generalize (word block 14) = v2
  generalize (word block 9) = v3
  ac_rfl

theorem w17 (block : Array Bool) :
    (word block 17) = ((((word block 15)).rotateLeft 13 ^^^ ((word block 15)).rotateLeft 15 ^^^ ((word block 15) >>> 10)) + (((word block 2)).rotateLeft 14 ^^^ ((word block 2)).rotateLeft 25 ^^^ ((word block 2) >>> 3)) + (word block 1) + (word block 10)) := by
  have hs := schedule_toBitVec_recurrence block 17 (by decide) (by decide)
  simp only [map_toBitVec_getElem!] at hs
  refine hs.trans ?_
  change (word block 1) + bitVecSmallSigma0 (word block 2) + (word block 10) + bitVecSmallSigma1 (word block 15) = ((((word block 15)).rotateLeft 13 ^^^ ((word block 15)).rotateLeft 15 ^^^ ((word block 15) >>> 10)) + (((word block 2)).rotateLeft 14 ^^^ ((word block 2)).rotateLeft 25 ^^^ ((word block 2) >>> 3)) + (word block 1) + (word block 10))
  simp only [bitVecSmallSigma0, bitVecSmallSigma1]
  generalize (word block 1) = v0
  generalize (word block 10) = v1
  generalize (word block 15) = v2
  generalize (word block 2) = v3
  ac_rfl

theorem w18 (block : Array Bool) :
    (word block 18) = ((((word block 16)).rotateLeft 13 ^^^ ((word block 16)).rotateLeft 15 ^^^ ((word block 16) >>> 10)) + (((word block 3)).rotateLeft 14 ^^^ ((word block 3)).rotateLeft 25 ^^^ ((word block 3) >>> 3)) + (word block 11) + (word block 2)) := by
  have hs := schedule_toBitVec_recurrence block 18 (by decide) (by decide)
  simp only [map_toBitVec_getElem!] at hs
  refine hs.trans ?_
  change (word block 2) + bitVecSmallSigma0 (word block 3) + (word block 11) + bitVecSmallSigma1 (word block 16) = ((((word block 16)).rotateLeft 13 ^^^ ((word block 16)).rotateLeft 15 ^^^ ((word block 16) >>> 10)) + (((word block 3)).rotateLeft 14 ^^^ ((word block 3)).rotateLeft 25 ^^^ ((word block 3) >>> 3)) + (word block 11) + (word block 2))
  simp only [bitVecSmallSigma0, bitVecSmallSigma1]
  generalize (word block 11) = v0
  generalize (word block 16) = v1
  generalize (word block 2) = v2
  generalize (word block 3) = v3
  ac_rfl

theorem w19 (block : Array Bool) :
    (word block 19) = ((((word block 17)).rotateLeft 13 ^^^ ((word block 17)).rotateLeft 15 ^^^ ((word block 17) >>> 10)) + (((word block 4)).rotateLeft 14 ^^^ ((word block 4)).rotateLeft 25 ^^^ ((word block 4) >>> 3)) + (word block 12) + (word block 3)) := by
  have hs := schedule_toBitVec_recurrence block 19 (by decide) (by decide)
  simp only [map_toBitVec_getElem!] at hs
  refine hs.trans ?_
  change (word block 3) + bitVecSmallSigma0 (word block 4) + (word block 12) + bitVecSmallSigma1 (word block 17) = ((((word block 17)).rotateLeft 13 ^^^ ((word block 17)).rotateLeft 15 ^^^ ((word block 17) >>> 10)) + (((word block 4)).rotateLeft 14 ^^^ ((word block 4)).rotateLeft 25 ^^^ ((word block 4) >>> 3)) + (word block 12) + (word block 3))
  simp only [bitVecSmallSigma0, bitVecSmallSigma1]
  generalize (word block 12) = v0
  generalize (word block 17) = v1
  generalize (word block 3) = v2
  generalize (word block 4) = v3
  ac_rfl

theorem w20 (block : Array Bool) :
    (word block 20) = ((((word block 18)).rotateLeft 13 ^^^ ((word block 18)).rotateLeft 15 ^^^ ((word block 18) >>> 10)) + (((word block 5)).rotateLeft 14 ^^^ ((word block 5)).rotateLeft 25 ^^^ ((word block 5) >>> 3)) + (word block 13) + (word block 4)) := by
  have hs := schedule_toBitVec_recurrence block 20 (by decide) (by decide)
  simp only [map_toBitVec_getElem!] at hs
  refine hs.trans ?_
  change (word block 4) + bitVecSmallSigma0 (word block 5) + (word block 13) + bitVecSmallSigma1 (word block 18) = ((((word block 18)).rotateLeft 13 ^^^ ((word block 18)).rotateLeft 15 ^^^ ((word block 18) >>> 10)) + (((word block 5)).rotateLeft 14 ^^^ ((word block 5)).rotateLeft 25 ^^^ ((word block 5) >>> 3)) + (word block 13) + (word block 4))
  simp only [bitVecSmallSigma0, bitVecSmallSigma1]
  generalize (word block 13) = v0
  generalize (word block 18) = v1
  generalize (word block 4) = v2
  generalize (word block 5) = v3
  ac_rfl

theorem w21 (block : Array Bool) :
    (word block 21) = ((((word block 19)).rotateLeft 13 ^^^ ((word block 19)).rotateLeft 15 ^^^ ((word block 19) >>> 10)) + (((word block 6)).rotateLeft 14 ^^^ ((word block 6)).rotateLeft 25 ^^^ ((word block 6) >>> 3)) + (word block 14) + (word block 5)) := by
  have hs := schedule_toBitVec_recurrence block 21 (by decide) (by decide)
  simp only [map_toBitVec_getElem!] at hs
  refine hs.trans ?_
  change (word block 5) + bitVecSmallSigma0 (word block 6) + (word block 14) + bitVecSmallSigma1 (word block 19) = ((((word block 19)).rotateLeft 13 ^^^ ((word block 19)).rotateLeft 15 ^^^ ((word block 19) >>> 10)) + (((word block 6)).rotateLeft 14 ^^^ ((word block 6)).rotateLeft 25 ^^^ ((word block 6) >>> 3)) + (word block 14) + (word block 5))
  simp only [bitVecSmallSigma0, bitVecSmallSigma1]
  generalize (word block 14) = v0
  generalize (word block 19) = v1
  generalize (word block 5) = v2
  generalize (word block 6) = v3
  ac_rfl

theorem w22 (block : Array Bool) :
    (word block 22) = ((((word block 20)).rotateLeft 13 ^^^ ((word block 20)).rotateLeft 15 ^^^ ((word block 20) >>> 10)) + (((word block 7)).rotateLeft 14 ^^^ ((word block 7)).rotateLeft 25 ^^^ ((word block 7) >>> 3)) + (word block 15) + (word block 6)) := by
  have hs := schedule_toBitVec_recurrence block 22 (by decide) (by decide)
  simp only [map_toBitVec_getElem!] at hs
  refine hs.trans ?_
  change (word block 6) + bitVecSmallSigma0 (word block 7) + (word block 15) + bitVecSmallSigma1 (word block 20) = ((((word block 20)).rotateLeft 13 ^^^ ((word block 20)).rotateLeft 15 ^^^ ((word block 20) >>> 10)) + (((word block 7)).rotateLeft 14 ^^^ ((word block 7)).rotateLeft 25 ^^^ ((word block 7) >>> 3)) + (word block 15) + (word block 6))
  simp only [bitVecSmallSigma0, bitVecSmallSigma1]
  generalize (word block 15) = v0
  generalize (word block 20) = v1
  generalize (word block 6) = v2
  generalize (word block 7) = v3
  ac_rfl

theorem w23 (block : Array Bool) :
    (word block 23) = ((((word block 21)).rotateLeft 13 ^^^ ((word block 21)).rotateLeft 15 ^^^ ((word block 21) >>> 10)) + (((word block 8)).rotateLeft 14 ^^^ ((word block 8)).rotateLeft 25 ^^^ ((word block 8) >>> 3)) + (word block 16) + (word block 7)) := by
  have hs := schedule_toBitVec_recurrence block 23 (by decide) (by decide)
  simp only [map_toBitVec_getElem!] at hs
  refine hs.trans ?_
  change (word block 7) + bitVecSmallSigma0 (word block 8) + (word block 16) + bitVecSmallSigma1 (word block 21) = ((((word block 21)).rotateLeft 13 ^^^ ((word block 21)).rotateLeft 15 ^^^ ((word block 21) >>> 10)) + (((word block 8)).rotateLeft 14 ^^^ ((word block 8)).rotateLeft 25 ^^^ ((word block 8) >>> 3)) + (word block 16) + (word block 7))
  simp only [bitVecSmallSigma0, bitVecSmallSigma1]
  generalize (word block 16) = v0
  generalize (word block 21) = v1
  generalize (word block 7) = v2
  generalize (word block 8) = v3
  ac_rfl

theorem w24 (block : Array Bool) :
    (word block 24) = ((((word block 22)).rotateLeft 13 ^^^ ((word block 22)).rotateLeft 15 ^^^ ((word block 22) >>> 10)) + (((word block 9)).rotateLeft 14 ^^^ ((word block 9)).rotateLeft 25 ^^^ ((word block 9) >>> 3)) + (word block 17) + (word block 8)) := by
  have hs := schedule_toBitVec_recurrence block 24 (by decide) (by decide)
  simp only [map_toBitVec_getElem!] at hs
  refine hs.trans ?_
  change (word block 8) + bitVecSmallSigma0 (word block 9) + (word block 17) + bitVecSmallSigma1 (word block 22) = ((((word block 22)).rotateLeft 13 ^^^ ((word block 22)).rotateLeft 15 ^^^ ((word block 22) >>> 10)) + (((word block 9)).rotateLeft 14 ^^^ ((word block 9)).rotateLeft 25 ^^^ ((word block 9) >>> 3)) + (word block 17) + (word block 8))
  simp only [bitVecSmallSigma0, bitVecSmallSigma1]
  generalize (word block 17) = v0
  generalize (word block 22) = v1
  generalize (word block 8) = v2
  generalize (word block 9) = v3
  ac_rfl

theorem w25 (block : Array Bool) :
    (word block 25) = ((((word block 10)).rotateLeft 14 ^^^ ((word block 10)).rotateLeft 25 ^^^ ((word block 10) >>> 3)) + (((word block 23)).rotateLeft 13 ^^^ ((word block 23)).rotateLeft 15 ^^^ ((word block 23) >>> 10)) + (word block 18) + (word block 9)) := by
  have hs := schedule_toBitVec_recurrence block 25 (by decide) (by decide)
  simp only [map_toBitVec_getElem!] at hs
  refine hs.trans ?_
  change (word block 9) + bitVecSmallSigma0 (word block 10) + (word block 18) + bitVecSmallSigma1 (word block 23) = ((((word block 10)).rotateLeft 14 ^^^ ((word block 10)).rotateLeft 25 ^^^ ((word block 10) >>> 3)) + (((word block 23)).rotateLeft 13 ^^^ ((word block 23)).rotateLeft 15 ^^^ ((word block 23) >>> 10)) + (word block 18) + (word block 9))
  simp only [bitVecSmallSigma0, bitVecSmallSigma1]
  generalize (word block 10) = v0
  generalize (word block 18) = v1
  generalize (word block 23) = v2
  generalize (word block 9) = v3
  ac_rfl

theorem w26 (block : Array Bool) :
    (word block 26) = ((((word block 11)).rotateLeft 14 ^^^ ((word block 11)).rotateLeft 25 ^^^ ((word block 11) >>> 3)) + (((word block 24)).rotateLeft 13 ^^^ ((word block 24)).rotateLeft 15 ^^^ ((word block 24) >>> 10)) + (word block 10) + (word block 19)) := by
  have hs := schedule_toBitVec_recurrence block 26 (by decide) (by decide)
  simp only [map_toBitVec_getElem!] at hs
  refine hs.trans ?_
  change (word block 10) + bitVecSmallSigma0 (word block 11) + (word block 19) + bitVecSmallSigma1 (word block 24) = ((((word block 11)).rotateLeft 14 ^^^ ((word block 11)).rotateLeft 25 ^^^ ((word block 11) >>> 3)) + (((word block 24)).rotateLeft 13 ^^^ ((word block 24)).rotateLeft 15 ^^^ ((word block 24) >>> 10)) + (word block 10) + (word block 19))
  simp only [bitVecSmallSigma0, bitVecSmallSigma1]
  generalize (word block 10) = v0
  generalize (word block 11) = v1
  generalize (word block 19) = v2
  generalize (word block 24) = v3
  ac_rfl

theorem w27 (block : Array Bool) :
    (word block 27) = ((((word block 12)).rotateLeft 14 ^^^ ((word block 12)).rotateLeft 25 ^^^ ((word block 12) >>> 3)) + (((word block 25)).rotateLeft 13 ^^^ ((word block 25)).rotateLeft 15 ^^^ ((word block 25) >>> 10)) + (word block 11) + (word block 20)) := by
  have hs := schedule_toBitVec_recurrence block 27 (by decide) (by decide)
  simp only [map_toBitVec_getElem!] at hs
  refine hs.trans ?_
  change (word block 11) + bitVecSmallSigma0 (word block 12) + (word block 20) + bitVecSmallSigma1 (word block 25) = ((((word block 12)).rotateLeft 14 ^^^ ((word block 12)).rotateLeft 25 ^^^ ((word block 12) >>> 3)) + (((word block 25)).rotateLeft 13 ^^^ ((word block 25)).rotateLeft 15 ^^^ ((word block 25) >>> 10)) + (word block 11) + (word block 20))
  simp only [bitVecSmallSigma0, bitVecSmallSigma1]
  generalize (word block 11) = v0
  generalize (word block 12) = v1
  generalize (word block 20) = v2
  generalize (word block 25) = v3
  ac_rfl

theorem w28 (block : Array Bool) :
    (word block 28) = ((((word block 13)).rotateLeft 14 ^^^ ((word block 13)).rotateLeft 25 ^^^ ((word block 13) >>> 3)) + (((word block 26)).rotateLeft 13 ^^^ ((word block 26)).rotateLeft 15 ^^^ ((word block 26) >>> 10)) + (word block 12) + (word block 21)) := by
  have hs := schedule_toBitVec_recurrence block 28 (by decide) (by decide)
  simp only [map_toBitVec_getElem!] at hs
  refine hs.trans ?_
  change (word block 12) + bitVecSmallSigma0 (word block 13) + (word block 21) + bitVecSmallSigma1 (word block 26) = ((((word block 13)).rotateLeft 14 ^^^ ((word block 13)).rotateLeft 25 ^^^ ((word block 13) >>> 3)) + (((word block 26)).rotateLeft 13 ^^^ ((word block 26)).rotateLeft 15 ^^^ ((word block 26) >>> 10)) + (word block 12) + (word block 21))
  simp only [bitVecSmallSigma0, bitVecSmallSigma1]
  generalize (word block 12) = v0
  generalize (word block 13) = v1
  generalize (word block 21) = v2
  generalize (word block 26) = v3
  ac_rfl

theorem w29 (block : Array Bool) :
    (word block 29) = ((((word block 14)).rotateLeft 14 ^^^ ((word block 14)).rotateLeft 25 ^^^ ((word block 14) >>> 3)) + (((word block 27)).rotateLeft 13 ^^^ ((word block 27)).rotateLeft 15 ^^^ ((word block 27) >>> 10)) + (word block 13) + (word block 22)) := by
  have hs := schedule_toBitVec_recurrence block 29 (by decide) (by decide)
  simp only [map_toBitVec_getElem!] at hs
  refine hs.trans ?_
  change (word block 13) + bitVecSmallSigma0 (word block 14) + (word block 22) + bitVecSmallSigma1 (word block 27) = ((((word block 14)).rotateLeft 14 ^^^ ((word block 14)).rotateLeft 25 ^^^ ((word block 14) >>> 3)) + (((word block 27)).rotateLeft 13 ^^^ ((word block 27)).rotateLeft 15 ^^^ ((word block 27) >>> 10)) + (word block 13) + (word block 22))
  simp only [bitVecSmallSigma0, bitVecSmallSigma1]
  generalize (word block 13) = v0
  generalize (word block 14) = v1
  generalize (word block 22) = v2
  generalize (word block 27) = v3
  ac_rfl

theorem w30 (block : Array Bool) :
    (word block 30) = ((((word block 15)).rotateLeft 14 ^^^ ((word block 15)).rotateLeft 25 ^^^ ((word block 15) >>> 3)) + (((word block 28)).rotateLeft 13 ^^^ ((word block 28)).rotateLeft 15 ^^^ ((word block 28) >>> 10)) + (word block 14) + (word block 23)) := by
  have hs := schedule_toBitVec_recurrence block 30 (by decide) (by decide)
  simp only [map_toBitVec_getElem!] at hs
  refine hs.trans ?_
  change (word block 14) + bitVecSmallSigma0 (word block 15) + (word block 23) + bitVecSmallSigma1 (word block 28) = ((((word block 15)).rotateLeft 14 ^^^ ((word block 15)).rotateLeft 25 ^^^ ((word block 15) >>> 3)) + (((word block 28)).rotateLeft 13 ^^^ ((word block 28)).rotateLeft 15 ^^^ ((word block 28) >>> 10)) + (word block 14) + (word block 23))
  simp only [bitVecSmallSigma0, bitVecSmallSigma1]
  generalize (word block 14) = v0
  generalize (word block 15) = v1
  generalize (word block 23) = v2
  generalize (word block 28) = v3
  ac_rfl

theorem w31 (block : Array Bool) :
    (word block 31) = ((((word block 16)).rotateLeft 14 ^^^ ((word block 16)).rotateLeft 25 ^^^ ((word block 16) >>> 3)) + (((word block 29)).rotateLeft 13 ^^^ ((word block 29)).rotateLeft 15 ^^^ ((word block 29) >>> 10)) + (word block 15) + (word block 24)) := by
  have hs := schedule_toBitVec_recurrence block 31 (by decide) (by decide)
  simp only [map_toBitVec_getElem!] at hs
  refine hs.trans ?_
  change (word block 15) + bitVecSmallSigma0 (word block 16) + (word block 24) + bitVecSmallSigma1 (word block 29) = ((((word block 16)).rotateLeft 14 ^^^ ((word block 16)).rotateLeft 25 ^^^ ((word block 16) >>> 3)) + (((word block 29)).rotateLeft 13 ^^^ ((word block 29)).rotateLeft 15 ^^^ ((word block 29) >>> 10)) + (word block 15) + (word block 24))
  simp only [bitVecSmallSigma0, bitVecSmallSigma1]
  generalize (word block 15) = v0
  generalize (word block 16) = v1
  generalize (word block 24) = v2
  generalize (word block 29) = v3
  ac_rfl

theorem w32 (block : Array Bool) :
    (word block 32) = ((((word block 17)).rotateLeft 14 ^^^ ((word block 17)).rotateLeft 25 ^^^ ((word block 17) >>> 3)) + (((word block 30)).rotateLeft 13 ^^^ ((word block 30)).rotateLeft 15 ^^^ ((word block 30) >>> 10)) + (word block 16) + (word block 25)) := by
  have hs := schedule_toBitVec_recurrence block 32 (by decide) (by decide)
  simp only [map_toBitVec_getElem!] at hs
  refine hs.trans ?_
  change (word block 16) + bitVecSmallSigma0 (word block 17) + (word block 25) + bitVecSmallSigma1 (word block 30) = ((((word block 17)).rotateLeft 14 ^^^ ((word block 17)).rotateLeft 25 ^^^ ((word block 17) >>> 3)) + (((word block 30)).rotateLeft 13 ^^^ ((word block 30)).rotateLeft 15 ^^^ ((word block 30) >>> 10)) + (word block 16) + (word block 25))
  simp only [bitVecSmallSigma0, bitVecSmallSigma1]
  generalize (word block 16) = v0
  generalize (word block 17) = v1
  generalize (word block 25) = v2
  generalize (word block 30) = v3
  ac_rfl

theorem w33 (block : Array Bool) :
    (word block 33) = ((((word block 18)).rotateLeft 14 ^^^ ((word block 18)).rotateLeft 25 ^^^ ((word block 18) >>> 3)) + (((word block 31)).rotateLeft 13 ^^^ ((word block 31)).rotateLeft 15 ^^^ ((word block 31) >>> 10)) + (word block 17) + (word block 26)) := by
  have hs := schedule_toBitVec_recurrence block 33 (by decide) (by decide)
  simp only [map_toBitVec_getElem!] at hs
  refine hs.trans ?_
  change (word block 17) + bitVecSmallSigma0 (word block 18) + (word block 26) + bitVecSmallSigma1 (word block 31) = ((((word block 18)).rotateLeft 14 ^^^ ((word block 18)).rotateLeft 25 ^^^ ((word block 18) >>> 3)) + (((word block 31)).rotateLeft 13 ^^^ ((word block 31)).rotateLeft 15 ^^^ ((word block 31) >>> 10)) + (word block 17) + (word block 26))
  simp only [bitVecSmallSigma0, bitVecSmallSigma1]
  generalize (word block 17) = v0
  generalize (word block 18) = v1
  generalize (word block 26) = v2
  generalize (word block 31) = v3
  ac_rfl

theorem w34 (block : Array Bool) :
    (word block 34) = ((((word block 19)).rotateLeft 14 ^^^ ((word block 19)).rotateLeft 25 ^^^ ((word block 19) >>> 3)) + (((word block 32)).rotateLeft 13 ^^^ ((word block 32)).rotateLeft 15 ^^^ ((word block 32) >>> 10)) + (word block 18) + (word block 27)) := by
  have hs := schedule_toBitVec_recurrence block 34 (by decide) (by decide)
  simp only [map_toBitVec_getElem!] at hs
  refine hs.trans ?_
  change (word block 18) + bitVecSmallSigma0 (word block 19) + (word block 27) + bitVecSmallSigma1 (word block 32) = ((((word block 19)).rotateLeft 14 ^^^ ((word block 19)).rotateLeft 25 ^^^ ((word block 19) >>> 3)) + (((word block 32)).rotateLeft 13 ^^^ ((word block 32)).rotateLeft 15 ^^^ ((word block 32) >>> 10)) + (word block 18) + (word block 27))
  simp only [bitVecSmallSigma0, bitVecSmallSigma1]
  generalize (word block 18) = v0
  generalize (word block 19) = v1
  generalize (word block 27) = v2
  generalize (word block 32) = v3
  ac_rfl

theorem w35 (block : Array Bool) :
    (word block 35) = ((((word block 20)).rotateLeft 14 ^^^ ((word block 20)).rotateLeft 25 ^^^ ((word block 20) >>> 3)) + (((word block 33)).rotateLeft 13 ^^^ ((word block 33)).rotateLeft 15 ^^^ ((word block 33) >>> 10)) + (word block 19) + (word block 28)) := by
  have hs := schedule_toBitVec_recurrence block 35 (by decide) (by decide)
  simp only [map_toBitVec_getElem!] at hs
  refine hs.trans ?_
  change (word block 19) + bitVecSmallSigma0 (word block 20) + (word block 28) + bitVecSmallSigma1 (word block 33) = ((((word block 20)).rotateLeft 14 ^^^ ((word block 20)).rotateLeft 25 ^^^ ((word block 20) >>> 3)) + (((word block 33)).rotateLeft 13 ^^^ ((word block 33)).rotateLeft 15 ^^^ ((word block 33) >>> 10)) + (word block 19) + (word block 28))
  simp only [bitVecSmallSigma0, bitVecSmallSigma1]
  generalize (word block 19) = v0
  generalize (word block 20) = v1
  generalize (word block 28) = v2
  generalize (word block 33) = v3
  ac_rfl

theorem w36 (block : Array Bool) :
    (word block 36) = ((((word block 21)).rotateLeft 14 ^^^ ((word block 21)).rotateLeft 25 ^^^ ((word block 21) >>> 3)) + (((word block 34)).rotateLeft 13 ^^^ ((word block 34)).rotateLeft 15 ^^^ ((word block 34) >>> 10)) + (word block 20) + (word block 29)) := by
  have hs := schedule_toBitVec_recurrence block 36 (by decide) (by decide)
  simp only [map_toBitVec_getElem!] at hs
  refine hs.trans ?_
  change (word block 20) + bitVecSmallSigma0 (word block 21) + (word block 29) + bitVecSmallSigma1 (word block 34) = ((((word block 21)).rotateLeft 14 ^^^ ((word block 21)).rotateLeft 25 ^^^ ((word block 21) >>> 3)) + (((word block 34)).rotateLeft 13 ^^^ ((word block 34)).rotateLeft 15 ^^^ ((word block 34) >>> 10)) + (word block 20) + (word block 29))
  simp only [bitVecSmallSigma0, bitVecSmallSigma1]
  generalize (word block 20) = v0
  generalize (word block 21) = v1
  generalize (word block 29) = v2
  generalize (word block 34) = v3
  ac_rfl

theorem w37 (block : Array Bool) :
    (word block 37) = ((((word block 22)).rotateLeft 14 ^^^ ((word block 22)).rotateLeft 25 ^^^ ((word block 22) >>> 3)) + (((word block 35)).rotateLeft 13 ^^^ ((word block 35)).rotateLeft 15 ^^^ ((word block 35) >>> 10)) + (word block 21) + (word block 30)) := by
  have hs := schedule_toBitVec_recurrence block 37 (by decide) (by decide)
  simp only [map_toBitVec_getElem!] at hs
  refine hs.trans ?_
  change (word block 21) + bitVecSmallSigma0 (word block 22) + (word block 30) + bitVecSmallSigma1 (word block 35) = ((((word block 22)).rotateLeft 14 ^^^ ((word block 22)).rotateLeft 25 ^^^ ((word block 22) >>> 3)) + (((word block 35)).rotateLeft 13 ^^^ ((word block 35)).rotateLeft 15 ^^^ ((word block 35) >>> 10)) + (word block 21) + (word block 30))
  simp only [bitVecSmallSigma0, bitVecSmallSigma1]
  generalize (word block 21) = v0
  generalize (word block 22) = v1
  generalize (word block 30) = v2
  generalize (word block 35) = v3
  ac_rfl

theorem w38 (block : Array Bool) :
    (word block 38) = ((((word block 23)).rotateLeft 14 ^^^ ((word block 23)).rotateLeft 25 ^^^ ((word block 23) >>> 3)) + (((word block 36)).rotateLeft 13 ^^^ ((word block 36)).rotateLeft 15 ^^^ ((word block 36) >>> 10)) + (word block 22) + (word block 31)) := by
  have hs := schedule_toBitVec_recurrence block 38 (by decide) (by decide)
  simp only [map_toBitVec_getElem!] at hs
  refine hs.trans ?_
  change (word block 22) + bitVecSmallSigma0 (word block 23) + (word block 31) + bitVecSmallSigma1 (word block 36) = ((((word block 23)).rotateLeft 14 ^^^ ((word block 23)).rotateLeft 25 ^^^ ((word block 23) >>> 3)) + (((word block 36)).rotateLeft 13 ^^^ ((word block 36)).rotateLeft 15 ^^^ ((word block 36) >>> 10)) + (word block 22) + (word block 31))
  simp only [bitVecSmallSigma0, bitVecSmallSigma1]
  generalize (word block 22) = v0
  generalize (word block 23) = v1
  generalize (word block 31) = v2
  generalize (word block 36) = v3
  ac_rfl

theorem w39 (block : Array Bool) :
    (word block 39) = ((((word block 24)).rotateLeft 14 ^^^ ((word block 24)).rotateLeft 25 ^^^ ((word block 24) >>> 3)) + (((word block 37)).rotateLeft 13 ^^^ ((word block 37)).rotateLeft 15 ^^^ ((word block 37) >>> 10)) + (word block 23) + (word block 32)) := by
  have hs := schedule_toBitVec_recurrence block 39 (by decide) (by decide)
  simp only [map_toBitVec_getElem!] at hs
  refine hs.trans ?_
  change (word block 23) + bitVecSmallSigma0 (word block 24) + (word block 32) + bitVecSmallSigma1 (word block 37) = ((((word block 24)).rotateLeft 14 ^^^ ((word block 24)).rotateLeft 25 ^^^ ((word block 24) >>> 3)) + (((word block 37)).rotateLeft 13 ^^^ ((word block 37)).rotateLeft 15 ^^^ ((word block 37) >>> 10)) + (word block 23) + (word block 32))
  simp only [bitVecSmallSigma0, bitVecSmallSigma1]
  generalize (word block 23) = v0
  generalize (word block 24) = v1
  generalize (word block 32) = v2
  generalize (word block 37) = v3
  ac_rfl

theorem w40 (block : Array Bool) :
    (word block 40) = ((((word block 25)).rotateLeft 14 ^^^ ((word block 25)).rotateLeft 25 ^^^ ((word block 25) >>> 3)) + (((word block 38)).rotateLeft 13 ^^^ ((word block 38)).rotateLeft 15 ^^^ ((word block 38) >>> 10)) + (word block 24) + (word block 33)) := by
  have hs := schedule_toBitVec_recurrence block 40 (by decide) (by decide)
  simp only [map_toBitVec_getElem!] at hs
  refine hs.trans ?_
  change (word block 24) + bitVecSmallSigma0 (word block 25) + (word block 33) + bitVecSmallSigma1 (word block 38) = ((((word block 25)).rotateLeft 14 ^^^ ((word block 25)).rotateLeft 25 ^^^ ((word block 25) >>> 3)) + (((word block 38)).rotateLeft 13 ^^^ ((word block 38)).rotateLeft 15 ^^^ ((word block 38) >>> 10)) + (word block 24) + (word block 33))
  simp only [bitVecSmallSigma0, bitVecSmallSigma1]
  generalize (word block 24) = v0
  generalize (word block 25) = v1
  generalize (word block 33) = v2
  generalize (word block 38) = v3
  ac_rfl

theorem w41 (block : Array Bool) :
    (word block 41) = ((((word block 26)).rotateLeft 14 ^^^ ((word block 26)).rotateLeft 25 ^^^ ((word block 26) >>> 3)) + (((word block 39)).rotateLeft 13 ^^^ ((word block 39)).rotateLeft 15 ^^^ ((word block 39) >>> 10)) + (word block 25) + (word block 34)) := by
  have hs := schedule_toBitVec_recurrence block 41 (by decide) (by decide)
  simp only [map_toBitVec_getElem!] at hs
  refine hs.trans ?_
  change (word block 25) + bitVecSmallSigma0 (word block 26) + (word block 34) + bitVecSmallSigma1 (word block 39) = ((((word block 26)).rotateLeft 14 ^^^ ((word block 26)).rotateLeft 25 ^^^ ((word block 26) >>> 3)) + (((word block 39)).rotateLeft 13 ^^^ ((word block 39)).rotateLeft 15 ^^^ ((word block 39) >>> 10)) + (word block 25) + (word block 34))
  simp only [bitVecSmallSigma0, bitVecSmallSigma1]
  generalize (word block 25) = v0
  generalize (word block 26) = v1
  generalize (word block 34) = v2
  generalize (word block 39) = v3
  ac_rfl

theorem w42 (block : Array Bool) :
    (word block 42) = ((((word block 27)).rotateLeft 14 ^^^ ((word block 27)).rotateLeft 25 ^^^ ((word block 27) >>> 3)) + (((word block 40)).rotateLeft 13 ^^^ ((word block 40)).rotateLeft 15 ^^^ ((word block 40) >>> 10)) + (word block 26) + (word block 35)) := by
  have hs := schedule_toBitVec_recurrence block 42 (by decide) (by decide)
  simp only [map_toBitVec_getElem!] at hs
  refine hs.trans ?_
  change (word block 26) + bitVecSmallSigma0 (word block 27) + (word block 35) + bitVecSmallSigma1 (word block 40) = ((((word block 27)).rotateLeft 14 ^^^ ((word block 27)).rotateLeft 25 ^^^ ((word block 27) >>> 3)) + (((word block 40)).rotateLeft 13 ^^^ ((word block 40)).rotateLeft 15 ^^^ ((word block 40) >>> 10)) + (word block 26) + (word block 35))
  simp only [bitVecSmallSigma0, bitVecSmallSigma1]
  generalize (word block 26) = v0
  generalize (word block 27) = v1
  generalize (word block 35) = v2
  generalize (word block 40) = v3
  ac_rfl

theorem w43 (block : Array Bool) :
    (word block 43) = ((((word block 28)).rotateLeft 14 ^^^ ((word block 28)).rotateLeft 25 ^^^ ((word block 28) >>> 3)) + (((word block 41)).rotateLeft 13 ^^^ ((word block 41)).rotateLeft 15 ^^^ ((word block 41) >>> 10)) + (word block 27) + (word block 36)) := by
  have hs := schedule_toBitVec_recurrence block 43 (by decide) (by decide)
  simp only [map_toBitVec_getElem!] at hs
  refine hs.trans ?_
  change (word block 27) + bitVecSmallSigma0 (word block 28) + (word block 36) + bitVecSmallSigma1 (word block 41) = ((((word block 28)).rotateLeft 14 ^^^ ((word block 28)).rotateLeft 25 ^^^ ((word block 28) >>> 3)) + (((word block 41)).rotateLeft 13 ^^^ ((word block 41)).rotateLeft 15 ^^^ ((word block 41) >>> 10)) + (word block 27) + (word block 36))
  simp only [bitVecSmallSigma0, bitVecSmallSigma1]
  generalize (word block 27) = v0
  generalize (word block 28) = v1
  generalize (word block 36) = v2
  generalize (word block 41) = v3
  ac_rfl

theorem w44 (block : Array Bool) :
    (word block 44) = ((((word block 29)).rotateLeft 14 ^^^ ((word block 29)).rotateLeft 25 ^^^ ((word block 29) >>> 3)) + (((word block 42)).rotateLeft 13 ^^^ ((word block 42)).rotateLeft 15 ^^^ ((word block 42) >>> 10)) + (word block 28) + (word block 37)) := by
  have hs := schedule_toBitVec_recurrence block 44 (by decide) (by decide)
  simp only [map_toBitVec_getElem!] at hs
  refine hs.trans ?_
  change (word block 28) + bitVecSmallSigma0 (word block 29) + (word block 37) + bitVecSmallSigma1 (word block 42) = ((((word block 29)).rotateLeft 14 ^^^ ((word block 29)).rotateLeft 25 ^^^ ((word block 29) >>> 3)) + (((word block 42)).rotateLeft 13 ^^^ ((word block 42)).rotateLeft 15 ^^^ ((word block 42) >>> 10)) + (word block 28) + (word block 37))
  simp only [bitVecSmallSigma0, bitVecSmallSigma1]
  generalize (word block 28) = v0
  generalize (word block 29) = v1
  generalize (word block 37) = v2
  generalize (word block 42) = v3
  ac_rfl

theorem w45 (block : Array Bool) :
    (word block 45) = ((((word block 30)).rotateLeft 14 ^^^ ((word block 30)).rotateLeft 25 ^^^ ((word block 30) >>> 3)) + (((word block 43)).rotateLeft 13 ^^^ ((word block 43)).rotateLeft 15 ^^^ ((word block 43) >>> 10)) + (word block 29) + (word block 38)) := by
  have hs := schedule_toBitVec_recurrence block 45 (by decide) (by decide)
  simp only [map_toBitVec_getElem!] at hs
  refine hs.trans ?_
  change (word block 29) + bitVecSmallSigma0 (word block 30) + (word block 38) + bitVecSmallSigma1 (word block 43) = ((((word block 30)).rotateLeft 14 ^^^ ((word block 30)).rotateLeft 25 ^^^ ((word block 30) >>> 3)) + (((word block 43)).rotateLeft 13 ^^^ ((word block 43)).rotateLeft 15 ^^^ ((word block 43) >>> 10)) + (word block 29) + (word block 38))
  simp only [bitVecSmallSigma0, bitVecSmallSigma1]
  generalize (word block 29) = v0
  generalize (word block 30) = v1
  generalize (word block 38) = v2
  generalize (word block 43) = v3
  ac_rfl

theorem w46 (block : Array Bool) :
    (word block 46) = ((((word block 31)).rotateLeft 14 ^^^ ((word block 31)).rotateLeft 25 ^^^ ((word block 31) >>> 3)) + (((word block 44)).rotateLeft 13 ^^^ ((word block 44)).rotateLeft 15 ^^^ ((word block 44) >>> 10)) + (word block 30) + (word block 39)) := by
  have hs := schedule_toBitVec_recurrence block 46 (by decide) (by decide)
  simp only [map_toBitVec_getElem!] at hs
  refine hs.trans ?_
  change (word block 30) + bitVecSmallSigma0 (word block 31) + (word block 39) + bitVecSmallSigma1 (word block 44) = ((((word block 31)).rotateLeft 14 ^^^ ((word block 31)).rotateLeft 25 ^^^ ((word block 31) >>> 3)) + (((word block 44)).rotateLeft 13 ^^^ ((word block 44)).rotateLeft 15 ^^^ ((word block 44) >>> 10)) + (word block 30) + (word block 39))
  simp only [bitVecSmallSigma0, bitVecSmallSigma1]
  generalize (word block 30) = v0
  generalize (word block 31) = v1
  generalize (word block 39) = v2
  generalize (word block 44) = v3
  ac_rfl

theorem w47 (block : Array Bool) :
    (word block 47) = ((((word block 32)).rotateLeft 14 ^^^ ((word block 32)).rotateLeft 25 ^^^ ((word block 32) >>> 3)) + (((word block 45)).rotateLeft 13 ^^^ ((word block 45)).rotateLeft 15 ^^^ ((word block 45) >>> 10)) + (word block 31) + (word block 40)) := by
  have hs := schedule_toBitVec_recurrence block 47 (by decide) (by decide)
  simp only [map_toBitVec_getElem!] at hs
  refine hs.trans ?_
  change (word block 31) + bitVecSmallSigma0 (word block 32) + (word block 40) + bitVecSmallSigma1 (word block 45) = ((((word block 32)).rotateLeft 14 ^^^ ((word block 32)).rotateLeft 25 ^^^ ((word block 32) >>> 3)) + (((word block 45)).rotateLeft 13 ^^^ ((word block 45)).rotateLeft 15 ^^^ ((word block 45) >>> 10)) + (word block 31) + (word block 40))
  simp only [bitVecSmallSigma0, bitVecSmallSigma1]
  generalize (word block 31) = v0
  generalize (word block 32) = v1
  generalize (word block 40) = v2
  generalize (word block 45) = v3
  ac_rfl

theorem w48 (block : Array Bool) :
    (word block 48) = ((((word block 33)).rotateLeft 14 ^^^ ((word block 33)).rotateLeft 25 ^^^ ((word block 33) >>> 3)) + (((word block 46)).rotateLeft 13 ^^^ ((word block 46)).rotateLeft 15 ^^^ ((word block 46) >>> 10)) + (word block 32) + (word block 41)) := by
  have hs := schedule_toBitVec_recurrence block 48 (by decide) (by decide)
  simp only [map_toBitVec_getElem!] at hs
  refine hs.trans ?_
  change (word block 32) + bitVecSmallSigma0 (word block 33) + (word block 41) + bitVecSmallSigma1 (word block 46) = ((((word block 33)).rotateLeft 14 ^^^ ((word block 33)).rotateLeft 25 ^^^ ((word block 33) >>> 3)) + (((word block 46)).rotateLeft 13 ^^^ ((word block 46)).rotateLeft 15 ^^^ ((word block 46) >>> 10)) + (word block 32) + (word block 41))
  simp only [bitVecSmallSigma0, bitVecSmallSigma1]
  generalize (word block 32) = v0
  generalize (word block 33) = v1
  generalize (word block 41) = v2
  generalize (word block 46) = v3
  ac_rfl

theorem w49 (block : Array Bool) :
    (word block 49) = ((((word block 34)).rotateLeft 14 ^^^ ((word block 34)).rotateLeft 25 ^^^ ((word block 34) >>> 3)) + (((word block 47)).rotateLeft 13 ^^^ ((word block 47)).rotateLeft 15 ^^^ ((word block 47) >>> 10)) + (word block 33) + (word block 42)) := by
  have hs := schedule_toBitVec_recurrence block 49 (by decide) (by decide)
  simp only [map_toBitVec_getElem!] at hs
  refine hs.trans ?_
  change (word block 33) + bitVecSmallSigma0 (word block 34) + (word block 42) + bitVecSmallSigma1 (word block 47) = ((((word block 34)).rotateLeft 14 ^^^ ((word block 34)).rotateLeft 25 ^^^ ((word block 34) >>> 3)) + (((word block 47)).rotateLeft 13 ^^^ ((word block 47)).rotateLeft 15 ^^^ ((word block 47) >>> 10)) + (word block 33) + (word block 42))
  simp only [bitVecSmallSigma0, bitVecSmallSigma1]
  generalize (word block 33) = v0
  generalize (word block 34) = v1
  generalize (word block 42) = v2
  generalize (word block 47) = v3
  ac_rfl

theorem w50 (block : Array Bool) :
    (word block 50) = ((((word block 35)).rotateLeft 14 ^^^ ((word block 35)).rotateLeft 25 ^^^ ((word block 35) >>> 3)) + (((word block 48)).rotateLeft 13 ^^^ ((word block 48)).rotateLeft 15 ^^^ ((word block 48) >>> 10)) + (word block 34) + (word block 43)) := by
  have hs := schedule_toBitVec_recurrence block 50 (by decide) (by decide)
  simp only [map_toBitVec_getElem!] at hs
  refine hs.trans ?_
  change (word block 34) + bitVecSmallSigma0 (word block 35) + (word block 43) + bitVecSmallSigma1 (word block 48) = ((((word block 35)).rotateLeft 14 ^^^ ((word block 35)).rotateLeft 25 ^^^ ((word block 35) >>> 3)) + (((word block 48)).rotateLeft 13 ^^^ ((word block 48)).rotateLeft 15 ^^^ ((word block 48) >>> 10)) + (word block 34) + (word block 43))
  simp only [bitVecSmallSigma0, bitVecSmallSigma1]
  generalize (word block 34) = v0
  generalize (word block 35) = v1
  generalize (word block 43) = v2
  generalize (word block 48) = v3
  ac_rfl

theorem w51 (block : Array Bool) :
    (word block 51) = ((((word block 36)).rotateLeft 14 ^^^ ((word block 36)).rotateLeft 25 ^^^ ((word block 36) >>> 3)) + (((word block 49)).rotateLeft 13 ^^^ ((word block 49)).rotateLeft 15 ^^^ ((word block 49) >>> 10)) + (word block 35) + (word block 44)) := by
  have hs := schedule_toBitVec_recurrence block 51 (by decide) (by decide)
  simp only [map_toBitVec_getElem!] at hs
  refine hs.trans ?_
  change (word block 35) + bitVecSmallSigma0 (word block 36) + (word block 44) + bitVecSmallSigma1 (word block 49) = ((((word block 36)).rotateLeft 14 ^^^ ((word block 36)).rotateLeft 25 ^^^ ((word block 36) >>> 3)) + (((word block 49)).rotateLeft 13 ^^^ ((word block 49)).rotateLeft 15 ^^^ ((word block 49) >>> 10)) + (word block 35) + (word block 44))
  simp only [bitVecSmallSigma0, bitVecSmallSigma1]
  generalize (word block 35) = v0
  generalize (word block 36) = v1
  generalize (word block 44) = v2
  generalize (word block 49) = v3
  ac_rfl

theorem w52 (block : Array Bool) :
    (word block 52) = ((((word block 37)).rotateLeft 14 ^^^ ((word block 37)).rotateLeft 25 ^^^ ((word block 37) >>> 3)) + (((word block 50)).rotateLeft 13 ^^^ ((word block 50)).rotateLeft 15 ^^^ ((word block 50) >>> 10)) + (word block 36) + (word block 45)) := by
  have hs := schedule_toBitVec_recurrence block 52 (by decide) (by decide)
  simp only [map_toBitVec_getElem!] at hs
  refine hs.trans ?_
  change (word block 36) + bitVecSmallSigma0 (word block 37) + (word block 45) + bitVecSmallSigma1 (word block 50) = ((((word block 37)).rotateLeft 14 ^^^ ((word block 37)).rotateLeft 25 ^^^ ((word block 37) >>> 3)) + (((word block 50)).rotateLeft 13 ^^^ ((word block 50)).rotateLeft 15 ^^^ ((word block 50) >>> 10)) + (word block 36) + (word block 45))
  simp only [bitVecSmallSigma0, bitVecSmallSigma1]
  generalize (word block 36) = v0
  generalize (word block 37) = v1
  generalize (word block 45) = v2
  generalize (word block 50) = v3
  ac_rfl

theorem w53 (block : Array Bool) :
    (word block 53) = ((((word block 38)).rotateLeft 14 ^^^ ((word block 38)).rotateLeft 25 ^^^ ((word block 38) >>> 3)) + (((word block 51)).rotateLeft 13 ^^^ ((word block 51)).rotateLeft 15 ^^^ ((word block 51) >>> 10)) + (word block 37) + (word block 46)) := by
  have hs := schedule_toBitVec_recurrence block 53 (by decide) (by decide)
  simp only [map_toBitVec_getElem!] at hs
  refine hs.trans ?_
  change (word block 37) + bitVecSmallSigma0 (word block 38) + (word block 46) + bitVecSmallSigma1 (word block 51) = ((((word block 38)).rotateLeft 14 ^^^ ((word block 38)).rotateLeft 25 ^^^ ((word block 38) >>> 3)) + (((word block 51)).rotateLeft 13 ^^^ ((word block 51)).rotateLeft 15 ^^^ ((word block 51) >>> 10)) + (word block 37) + (word block 46))
  simp only [bitVecSmallSigma0, bitVecSmallSigma1]
  generalize (word block 37) = v0
  generalize (word block 38) = v1
  generalize (word block 46) = v2
  generalize (word block 51) = v3
  ac_rfl

theorem w54 (block : Array Bool) :
    (word block 54) = ((((word block 39)).rotateLeft 14 ^^^ ((word block 39)).rotateLeft 25 ^^^ ((word block 39) >>> 3)) + (((word block 52)).rotateLeft 13 ^^^ ((word block 52)).rotateLeft 15 ^^^ ((word block 52) >>> 10)) + (word block 38) + (word block 47)) := by
  have hs := schedule_toBitVec_recurrence block 54 (by decide) (by decide)
  simp only [map_toBitVec_getElem!] at hs
  refine hs.trans ?_
  change (word block 38) + bitVecSmallSigma0 (word block 39) + (word block 47) + bitVecSmallSigma1 (word block 52) = ((((word block 39)).rotateLeft 14 ^^^ ((word block 39)).rotateLeft 25 ^^^ ((word block 39) >>> 3)) + (((word block 52)).rotateLeft 13 ^^^ ((word block 52)).rotateLeft 15 ^^^ ((word block 52) >>> 10)) + (word block 38) + (word block 47))
  simp only [bitVecSmallSigma0, bitVecSmallSigma1]
  generalize (word block 38) = v0
  generalize (word block 39) = v1
  generalize (word block 47) = v2
  generalize (word block 52) = v3
  ac_rfl

theorem w55 (block : Array Bool) :
    (word block 55) = ((((word block 40)).rotateLeft 14 ^^^ ((word block 40)).rotateLeft 25 ^^^ ((word block 40) >>> 3)) + (((word block 53)).rotateLeft 13 ^^^ ((word block 53)).rotateLeft 15 ^^^ ((word block 53) >>> 10)) + (word block 39) + (word block 48)) := by
  have hs := schedule_toBitVec_recurrence block 55 (by decide) (by decide)
  simp only [map_toBitVec_getElem!] at hs
  refine hs.trans ?_
  change (word block 39) + bitVecSmallSigma0 (word block 40) + (word block 48) + bitVecSmallSigma1 (word block 53) = ((((word block 40)).rotateLeft 14 ^^^ ((word block 40)).rotateLeft 25 ^^^ ((word block 40) >>> 3)) + (((word block 53)).rotateLeft 13 ^^^ ((word block 53)).rotateLeft 15 ^^^ ((word block 53) >>> 10)) + (word block 39) + (word block 48))
  simp only [bitVecSmallSigma0, bitVecSmallSigma1]
  generalize (word block 39) = v0
  generalize (word block 40) = v1
  generalize (word block 48) = v2
  generalize (word block 53) = v3
  ac_rfl

theorem w56 (block : Array Bool) :
    (word block 56) = ((((word block 41)).rotateLeft 14 ^^^ ((word block 41)).rotateLeft 25 ^^^ ((word block 41) >>> 3)) + (((word block 54)).rotateLeft 13 ^^^ ((word block 54)).rotateLeft 15 ^^^ ((word block 54) >>> 10)) + (word block 40) + (word block 49)) := by
  have hs := schedule_toBitVec_recurrence block 56 (by decide) (by decide)
  simp only [map_toBitVec_getElem!] at hs
  refine hs.trans ?_
  change (word block 40) + bitVecSmallSigma0 (word block 41) + (word block 49) + bitVecSmallSigma1 (word block 54) = ((((word block 41)).rotateLeft 14 ^^^ ((word block 41)).rotateLeft 25 ^^^ ((word block 41) >>> 3)) + (((word block 54)).rotateLeft 13 ^^^ ((word block 54)).rotateLeft 15 ^^^ ((word block 54) >>> 10)) + (word block 40) + (word block 49))
  simp only [bitVecSmallSigma0, bitVecSmallSigma1]
  generalize (word block 40) = v0
  generalize (word block 41) = v1
  generalize (word block 49) = v2
  generalize (word block 54) = v3
  ac_rfl

theorem w57 (block : Array Bool) :
    (word block 57) = ((((word block 42)).rotateLeft 14 ^^^ ((word block 42)).rotateLeft 25 ^^^ ((word block 42) >>> 3)) + (((word block 55)).rotateLeft 13 ^^^ ((word block 55)).rotateLeft 15 ^^^ ((word block 55) >>> 10)) + (word block 41) + (word block 50)) := by
  have hs := schedule_toBitVec_recurrence block 57 (by decide) (by decide)
  simp only [map_toBitVec_getElem!] at hs
  refine hs.trans ?_
  change (word block 41) + bitVecSmallSigma0 (word block 42) + (word block 50) + bitVecSmallSigma1 (word block 55) = ((((word block 42)).rotateLeft 14 ^^^ ((word block 42)).rotateLeft 25 ^^^ ((word block 42) >>> 3)) + (((word block 55)).rotateLeft 13 ^^^ ((word block 55)).rotateLeft 15 ^^^ ((word block 55) >>> 10)) + (word block 41) + (word block 50))
  simp only [bitVecSmallSigma0, bitVecSmallSigma1]
  generalize (word block 41) = v0
  generalize (word block 42) = v1
  generalize (word block 50) = v2
  generalize (word block 55) = v3
  ac_rfl

theorem w58 (block : Array Bool) :
    (word block 58) = ((((word block 43)).rotateLeft 14 ^^^ ((word block 43)).rotateLeft 25 ^^^ ((word block 43) >>> 3)) + (((word block 56)).rotateLeft 13 ^^^ ((word block 56)).rotateLeft 15 ^^^ ((word block 56) >>> 10)) + (word block 42) + (word block 51)) := by
  have hs := schedule_toBitVec_recurrence block 58 (by decide) (by decide)
  simp only [map_toBitVec_getElem!] at hs
  refine hs.trans ?_
  change (word block 42) + bitVecSmallSigma0 (word block 43) + (word block 51) + bitVecSmallSigma1 (word block 56) = ((((word block 43)).rotateLeft 14 ^^^ ((word block 43)).rotateLeft 25 ^^^ ((word block 43) >>> 3)) + (((word block 56)).rotateLeft 13 ^^^ ((word block 56)).rotateLeft 15 ^^^ ((word block 56) >>> 10)) + (word block 42) + (word block 51))
  simp only [bitVecSmallSigma0, bitVecSmallSigma1]
  generalize (word block 42) = v0
  generalize (word block 43) = v1
  generalize (word block 51) = v2
  generalize (word block 56) = v3
  ac_rfl

theorem w59 (block : Array Bool) :
    (word block 59) = ((((word block 44)).rotateLeft 14 ^^^ ((word block 44)).rotateLeft 25 ^^^ ((word block 44) >>> 3)) + (((word block 57)).rotateLeft 13 ^^^ ((word block 57)).rotateLeft 15 ^^^ ((word block 57) >>> 10)) + (word block 43) + (word block 52)) := by
  have hs := schedule_toBitVec_recurrence block 59 (by decide) (by decide)
  simp only [map_toBitVec_getElem!] at hs
  refine hs.trans ?_
  change (word block 43) + bitVecSmallSigma0 (word block 44) + (word block 52) + bitVecSmallSigma1 (word block 57) = ((((word block 44)).rotateLeft 14 ^^^ ((word block 44)).rotateLeft 25 ^^^ ((word block 44) >>> 3)) + (((word block 57)).rotateLeft 13 ^^^ ((word block 57)).rotateLeft 15 ^^^ ((word block 57) >>> 10)) + (word block 43) + (word block 52))
  simp only [bitVecSmallSigma0, bitVecSmallSigma1]
  generalize (word block 43) = v0
  generalize (word block 44) = v1
  generalize (word block 52) = v2
  generalize (word block 57) = v3
  ac_rfl

theorem w60 (block : Array Bool) :
    (word block 60) = ((((word block 45)).rotateLeft 14 ^^^ ((word block 45)).rotateLeft 25 ^^^ ((word block 45) >>> 3)) + (((word block 58)).rotateLeft 13 ^^^ ((word block 58)).rotateLeft 15 ^^^ ((word block 58) >>> 10)) + (word block 44) + (word block 53)) := by
  have hs := schedule_toBitVec_recurrence block 60 (by decide) (by decide)
  simp only [map_toBitVec_getElem!] at hs
  refine hs.trans ?_
  change (word block 44) + bitVecSmallSigma0 (word block 45) + (word block 53) + bitVecSmallSigma1 (word block 58) = ((((word block 45)).rotateLeft 14 ^^^ ((word block 45)).rotateLeft 25 ^^^ ((word block 45) >>> 3)) + (((word block 58)).rotateLeft 13 ^^^ ((word block 58)).rotateLeft 15 ^^^ ((word block 58) >>> 10)) + (word block 44) + (word block 53))
  simp only [bitVecSmallSigma0, bitVecSmallSigma1]
  generalize (word block 44) = v0
  generalize (word block 45) = v1
  generalize (word block 53) = v2
  generalize (word block 58) = v3
  ac_rfl

theorem w61 (block : Array Bool) :
    (word block 61) = ((((word block 46)).rotateLeft 14 ^^^ ((word block 46)).rotateLeft 25 ^^^ ((word block 46) >>> 3)) + (((word block 59)).rotateLeft 13 ^^^ ((word block 59)).rotateLeft 15 ^^^ ((word block 59) >>> 10)) + (word block 45) + (word block 54)) := by
  have hs := schedule_toBitVec_recurrence block 61 (by decide) (by decide)
  simp only [map_toBitVec_getElem!] at hs
  refine hs.trans ?_
  change (word block 45) + bitVecSmallSigma0 (word block 46) + (word block 54) + bitVecSmallSigma1 (word block 59) = ((((word block 46)).rotateLeft 14 ^^^ ((word block 46)).rotateLeft 25 ^^^ ((word block 46) >>> 3)) + (((word block 59)).rotateLeft 13 ^^^ ((word block 59)).rotateLeft 15 ^^^ ((word block 59) >>> 10)) + (word block 45) + (word block 54))
  simp only [bitVecSmallSigma0, bitVecSmallSigma1]
  generalize (word block 45) = v0
  generalize (word block 46) = v1
  generalize (word block 54) = v2
  generalize (word block 59) = v3
  ac_rfl

theorem w62 (block : Array Bool) :
    (word block 62) = ((((word block 47)).rotateLeft 14 ^^^ ((word block 47)).rotateLeft 25 ^^^ ((word block 47) >>> 3)) + (((word block 60)).rotateLeft 13 ^^^ ((word block 60)).rotateLeft 15 ^^^ ((word block 60) >>> 10)) + (word block 46) + (word block 55)) := by
  have hs := schedule_toBitVec_recurrence block 62 (by decide) (by decide)
  simp only [map_toBitVec_getElem!] at hs
  refine hs.trans ?_
  change (word block 46) + bitVecSmallSigma0 (word block 47) + (word block 55) + bitVecSmallSigma1 (word block 60) = ((((word block 47)).rotateLeft 14 ^^^ ((word block 47)).rotateLeft 25 ^^^ ((word block 47) >>> 3)) + (((word block 60)).rotateLeft 13 ^^^ ((word block 60)).rotateLeft 15 ^^^ ((word block 60) >>> 10)) + (word block 46) + (word block 55))
  simp only [bitVecSmallSigma0, bitVecSmallSigma1]
  generalize (word block 46) = v0
  generalize (word block 47) = v1
  generalize (word block 55) = v2
  generalize (word block 60) = v3
  ac_rfl

theorem w63 (block : Array Bool) :
    (word block 63) = ((((word block 48)).rotateLeft 14 ^^^ ((word block 48)).rotateLeft 25 ^^^ ((word block 48) >>> 3)) + (((word block 61)).rotateLeft 13 ^^^ ((word block 61)).rotateLeft 15 ^^^ ((word block 61) >>> 10)) + (word block 47) + (word block 56)) := by
  have hs := schedule_toBitVec_recurrence block 63 (by decide) (by decide)
  simp only [map_toBitVec_getElem!] at hs
  refine hs.trans ?_
  change (word block 47) + bitVecSmallSigma0 (word block 48) + (word block 56) + bitVecSmallSigma1 (word block 61) = ((((word block 48)).rotateLeft 14 ^^^ ((word block 48)).rotateLeft 25 ^^^ ((word block 48) >>> 3)) + (((word block 61)).rotateLeft 13 ^^^ ((word block 61)).rotateLeft 15 ^^^ ((word block 61) >>> 10)) + (word block 47) + (word block 56))
  simp only [bitVecSmallSigma0, bitVecSmallSigma1]
  generalize (word block 47) = v0
  generalize (word block 48) = v1
  generalize (word block 56) = v2
  generalize (word block 61) = v3
  ac_rfl

end Hkdf.Proofs.Common.SHA256.Compression.Values.Correctness
