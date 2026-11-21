import AesGcm.Proofs.Machine.Fixslice.Representation

namespace AesGcm.Proofs.Machine.Fixslice

def doubleBits (b : BitVec 8) : BitVec 16 :=
  let x := b.zeroExtend 16
  let x := (x ||| (x <<< 4)) &&& 0x0f0f
  let x := (x ||| (x <<< 2)) &&& 0x3333
  let x := (x ||| (x <<< 1)) &&& 0x5555
  x ||| (x <<< 1)

def packRows (r0 r1 r2 r3 : BitVec 8) : BitVec 64 :=
  (doubleBits r0).zeroExtend 64 ||| ((doubleBits r1).zeroExtend 64 <<< 16) |||
    ((doubleBits r2).zeroExtend 64 <<< 32) ||| ((doubleBits r3).zeroExtend 64 <<< 48)

def uniformRow (b : BitVec 8) : BitVec 64 :=
  (doubleBits b).zeroExtend 64 * 0x0001000100010001

def deltaSwap1 (x : BitVec 64) (shift : Nat) (mask : BitVec 64) : BitVec 64 :=
  let t := (x ^^^ (x >>> shift)) &&& mask
  x ^^^ t ^^^ (t <<< shift)

def shiftRowsWord1 (x : BitVec 64) : BitVec 64 :=
  deltaSwap1 (deltaSwap1 x 8 (packRows 0 0x03 0x0f 0x0c)) 4
    (packRows 0 0x33 0 0x33)

def shiftRowsIndex (n i : Nat) : Nat :=
  16 * (i / 16) + 4 * ((i / 4 % 4 + n * (i / 16)) % 4) + i % 4

private theorem bne_left_comm (a b c : Bool) :
    (a != (b != c)) = (b != (a != c)) := by decide +kernel +revert

private theorem bne_cancel_middle (a b : Bool) :
    (a != (b != a)) = b := by decide +kernel +revert

set_option maxHeartbeats 800000 in
theorem getLsbD_shiftRowsWord1 (x : BitVec 64) (i : Fin 64) :
    (shiftRowsWord1 x).getLsbD i.val = x.getLsbD (shiftRowsIndex 1 i.val) := by
  have h : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 ∨ i.val = 6 ∨ i.val = 7 ∨ i.val = 8 ∨ i.val = 9 ∨ i.val = 10 ∨ i.val = 11 ∨ i.val = 12 ∨ i.val = 13 ∨ i.val = 14 ∨ i.val = 15 ∨ i.val = 16 ∨ i.val = 17 ∨ i.val = 18 ∨ i.val = 19 ∨ i.val = 20 ∨ i.val = 21 ∨ i.val = 22 ∨ i.val = 23 ∨ i.val = 24 ∨ i.val = 25 ∨ i.val = 26 ∨ i.val = 27 ∨ i.val = 28 ∨ i.val = 29 ∨ i.val = 30 ∨ i.val = 31 ∨ i.val = 32 ∨ i.val = 33 ∨ i.val = 34 ∨ i.val = 35 ∨ i.val = 36 ∨ i.val = 37 ∨ i.val = 38 ∨ i.val = 39 ∨ i.val = 40 ∨ i.val = 41 ∨ i.val = 42 ∨ i.val = 43 ∨ i.val = 44 ∨ i.val = 45 ∨ i.val = 46 ∨ i.val = 47 ∨ i.val = 48 ∨ i.val = 49 ∨ i.val = 50 ∨ i.val = 51 ∨ i.val = 52 ∨ i.val = 53 ∨ i.val = 54 ∨ i.val = 55 ∨ i.val = 56 ∨ i.val = 57 ∨ i.val = 58 ∨ i.val = 59 ∨ i.val = 60 ∨ i.val = 61 ∨ i.val = 62 ∨ i.val = 63 := by omega
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals simp [h, shiftRowsWord1, deltaSwap1, packRows, doubleBits, shiftRowsIndex,
    Bool.xor, bne_left_comm, bne_cancel_middle]


def shiftRowsWord2 (x : BitVec 64) : BitVec 64 :=
  deltaSwap1 x 8 (packRows 0 0x0f 0 0x0f)

def shiftRowsWord3 (x : BitVec 64) : BitVec 64 :=
  deltaSwap1 (deltaSwap1 x 8 (packRows 0 0x0c 0x0f 0x03)) 4
    (packRows 0 0x33 0 0x33)

def shiftRows1 (x : Planes) : Planes := fun p ↦ shiftRowsWord1 (x p)
def shiftRows2 (x : Planes) : Planes := fun p ↦ shiftRowsWord2 (x p)
def shiftRows3 (x : Planes) : Planes := fun p ↦ shiftRowsWord3 (x p)
def invShiftRows1 := shiftRows3
def invShiftRows2 := shiftRows2
def invShiftRows3 := shiftRows1

def shiftRowsBlocks (n : Nat) (x : Blocks) : Blocks := fun b j ↦
  x b ⟨4 * ((j.val / 4 + n * (j.val % 4)) % 4) + j.val % 4, by omega⟩

def rotateRows1 (x : BitVec 64) : BitVec 64 := x.rotateRight 16
def rotateRows2 (x : BitVec 64) : BitVec 64 := x.rotateRight 32

def rotateRowsAndColumns11 (x : BitVec 64) : BitVec 64 :=
  (x.rotateRight 20 &&& uniformRow 0x3f) ||| (x.rotateRight 4 &&& uniformRow 0xc0)
def rotateRowsAndColumns12 (x : BitVec 64) : BitVec 64 :=
  (x.rotateRight 24 &&& uniformRow 0x0f) ||| (x.rotateRight 8 &&& uniformRow 0xf0)
def rotateRowsAndColumns13 (x : BitVec 64) : BitVec 64 :=
  (x.rotateRight 28 &&& uniformRow 0x03) ||| (x.rotateRight 12 &&& uniformRow 0xfc)
def rotateRowsAndColumns22 (x : BitVec 64) : BitVec 64 :=
  (x.rotateRight 40 &&& uniformRow 0x0f) ||| (x.rotateRight 24 &&& uniformRow 0xf0)

def rotateRowsColumnsIndex (r c i : Nat) : Nat :=
  16 * ((i / 16 + r) % 4) + 4 * ((i / 4 % 4 + c) % 4) + i % 4

set_option maxHeartbeats 800000 in
theorem getLsbD_shiftRowsWord2 (x : BitVec 64) (i : Fin 64) :
    (shiftRowsWord2 x).getLsbD i.val = x.getLsbD (shiftRowsIndex 2 i.val) := by
  have h : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 ∨ i.val = 6 ∨ i.val = 7 ∨ i.val = 8 ∨ i.val = 9 ∨ i.val = 10 ∨ i.val = 11 ∨ i.val = 12 ∨ i.val = 13 ∨ i.val = 14 ∨ i.val = 15 ∨ i.val = 16 ∨ i.val = 17 ∨ i.val = 18 ∨ i.val = 19 ∨ i.val = 20 ∨ i.val = 21 ∨ i.val = 22 ∨ i.val = 23 ∨ i.val = 24 ∨ i.val = 25 ∨ i.val = 26 ∨ i.val = 27 ∨ i.val = 28 ∨ i.val = 29 ∨ i.val = 30 ∨ i.val = 31 ∨ i.val = 32 ∨ i.val = 33 ∨ i.val = 34 ∨ i.val = 35 ∨ i.val = 36 ∨ i.val = 37 ∨ i.val = 38 ∨ i.val = 39 ∨ i.val = 40 ∨ i.val = 41 ∨ i.val = 42 ∨ i.val = 43 ∨ i.val = 44 ∨ i.val = 45 ∨ i.val = 46 ∨ i.val = 47 ∨ i.val = 48 ∨ i.val = 49 ∨ i.val = 50 ∨ i.val = 51 ∨ i.val = 52 ∨ i.val = 53 ∨ i.val = 54 ∨ i.val = 55 ∨ i.val = 56 ∨ i.val = 57 ∨ i.val = 58 ∨ i.val = 59 ∨ i.val = 60 ∨ i.val = 61 ∨ i.val = 62 ∨ i.val = 63 := by omega
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals simp [h, shiftRowsWord2, deltaSwap1, packRows, doubleBits, shiftRowsIndex,
    Bool.xor, bne_left_comm]



set_option maxHeartbeats 800000 in
theorem getLsbD_shiftRowsWord3 (x : BitVec 64) (i : Fin 64) :
    (shiftRowsWord3 x).getLsbD i.val = x.getLsbD (shiftRowsIndex 3 i.val) := by
  have h : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 ∨ i.val = 6 ∨ i.val = 7 ∨ i.val = 8 ∨ i.val = 9 ∨ i.val = 10 ∨ i.val = 11 ∨ i.val = 12 ∨ i.val = 13 ∨ i.val = 14 ∨ i.val = 15 ∨ i.val = 16 ∨ i.val = 17 ∨ i.val = 18 ∨ i.val = 19 ∨ i.val = 20 ∨ i.val = 21 ∨ i.val = 22 ∨ i.val = 23 ∨ i.val = 24 ∨ i.val = 25 ∨ i.val = 26 ∨ i.val = 27 ∨ i.val = 28 ∨ i.val = 29 ∨ i.val = 30 ∨ i.val = 31 ∨ i.val = 32 ∨ i.val = 33 ∨ i.val = 34 ∨ i.val = 35 ∨ i.val = 36 ∨ i.val = 37 ∨ i.val = 38 ∨ i.val = 39 ∨ i.val = 40 ∨ i.val = 41 ∨ i.val = 42 ∨ i.val = 43 ∨ i.val = 44 ∨ i.val = 45 ∨ i.val = 46 ∨ i.val = 47 ∨ i.val = 48 ∨ i.val = 49 ∨ i.val = 50 ∨ i.val = 51 ∨ i.val = 52 ∨ i.val = 53 ∨ i.val = 54 ∨ i.val = 55 ∨ i.val = 56 ∨ i.val = 57 ∨ i.val = 58 ∨ i.val = 59 ∨ i.val = 60 ∨ i.val = 61 ∨ i.val = 62 ∨ i.val = 63 := by omega
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals simp [h, shiftRowsWord3, deltaSwap1, packRows, doubleBits, shiftRowsIndex,
    Bool.xor, bne_left_comm, bne_cancel_middle]



set_option maxHeartbeats 800000 in
theorem getLsbD_rotateRows1 (x : BitVec 64) (i : Fin 64) :
    (rotateRows1 x).getLsbD i.val = x.getLsbD (rotateRowsColumnsIndex 1 0 i.val) := by
  have h : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 ∨ i.val = 6 ∨ i.val = 7 ∨ i.val = 8 ∨ i.val = 9 ∨ i.val = 10 ∨ i.val = 11 ∨ i.val = 12 ∨ i.val = 13 ∨ i.val = 14 ∨ i.val = 15 ∨ i.val = 16 ∨ i.val = 17 ∨ i.val = 18 ∨ i.val = 19 ∨ i.val = 20 ∨ i.val = 21 ∨ i.val = 22 ∨ i.val = 23 ∨ i.val = 24 ∨ i.val = 25 ∨ i.val = 26 ∨ i.val = 27 ∨ i.val = 28 ∨ i.val = 29 ∨ i.val = 30 ∨ i.val = 31 ∨ i.val = 32 ∨ i.val = 33 ∨ i.val = 34 ∨ i.val = 35 ∨ i.val = 36 ∨ i.val = 37 ∨ i.val = 38 ∨ i.val = 39 ∨ i.val = 40 ∨ i.val = 41 ∨ i.val = 42 ∨ i.val = 43 ∨ i.val = 44 ∨ i.val = 45 ∨ i.val = 46 ∨ i.val = 47 ∨ i.val = 48 ∨ i.val = 49 ∨ i.val = 50 ∨ i.val = 51 ∨ i.val = 52 ∨ i.val = 53 ∨ i.val = 54 ∨ i.val = 55 ∨ i.val = 56 ∨ i.val = 57 ∨ i.val = 58 ∨ i.val = 59 ∨ i.val = 60 ∨ i.val = 61 ∨ i.val = 62 ∨ i.val = 63 := by omega
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals simp [h, rotateRows1, rotateRowsColumnsIndex]

set_option maxHeartbeats 800000 in
theorem getLsbD_rotateRows2 (x : BitVec 64) (i : Fin 64) :
    (rotateRows2 x).getLsbD i.val = x.getLsbD (rotateRowsColumnsIndex 2 0 i.val) := by
  have h : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 ∨ i.val = 6 ∨ i.val = 7 ∨ i.val = 8 ∨ i.val = 9 ∨ i.val = 10 ∨ i.val = 11 ∨ i.val = 12 ∨ i.val = 13 ∨ i.val = 14 ∨ i.val = 15 ∨ i.val = 16 ∨ i.val = 17 ∨ i.val = 18 ∨ i.val = 19 ∨ i.val = 20 ∨ i.val = 21 ∨ i.val = 22 ∨ i.val = 23 ∨ i.val = 24 ∨ i.val = 25 ∨ i.val = 26 ∨ i.val = 27 ∨ i.val = 28 ∨ i.val = 29 ∨ i.val = 30 ∨ i.val = 31 ∨ i.val = 32 ∨ i.val = 33 ∨ i.val = 34 ∨ i.val = 35 ∨ i.val = 36 ∨ i.val = 37 ∨ i.val = 38 ∨ i.val = 39 ∨ i.val = 40 ∨ i.val = 41 ∨ i.val = 42 ∨ i.val = 43 ∨ i.val = 44 ∨ i.val = 45 ∨ i.val = 46 ∨ i.val = 47 ∨ i.val = 48 ∨ i.val = 49 ∨ i.val = 50 ∨ i.val = 51 ∨ i.val = 52 ∨ i.val = 53 ∨ i.val = 54 ∨ i.val = 55 ∨ i.val = 56 ∨ i.val = 57 ∨ i.val = 58 ∨ i.val = 59 ∨ i.val = 60 ∨ i.val = 61 ∨ i.val = 62 ∨ i.val = 63 := by omega
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals simp [h, rotateRows2, rotateRowsColumnsIndex]

set_option maxHeartbeats 800000 in
theorem getLsbD_rotateRowsAndColumns11 (x : BitVec 64) (i : Fin 64) :
    (rotateRowsAndColumns11 x).getLsbD i.val = x.getLsbD (rotateRowsColumnsIndex 1 1 i.val) := by
  have h : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 ∨ i.val = 6 ∨ i.val = 7 ∨ i.val = 8 ∨ i.val = 9 ∨ i.val = 10 ∨ i.val = 11 ∨ i.val = 12 ∨ i.val = 13 ∨ i.val = 14 ∨ i.val = 15 ∨ i.val = 16 ∨ i.val = 17 ∨ i.val = 18 ∨ i.val = 19 ∨ i.val = 20 ∨ i.val = 21 ∨ i.val = 22 ∨ i.val = 23 ∨ i.val = 24 ∨ i.val = 25 ∨ i.val = 26 ∨ i.val = 27 ∨ i.val = 28 ∨ i.val = 29 ∨ i.val = 30 ∨ i.val = 31 ∨ i.val = 32 ∨ i.val = 33 ∨ i.val = 34 ∨ i.val = 35 ∨ i.val = 36 ∨ i.val = 37 ∨ i.val = 38 ∨ i.val = 39 ∨ i.val = 40 ∨ i.val = 41 ∨ i.val = 42 ∨ i.val = 43 ∨ i.val = 44 ∨ i.val = 45 ∨ i.val = 46 ∨ i.val = 47 ∨ i.val = 48 ∨ i.val = 49 ∨ i.val = 50 ∨ i.val = 51 ∨ i.val = 52 ∨ i.val = 53 ∨ i.val = 54 ∨ i.val = 55 ∨ i.val = 56 ∨ i.val = 57 ∨ i.val = 58 ∨ i.val = 59 ∨ i.val = 60 ∨ i.val = 61 ∨ i.val = 62 ∨ i.val = 63 := by omega
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals simp [h, rotateRowsAndColumns11, uniformRow, doubleBits, rotateRowsColumnsIndex]

set_option maxHeartbeats 800000 in
theorem getLsbD_rotateRowsAndColumns12 (x : BitVec 64) (i : Fin 64) :
    (rotateRowsAndColumns12 x).getLsbD i.val = x.getLsbD (rotateRowsColumnsIndex 1 2 i.val) := by
  have h : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 ∨ i.val = 6 ∨ i.val = 7 ∨ i.val = 8 ∨ i.val = 9 ∨ i.val = 10 ∨ i.val = 11 ∨ i.val = 12 ∨ i.val = 13 ∨ i.val = 14 ∨ i.val = 15 ∨ i.val = 16 ∨ i.val = 17 ∨ i.val = 18 ∨ i.val = 19 ∨ i.val = 20 ∨ i.val = 21 ∨ i.val = 22 ∨ i.val = 23 ∨ i.val = 24 ∨ i.val = 25 ∨ i.val = 26 ∨ i.val = 27 ∨ i.val = 28 ∨ i.val = 29 ∨ i.val = 30 ∨ i.val = 31 ∨ i.val = 32 ∨ i.val = 33 ∨ i.val = 34 ∨ i.val = 35 ∨ i.val = 36 ∨ i.val = 37 ∨ i.val = 38 ∨ i.val = 39 ∨ i.val = 40 ∨ i.val = 41 ∨ i.val = 42 ∨ i.val = 43 ∨ i.val = 44 ∨ i.val = 45 ∨ i.val = 46 ∨ i.val = 47 ∨ i.val = 48 ∨ i.val = 49 ∨ i.val = 50 ∨ i.val = 51 ∨ i.val = 52 ∨ i.val = 53 ∨ i.val = 54 ∨ i.val = 55 ∨ i.val = 56 ∨ i.val = 57 ∨ i.val = 58 ∨ i.val = 59 ∨ i.val = 60 ∨ i.val = 61 ∨ i.val = 62 ∨ i.val = 63 := by omega
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals simp [h, rotateRowsAndColumns12, uniformRow, doubleBits, rotateRowsColumnsIndex]

set_option maxHeartbeats 800000 in
theorem getLsbD_rotateRowsAndColumns13 (x : BitVec 64) (i : Fin 64) :
    (rotateRowsAndColumns13 x).getLsbD i.val = x.getLsbD (rotateRowsColumnsIndex 1 3 i.val) := by
  have h : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 ∨ i.val = 6 ∨ i.val = 7 ∨ i.val = 8 ∨ i.val = 9 ∨ i.val = 10 ∨ i.val = 11 ∨ i.val = 12 ∨ i.val = 13 ∨ i.val = 14 ∨ i.val = 15 ∨ i.val = 16 ∨ i.val = 17 ∨ i.val = 18 ∨ i.val = 19 ∨ i.val = 20 ∨ i.val = 21 ∨ i.val = 22 ∨ i.val = 23 ∨ i.val = 24 ∨ i.val = 25 ∨ i.val = 26 ∨ i.val = 27 ∨ i.val = 28 ∨ i.val = 29 ∨ i.val = 30 ∨ i.val = 31 ∨ i.val = 32 ∨ i.val = 33 ∨ i.val = 34 ∨ i.val = 35 ∨ i.val = 36 ∨ i.val = 37 ∨ i.val = 38 ∨ i.val = 39 ∨ i.val = 40 ∨ i.val = 41 ∨ i.val = 42 ∨ i.val = 43 ∨ i.val = 44 ∨ i.val = 45 ∨ i.val = 46 ∨ i.val = 47 ∨ i.val = 48 ∨ i.val = 49 ∨ i.val = 50 ∨ i.val = 51 ∨ i.val = 52 ∨ i.val = 53 ∨ i.val = 54 ∨ i.val = 55 ∨ i.val = 56 ∨ i.val = 57 ∨ i.val = 58 ∨ i.val = 59 ∨ i.val = 60 ∨ i.val = 61 ∨ i.val = 62 ∨ i.val = 63 := by omega
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals simp [h, rotateRowsAndColumns13, uniformRow, doubleBits, rotateRowsColumnsIndex]

set_option maxHeartbeats 800000 in
theorem getLsbD_rotateRowsAndColumns22 (x : BitVec 64) (i : Fin 64) :
    (rotateRowsAndColumns22 x).getLsbD i.val = x.getLsbD (rotateRowsColumnsIndex 2 2 i.val) := by
  have h : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 ∨ i.val = 6 ∨ i.val = 7 ∨ i.val = 8 ∨ i.val = 9 ∨ i.val = 10 ∨ i.val = 11 ∨ i.val = 12 ∨ i.val = 13 ∨ i.val = 14 ∨ i.val = 15 ∨ i.val = 16 ∨ i.val = 17 ∨ i.val = 18 ∨ i.val = 19 ∨ i.val = 20 ∨ i.val = 21 ∨ i.val = 22 ∨ i.val = 23 ∨ i.val = 24 ∨ i.val = 25 ∨ i.val = 26 ∨ i.val = 27 ∨ i.val = 28 ∨ i.val = 29 ∨ i.val = 30 ∨ i.val = 31 ∨ i.val = 32 ∨ i.val = 33 ∨ i.val = 34 ∨ i.val = 35 ∨ i.val = 36 ∨ i.val = 37 ∨ i.val = 38 ∨ i.val = 39 ∨ i.val = 40 ∨ i.val = 41 ∨ i.val = 42 ∨ i.val = 43 ∨ i.val = 44 ∨ i.val = 45 ∨ i.val = 46 ∨ i.val = 47 ∨ i.val = 48 ∨ i.val = 49 ∨ i.val = 50 ∨ i.val = 51 ∨ i.val = 52 ∨ i.val = 53 ∨ i.val = 54 ∨ i.val = 55 ∨ i.val = 56 ∨ i.val = 57 ∨ i.val = 58 ∨ i.val = 59 ∨ i.val = 60 ∨ i.val = 61 ∨ i.val = 62 ∨ i.val = 63 := by omega
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals simp [h, rotateRowsAndColumns22, uniformRow, doubleBits, rotateRowsColumnsIndex]

theorem shiftRowsIndex_lt (n : Nat) (i : Fin 64) : shiftRowsIndex n i.val < 64 := by
  unfold shiftRowsIndex
  omega

theorem shiftRowsWord_encode (f : BitVec 64 → BitVec 64) (n : Nat)
    (h : ∀ (x : BitVec 64) (i : Fin 64), (f x).getLsbD i.val = x.getLsbD (shiftRowsIndex n i.val))
    (x : Blocks) : (fun p ↦ f (encode x p)) = encode (shiftRowsBlocks n x) := by
  funext p
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [show i = (⟨i, hi⟩ : Fin 64).val from rfl, h,
    getLsbD_encode _ _ ⟨shiftRowsIndex n i, shiftRowsIndex_lt n ⟨i, hi⟩⟩,
    getLsbD_encode _ _ ⟨i, hi⟩]
  simp only [shiftRowsBlocks]
  have hs : shiftRowsIndex n i % 4 = i % 4 ∧
      shiftRowsIndex n i / 16 = i / 16 ∧
      shiftRowsIndex n i / 4 % 4 = (i / 4 % 4 + n * (i / 16)) % 4 := by
    unfold shiftRowsIndex
    omega
  have ht : (4 * (i / 4 % 4) + i / 16) / 4 = i / 4 % 4 ∧
      (4 * (i / 4 % 4) + i / 16) % 4 = i / 16 := by omega
  simp only [hs.1, hs.2.1, hs.2.2, ht.1, ht.2]

theorem shiftRows1_encode (x : Blocks) : shiftRows1 (encode x) = encode (shiftRowsBlocks 1 x) :=
  shiftRowsWord_encode shiftRowsWord1 1 getLsbD_shiftRowsWord1 x

theorem shiftRows2_encode (x : Blocks) : shiftRows2 (encode x) = encode (shiftRowsBlocks 2 x) :=
  shiftRowsWord_encode shiftRowsWord2 2 getLsbD_shiftRowsWord2 x

theorem shiftRows3_encode (x : Blocks) : shiftRows3 (encode x) = encode (shiftRowsBlocks 3 x) :=
  shiftRowsWord_encode shiftRowsWord3 3 getLsbD_shiftRowsWord3 x

theorem invShiftRows1_encode (x : Blocks) : invShiftRows1 (encode x) = encode (shiftRowsBlocks 3 x) :=
  shiftRows3_encode x

theorem invShiftRows2_encode (x : Blocks) : invShiftRows2 (encode x) = encode (shiftRowsBlocks 2 x) :=
  shiftRows2_encode x

theorem invShiftRows3_encode (x : Blocks) : invShiftRows3 (encode x) = encode (shiftRowsBlocks 1 x) :=
  shiftRows1_encode x

theorem getLsbD_rotateRight_mod (x : BitVec 64) (r : Nat) (i : Fin 64) :
    (x.rotateRight r).getLsbD i.val = x.getLsbD ((i.val + r) % 64) := by
  rw [BitVec.getLsbD_rotateRight]
  have hr : r % 64 < 64 := Nat.mod_lt _ (by decide)
  split
  · congr 1
    omega
  · simp only [i.isLt, decide_true, Bool.true_and]
    congr 1
    omega

theorem rotateRowsColumnsIndex_lt (r c : Nat) (i : Fin 64) :
    rotateRowsColumnsIndex r c i.val < 64 := by
  unfold rotateRowsColumnsIndex
  omega

set_option maxHeartbeats 400000 in
theorem getLsbD_doubleBits (b : BitVec 8) (i : Fin 16) :
    (doubleBits b).getLsbD i.val = b.getLsbD (i.val / 2) := by
  have h : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 ∨ i.val = 6 ∨ i.val = 7 ∨ i.val = 8 ∨ i.val = 9 ∨ i.val = 10 ∨ i.val = 11 ∨ i.val = 12 ∨ i.val = 13 ∨ i.val = 14 ∨ i.val = 15 := by omega
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals simp [h, doubleBits]

set_option maxHeartbeats 800000 in
theorem getLsbD_packRows (r0 r1 r2 r3 : BitVec 8) (i : Fin 64) :
    (packRows r0 r1 r2 r3).getLsbD i.val =
      (if i.val / 16 = 0 then r0 else if i.val / 16 = 1 then r1 else
        if i.val / 16 = 2 then r2 else r3).getLsbD ((i.val % 16) / 2) := by
  have h : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 ∨ i.val = 6 ∨ i.val = 7 ∨ i.val = 8 ∨ i.val = 9 ∨ i.val = 10 ∨ i.val = 11 ∨ i.val = 12 ∨ i.val = 13 ∨ i.val = 14 ∨ i.val = 15 ∨ i.val = 16 ∨ i.val = 17 ∨ i.val = 18 ∨ i.val = 19 ∨ i.val = 20 ∨ i.val = 21 ∨ i.val = 22 ∨ i.val = 23 ∨ i.val = 24 ∨ i.val = 25 ∨ i.val = 26 ∨ i.val = 27 ∨ i.val = 28 ∨ i.val = 29 ∨ i.val = 30 ∨ i.val = 31 ∨ i.val = 32 ∨ i.val = 33 ∨ i.val = 34 ∨ i.val = 35 ∨ i.val = 36 ∨ i.val = 37 ∨ i.val = 38 ∨ i.val = 39 ∨ i.val = 40 ∨ i.val = 41 ∨ i.val = 42 ∨ i.val = 43 ∨ i.val = 44 ∨ i.val = 45 ∨ i.val = 46 ∨ i.val = 47 ∨ i.val = 48 ∨ i.val = 49 ∨ i.val = 50 ∨ i.val = 51 ∨ i.val = 52 ∨ i.val = 53 ∨ i.val = 54 ∨ i.val = 55 ∨ i.val = 56 ∨ i.val = 57 ∨ i.val = 58 ∨ i.val = 59 ∨ i.val = 60 ∨ i.val = 61 ∨ i.val = 62 ∨ i.val = 63 := by omega
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals simp [h, packRows, doubleBits]

set_option maxHeartbeats 800000 in
theorem uniformRow_eq_packRows (b : BitVec 8) : uniformRow b = packRows b b b b := by
  decide +kernel +revert

theorem getLsbD_uniformRow (b : BitVec 8) (i : Fin 64) :
    (uniformRow b).getLsbD i.val = b.getLsbD ((i.val % 16) / 2) := by
  rw [uniformRow_eq_packRows, getLsbD_packRows]
  simp only [ite_self]

end AesGcm.Proofs.Machine.Fixslice
