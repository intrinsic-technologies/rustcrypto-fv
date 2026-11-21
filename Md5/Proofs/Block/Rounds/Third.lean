import Md5.Proofs.Block.Rounds.Second

namespace Md5.Proofs.Block.Rounds

open Standards.RFC.MD5

def Invariant33 (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) : Prop :=
  s (.stack 4) = X[9] ∧
  s (.stack 8) = initial.B ∧
  s (.stack 20) = X[13] ∧
  s (.stack 24) = X[8] ∧
  s (.stack 28) = X[4] ∧
  s (.stack 32) = X[11] ∧
  s (.stack 36) = X[14] ∧
  s (.stack 40) = X[10] ∧
  s (.stack 48) = X[15] ∧
  s (.stack 56) = X[6] ∧
  s (.stack 60) = initial.A ∧
  s (.stack 64) = X[5] ∧
  s (.stack 72) = X[3] ∧
  s (.stack 80) = X[1] ∧
  s (.stack 88) = X[0] ∧
  s (.stack 120) = initial.C ∧
  s (.stack 128) = initial.D ∧
  s (.reg 0) = working.B ∧
  s (.reg 1) = working.D ∧
  s (.reg 2) = working.A ∧
  s (.reg 5) = working.C ∧
  s (.reg 7) = X[4] ∧
  s (.reg 8) = X[7] ∧
  s (.reg 9) = X[3] ∧
  s (.reg 10) = X[13] ∧
  s (.reg 11) = X[12] ∧
  s (.reg 13) = X[2] ∧
  s (.reg 14) = X[8] ∧
  s (.reg 15) = (working.C ^^^ working.D)

def segment33 : List WordInstruction := [
  .mov (.reg 15) (.location (.reg 5)),
  .xor (.reg 15) (.location (.reg 1)),
  .mov (.reg 0) (.location (.reg 15)),
  .xor (.reg 0) (.location (.reg 2)),
  .add (.reg 0) (.location (.reg 12)),
  .add (.reg 0) (.immediate 0xfffa3942),
  .rol (.reg 0) 4,
  .add (.reg 0) (.location (.reg 5))]

theorem segment33_correct (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) (h : Invariant32 initial X working s) :
    Invariant33 initial X (operation H X[5] 0xfffa3942 4 working) (executeWords segment33 s) := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    h18, h19, h20, h21, h22, h23, h24, h25, h26, h27⟩
  with_unfolding_all change (s (.stack 4)) = X[9] ∧
    (s (.stack 8)) = initial.B ∧
    (s (.stack 20)) = X[13] ∧
    (s (.stack 24)) = X[8] ∧
    (s (.stack 28)) = X[4] ∧
    (s (.stack 32)) = X[11] ∧
    (s (.stack 36)) = X[14] ∧
    (s (.stack 40)) = X[10] ∧
    (s (.stack 48)) = X[15] ∧
    (s (.stack 56)) = X[6] ∧
    (s (.stack 60)) = initial.A ∧
    (s (.stack 64)) = X[5] ∧
    (s (.stack 72)) = X[3] ∧
    (s (.stack 80)) = X[1] ∧
    (s (.stack 88)) = X[0] ∧
    (s (.stack 120)) = initial.C ∧
    (s (.stack 128)) = initial.D ∧
    (((((((s (.reg 5)) ^^^ (s (.reg 1))) ^^^ (s (.reg 2))) + (s (.reg 12))) +
      0xfffa3942)).rotateLeft 4 + (s (.reg 5))) = (operation H X[5] 0xfffa3942 4 working).B ∧
    (s (.reg 1)) = (operation H X[5] 0xfffa3942 4 working).D ∧
    (s (.reg 2)) = (operation H X[5] 0xfffa3942 4 working).A ∧
    (s (.reg 5)) = (operation H X[5] 0xfffa3942 4 working).C ∧
    (s (.reg 7)) = X[4] ∧
    (s (.reg 8)) = X[7] ∧
    (s (.reg 9)) = X[3] ∧
    (s (.reg 10)) = X[13] ∧
    (s (.reg 11)) = X[12] ∧
    (s (.reg 13)) = X[2] ∧
    (s (.reg 14)) = X[8] ∧
    ((s (.reg 5)) ^^^ (s (.reg 1))) = ((operation H X[5] 0xfffa3942 4 working).C ^^^ (operation H
      X[5] 0xfffa3942 4 working).D)
  simp only [operation, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, true_and, and_true]
  md5_word_arithmetic

def Invariant34 (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) : Prop :=
  s (.stack 4) = X[9] ∧
  s (.stack 8) = initial.B ∧
  s (.stack 20) = X[13] ∧
  s (.stack 24) = X[8] ∧
  s (.stack 28) = X[4] ∧
  s (.stack 32) = X[11] ∧
  s (.stack 36) = X[14] ∧
  s (.stack 40) = X[10] ∧
  s (.stack 48) = X[15] ∧
  s (.stack 56) = X[6] ∧
  s (.stack 60) = initial.A ∧
  s (.stack 64) = X[5] ∧
  s (.stack 72) = X[3] ∧
  s (.stack 80) = X[1] ∧
  s (.stack 88) = X[0] ∧
  s (.stack 120) = initial.C ∧
  s (.stack 128) = initial.D ∧
  s (.reg 0) = working.C ∧
  s (.reg 1) = working.A ∧
  s (.reg 2) = working.B ∧
  s (.reg 5) = working.D ∧
  s (.reg 7) = X[4] ∧
  s (.reg 8) = X[7] ∧
  s (.reg 9) = X[3] ∧
  s (.reg 10) = X[13] ∧
  s (.reg 11) = X[12] ∧
  s (.reg 13) = X[2]

def segment34 : List WordInstruction := [
  .add (.reg 2) (.location (.reg 14)),
  .xor (.reg 15) (.location (.reg 0)),
  .add (.reg 2) (.location (.reg 15)),
  .add (.reg 2) (.immediate 0x8771f681),
  .rol (.reg 2) 11,
  .add (.reg 2) (.location (.reg 0))]

theorem segment34_correct (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) (h : Invariant33 initial X working s) :
    Invariant34 initial X (operation H X[8] 0x8771f681 11 working) (executeWords segment34 s) := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28⟩
  with_unfolding_all change (s (.stack 4)) = X[9] ∧
    (s (.stack 8)) = initial.B ∧
    (s (.stack 20)) = X[13] ∧
    (s (.stack 24)) = X[8] ∧
    (s (.stack 28)) = X[4] ∧
    (s (.stack 32)) = X[11] ∧
    (s (.stack 36)) = X[14] ∧
    (s (.stack 40)) = X[10] ∧
    (s (.stack 48)) = X[15] ∧
    (s (.stack 56)) = X[6] ∧
    (s (.stack 60)) = initial.A ∧
    (s (.stack 64)) = X[5] ∧
    (s (.stack 72)) = X[3] ∧
    (s (.stack 80)) = X[1] ∧
    (s (.stack 88)) = X[0] ∧
    (s (.stack 120)) = initial.C ∧
    (s (.stack 128)) = initial.D ∧
    (s (.reg 0)) = (operation H X[8] 0x8771f681 11 working).C ∧
    (s (.reg 1)) = (operation H X[8] 0x8771f681 11 working).A ∧
    ((((((s (.reg 2)) + (s (.reg 14))) + ((s (.reg 15)) ^^^ (s (.reg 0)))) + 0x8771f681)).rotateLeft
      11 + (s (.reg 0))) = (operation H X[8] 0x8771f681 11 working).B ∧
    (s (.reg 5)) = (operation H X[8] 0x8771f681 11 working).D ∧
    (s (.reg 7)) = X[4] ∧
    (s (.reg 8)) = X[7] ∧
    (s (.reg 9)) = X[3] ∧
    (s (.reg 10)) = X[13] ∧
    (s (.reg 11)) = X[12] ∧
    (s (.reg 13)) = X[2]
  simp only [operation, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, true_and, and_true]
  md5_word_arithmetic

def Invariant35 (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) : Prop :=
  s (.stack 4) = X[9] ∧
  s (.stack 8) = initial.B ∧
  s (.stack 20) = X[13] ∧
  s (.stack 24) = X[8] ∧
  s (.stack 28) = X[4] ∧
  s (.stack 32) = X[11] ∧
  s (.stack 36) = X[14] ∧
  s (.stack 40) = X[10] ∧
  s (.stack 48) = X[15] ∧
  s (.stack 56) = X[6] ∧
  s (.stack 60) = initial.A ∧
  s (.stack 64) = X[5] ∧
  s (.stack 72) = X[3] ∧
  s (.stack 80) = X[1] ∧
  s (.stack 88) = X[0] ∧
  s (.stack 120) = initial.C ∧
  s (.stack 128) = initial.D ∧
  s (.reg 0) = working.D ∧
  s (.reg 2) = working.C ∧
  s (.reg 5) = working.A ∧
  s (.reg 7) = X[4] ∧
  s (.reg 8) = X[7] ∧
  s (.reg 9) = X[3] ∧
  s (.reg 10) = X[13] ∧
  s (.reg 11) = X[12] ∧
  s (.reg 12) = working.B ∧
  s (.reg 13) = X[2] ∧
  s (.reg 15) = (working.C ^^^ working.D)

def segment35 : List WordInstruction := [
  .mov (.reg 15) (.location (.reg 2)),
  .xor (.reg 15) (.location (.reg 0)),
  .mov (.reg 12) (.location (.reg 15)),
  .xor (.reg 12) (.location (.reg 5)),
  .add (.reg 1) (.location (.stack 32)),
  .add (.reg 12) (.location (.reg 1)),
  .add (.reg 12) (.immediate 0x6d9d6122),
  .rol (.reg 12) 16,
  .add (.reg 12) (.location (.reg 2))]

theorem segment35_correct (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) (h : Invariant34 initial X working s) :
    Invariant35 initial X (operation H X[11] 0x6d9d6122 16 working) (executeWords segment35 s) := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    h18, h19, h20, h21, h22, h23, h24, h25, h26⟩
  with_unfolding_all change (s (.stack 4)) = X[9] ∧
    (s (.stack 8)) = initial.B ∧
    (s (.stack 20)) = X[13] ∧
    (s (.stack 24)) = X[8] ∧
    (s (.stack 28)) = X[4] ∧
    (s (.stack 32)) = X[11] ∧
    (s (.stack 36)) = X[14] ∧
    (s (.stack 40)) = X[10] ∧
    (s (.stack 48)) = X[15] ∧
    (s (.stack 56)) = X[6] ∧
    (s (.stack 60)) = initial.A ∧
    (s (.stack 64)) = X[5] ∧
    (s (.stack 72)) = X[3] ∧
    (s (.stack 80)) = X[1] ∧
    (s (.stack 88)) = X[0] ∧
    (s (.stack 120)) = initial.C ∧
    (s (.stack 128)) = initial.D ∧
    (s (.reg 0)) = (operation H X[11] 0x6d9d6122 16 working).D ∧
    (s (.reg 2)) = (operation H X[11] 0x6d9d6122 16 working).C ∧
    (s (.reg 5)) = (operation H X[11] 0x6d9d6122 16 working).A ∧
    (s (.reg 7)) = X[4] ∧
    (s (.reg 8)) = X[7] ∧
    (s (.reg 9)) = X[3] ∧
    (s (.reg 10)) = X[13] ∧
    (s (.reg 11)) = X[12] ∧
    (((((((s (.reg 2)) ^^^ (s (.reg 0))) ^^^ (s (.reg 5))) + ((s (.reg 1)) + (s (.stack 32)))) +
      0x6d9d6122)).rotateLeft 16 + (s (.reg 2))) = (operation H X[11] 0x6d9d6122 16 working).B ∧
    (s (.reg 13)) = X[2] ∧
    ((s (.reg 2)) ^^^ (s (.reg 0))) = ((operation H X[11] 0x6d9d6122 16 working).C ^^^ (operation H
      X[11] 0x6d9d6122 16 working).D)
  simp only [operation, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, true_and, and_true]
  md5_word_arithmetic

def Invariant36 (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) : Prop :=
  s (.stack 4) = X[9] ∧
  s (.stack 8) = initial.B ∧
  s (.stack 20) = X[13] ∧
  s (.stack 24) = X[8] ∧
  s (.stack 28) = X[4] ∧
  s (.stack 32) = X[11] ∧
  s (.stack 40) = X[10] ∧
  s (.stack 48) = X[15] ∧
  s (.stack 56) = X[6] ∧
  s (.stack 60) = initial.A ∧
  s (.stack 64) = X[5] ∧
  s (.stack 72) = X[3] ∧
  s (.stack 80) = X[1] ∧
  s (.stack 88) = X[0] ∧
  s (.stack 120) = initial.C ∧
  s (.stack 128) = initial.D ∧
  s (.reg 0) = working.A ∧
  s (.reg 2) = working.D ∧
  s (.reg 3) = X[14] ∧
  s (.reg 5) = working.B ∧
  s (.reg 7) = X[4] ∧
  s (.reg 8) = X[7] ∧
  s (.reg 9) = X[3] ∧
  s (.reg 10) = X[13] ∧
  s (.reg 11) = X[12] ∧
  s (.reg 12) = working.C ∧
  s (.reg 13) = X[2]

def segment36 : List WordInstruction := [
  .mov (.reg 3) (.location (.stack 36)),
  .add (.reg 5) (.location (.reg 3)),
  .xor (.reg 15) (.location (.reg 12)),
  .add (.reg 5) (.location (.reg 15)),
  .add (.reg 5) (.immediate 0xfde5380c),
  .rol (.reg 5) 23,
  .add (.reg 5) (.location (.reg 12))]

theorem segment36_correct (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) (h : Invariant35 initial X working s) :
    Invariant36 initial X (operation H X[14] 0xfde5380c 23 working) (executeWords segment36 s) := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    h18, h19, h20, h21, h22, h23, h24, h25, h26, h27⟩
  with_unfolding_all change (s (.stack 4)) = X[9] ∧
    (s (.stack 8)) = initial.B ∧
    (s (.stack 20)) = X[13] ∧
    (s (.stack 24)) = X[8] ∧
    (s (.stack 28)) = X[4] ∧
    (s (.stack 32)) = X[11] ∧
    (s (.stack 40)) = X[10] ∧
    (s (.stack 48)) = X[15] ∧
    (s (.stack 56)) = X[6] ∧
    (s (.stack 60)) = initial.A ∧
    (s (.stack 64)) = X[5] ∧
    (s (.stack 72)) = X[3] ∧
    (s (.stack 80)) = X[1] ∧
    (s (.stack 88)) = X[0] ∧
    (s (.stack 120)) = initial.C ∧
    (s (.stack 128)) = initial.D ∧
    (s (.reg 0)) = (operation H X[14] 0xfde5380c 23 working).A ∧
    (s (.reg 2)) = (operation H X[14] 0xfde5380c 23 working).D ∧
    (s (.stack 36)) = X[14] ∧
    ((((((s (.reg 5)) + (s (.stack 36))) + ((s (.reg 15)) ^^^ (s (.reg 12)))) +
      0xfde5380c)).rotateLeft 23 + (s (.reg 12))) = (operation H X[14] 0xfde5380c 23 working).B ∧
    (s (.reg 7)) = X[4] ∧
    (s (.reg 8)) = X[7] ∧
    (s (.reg 9)) = X[3] ∧
    (s (.reg 10)) = X[13] ∧
    (s (.reg 11)) = X[12] ∧
    (s (.reg 12)) = (operation H X[14] 0xfde5380c 23 working).C ∧
    (s (.reg 13)) = X[2]
  simp only [operation, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, true_and, and_true]
  md5_word_arithmetic

def Invariant37 (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) : Prop :=
  s (.stack 4) = X[9] ∧
  s (.stack 8) = initial.B ∧
  s (.stack 20) = X[13] ∧
  s (.stack 24) = X[8] ∧
  s (.stack 28) = X[4] ∧
  s (.stack 32) = X[11] ∧
  s (.stack 40) = X[10] ∧
  s (.stack 48) = X[15] ∧
  s (.stack 56) = X[6] ∧
  s (.stack 60) = initial.A ∧
  s (.stack 64) = X[5] ∧
  s (.stack 72) = X[3] ∧
  s (.stack 80) = X[1] ∧
  s (.stack 88) = X[0] ∧
  s (.stack 120) = initial.C ∧
  s (.stack 128) = initial.D ∧
  s (.reg 1) = working.B ∧
  s (.reg 2) = working.A ∧
  s (.reg 3) = X[14] ∧
  s (.reg 5) = working.C ∧
  s (.reg 7) = X[4] ∧
  s (.reg 8) = X[7] ∧
  s (.reg 9) = X[3] ∧
  s (.reg 10) = X[13] ∧
  s (.reg 11) = X[12] ∧
  s (.reg 12) = working.D ∧
  s (.reg 13) = X[2] ∧
  s (.reg 15) = (working.C ^^^ working.D)

def segment37 : List WordInstruction := [
  .mov (.reg 15) (.location (.reg 5)),
  .xor (.reg 15) (.location (.reg 12)),
  .mov (.reg 1) (.location (.reg 15)),
  .xor (.reg 1) (.location (.reg 2)),
  .add (.reg 0) (.location (.stack 80)),
  .add (.reg 1) (.location (.reg 0)),
  .add (.reg 1) (.immediate 0xa4beea44),
  .rol (.reg 1) 4,
  .add (.reg 1) (.location (.reg 5))]

theorem segment37_correct (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) (h : Invariant36 initial X working s) :
    Invariant37 initial X (operation H X[1] 0xa4beea44 4 working) (executeWords segment37 s) := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    h18, h19, h20, h21, h22, h23, h24, h25, h26⟩
  with_unfolding_all change (s (.stack 4)) = X[9] ∧
    (s (.stack 8)) = initial.B ∧
    (s (.stack 20)) = X[13] ∧
    (s (.stack 24)) = X[8] ∧
    (s (.stack 28)) = X[4] ∧
    (s (.stack 32)) = X[11] ∧
    (s (.stack 40)) = X[10] ∧
    (s (.stack 48)) = X[15] ∧
    (s (.stack 56)) = X[6] ∧
    (s (.stack 60)) = initial.A ∧
    (s (.stack 64)) = X[5] ∧
    (s (.stack 72)) = X[3] ∧
    (s (.stack 80)) = X[1] ∧
    (s (.stack 88)) = X[0] ∧
    (s (.stack 120)) = initial.C ∧
    (s (.stack 128)) = initial.D ∧
    (((((((s (.reg 5)) ^^^ (s (.reg 12))) ^^^ (s (.reg 2))) + ((s (.reg 0)) + (s (.stack 80)))) +
      0xa4beea44)).rotateLeft 4 + (s (.reg 5))) = (operation H X[1] 0xa4beea44 4 working).B ∧
    (s (.reg 2)) = (operation H X[1] 0xa4beea44 4 working).A ∧
    (s (.reg 3)) = X[14] ∧
    (s (.reg 5)) = (operation H X[1] 0xa4beea44 4 working).C ∧
    (s (.reg 7)) = X[4] ∧
    (s (.reg 8)) = X[7] ∧
    (s (.reg 9)) = X[3] ∧
    (s (.reg 10)) = X[13] ∧
    (s (.reg 11)) = X[12] ∧
    (s (.reg 12)) = (operation H X[1] 0xa4beea44 4 working).D ∧
    (s (.reg 13)) = X[2] ∧
    ((s (.reg 5)) ^^^ (s (.reg 12))) = ((operation H X[1] 0xa4beea44 4 working).C ^^^ (operation H
      X[1] 0xa4beea44 4 working).D)
  simp only [operation, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, true_and, and_true]
  md5_word_arithmetic

def Invariant38 (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) : Prop :=
  s (.stack 4) = X[9] ∧
  s (.stack 8) = initial.B ∧
  s (.stack 20) = X[13] ∧
  s (.stack 24) = X[8] ∧
  s (.stack 28) = X[4] ∧
  s (.stack 32) = X[11] ∧
  s (.stack 40) = X[10] ∧
  s (.stack 48) = X[15] ∧
  s (.stack 56) = X[6] ∧
  s (.stack 60) = initial.A ∧
  s (.stack 64) = X[5] ∧
  s (.stack 72) = X[3] ∧
  s (.stack 80) = X[1] ∧
  s (.stack 88) = X[0] ∧
  s (.stack 120) = initial.C ∧
  s (.stack 128) = initial.D ∧
  s (.reg 1) = working.C ∧
  s (.reg 2) = working.B ∧
  s (.reg 3) = X[14] ∧
  s (.reg 5) = working.D ∧
  s (.reg 8) = X[7] ∧
  s (.reg 9) = X[3] ∧
  s (.reg 10) = X[13] ∧
  s (.reg 11) = X[12] ∧
  s (.reg 12) = working.A ∧
  s (.reg 13) = X[2]

def segment38 : List WordInstruction := [
  .add (.reg 2) (.location (.reg 7)),
  .xor (.reg 15) (.location (.reg 1)),
  .add (.reg 2) (.location (.reg 15)),
  .add (.reg 2) (.immediate 0x4bdecfa9),
  .rol (.reg 2) 11,
  .add (.reg 2) (.location (.reg 1))]

theorem segment38_correct (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) (h : Invariant37 initial X working s) :
    Invariant38 initial X (operation H X[4] 0x4bdecfa9 11 working) (executeWords segment38 s) := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    h18, h19, h20, h21, h22, h23, h24, h25, h26, h27⟩
  with_unfolding_all change (s (.stack 4)) = X[9] ∧
    (s (.stack 8)) = initial.B ∧
    (s (.stack 20)) = X[13] ∧
    (s (.stack 24)) = X[8] ∧
    (s (.stack 28)) = X[4] ∧
    (s (.stack 32)) = X[11] ∧
    (s (.stack 40)) = X[10] ∧
    (s (.stack 48)) = X[15] ∧
    (s (.stack 56)) = X[6] ∧
    (s (.stack 60)) = initial.A ∧
    (s (.stack 64)) = X[5] ∧
    (s (.stack 72)) = X[3] ∧
    (s (.stack 80)) = X[1] ∧
    (s (.stack 88)) = X[0] ∧
    (s (.stack 120)) = initial.C ∧
    (s (.stack 128)) = initial.D ∧
    (s (.reg 1)) = (operation H X[4] 0x4bdecfa9 11 working).C ∧
    ((((((s (.reg 2)) + (s (.reg 7))) + ((s (.reg 15)) ^^^ (s (.reg 1)))) + 0x4bdecfa9)).rotateLeft
      11 + (s (.reg 1))) = (operation H X[4] 0x4bdecfa9 11 working).B ∧
    (s (.reg 3)) = X[14] ∧
    (s (.reg 5)) = (operation H X[4] 0x4bdecfa9 11 working).D ∧
    (s (.reg 8)) = X[7] ∧
    (s (.reg 9)) = X[3] ∧
    (s (.reg 10)) = X[13] ∧
    (s (.reg 11)) = X[12] ∧
    (s (.reg 12)) = (operation H X[4] 0x4bdecfa9 11 working).A ∧
    (s (.reg 13)) = X[2]
  simp only [operation, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, true_and, and_true]
  md5_word_arithmetic

def Invariant39 (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) : Prop :=
  s (.stack 4) = X[9] ∧
  s (.stack 8) = initial.B ∧
  s (.stack 20) = X[13] ∧
  s (.stack 24) = X[8] ∧
  s (.stack 28) = X[4] ∧
  s (.stack 32) = X[11] ∧
  s (.stack 40) = X[10] ∧
  s (.stack 48) = X[15] ∧
  s (.stack 56) = X[6] ∧
  s (.stack 60) = initial.A ∧
  s (.stack 64) = X[5] ∧
  s (.stack 72) = X[3] ∧
  s (.stack 80) = X[1] ∧
  s (.stack 88) = X[0] ∧
  s (.stack 120) = initial.C ∧
  s (.stack 128) = initial.D ∧
  s (.reg 0) = (working.C ^^^ working.D) ∧
  s (.reg 1) = working.D ∧
  s (.reg 2) = working.C ∧
  s (.reg 3) = X[14] ∧
  s (.reg 5) = working.A ∧
  s (.reg 8) = X[7] ∧
  s (.reg 9) = X[3] ∧
  s (.reg 10) = X[13] ∧
  s (.reg 11) = X[12] ∧
  s (.reg 12) = working.B ∧
  s (.reg 13) = X[2]

def segment39 : List WordInstruction := [
  .mov (.reg 0) (.location (.reg 2)),
  .xor (.reg 0) (.location (.reg 1)),
  .mov (.reg 15) (.location (.reg 0)),
  .xor (.reg 15) (.location (.reg 5)),
  .add (.reg 12) (.location (.reg 8)),
  .add (.reg 12) (.location (.reg 15)),
  .add (.reg 12) (.immediate 0xf6bb4b60),
  .rol (.reg 12) 16,
  .add (.reg 12) (.location (.reg 2))]

theorem segment39_correct (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) (h : Invariant38 initial X working s) :
    Invariant39 initial X (operation H X[7] 0xf6bb4b60 16 working) (executeWords segment39 s) := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    h18, h19, h20, h21, h22, h23, h24, h25⟩
  with_unfolding_all change (s (.stack 4)) = X[9] ∧
    (s (.stack 8)) = initial.B ∧
    (s (.stack 20)) = X[13] ∧
    (s (.stack 24)) = X[8] ∧
    (s (.stack 28)) = X[4] ∧
    (s (.stack 32)) = X[11] ∧
    (s (.stack 40)) = X[10] ∧
    (s (.stack 48)) = X[15] ∧
    (s (.stack 56)) = X[6] ∧
    (s (.stack 60)) = initial.A ∧
    (s (.stack 64)) = X[5] ∧
    (s (.stack 72)) = X[3] ∧
    (s (.stack 80)) = X[1] ∧
    (s (.stack 88)) = X[0] ∧
    (s (.stack 120)) = initial.C ∧
    (s (.stack 128)) = initial.D ∧
    ((s (.reg 2)) ^^^ (s (.reg 1))) = ((operation H X[7] 0xf6bb4b60 16 working).C ^^^ (operation H
      X[7] 0xf6bb4b60 16 working).D) ∧
    (s (.reg 1)) = (operation H X[7] 0xf6bb4b60 16 working).D ∧
    (s (.reg 2)) = (operation H X[7] 0xf6bb4b60 16 working).C ∧
    (s (.reg 3)) = X[14] ∧
    (s (.reg 5)) = (operation H X[7] 0xf6bb4b60 16 working).A ∧
    (s (.reg 8)) = X[7] ∧
    (s (.reg 9)) = X[3] ∧
    (s (.reg 10)) = X[13] ∧
    (s (.reg 11)) = X[12] ∧
    ((((((s (.reg 12)) + (s (.reg 8))) + (((s (.reg 2)) ^^^ (s (.reg 1))) ^^^ (s (.reg 5)))) +
      0xf6bb4b60)).rotateLeft 16 + (s (.reg 2))) = (operation H X[7] 0xf6bb4b60 16 working).B ∧
    (s (.reg 13)) = X[2]
  simp only [operation, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18, h19, h20, h21, h22, h23, h24, h25, true_and, and_true]
  md5_word_arithmetic

def Invariant40 (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) : Prop :=
  s (.stack 4) = X[9] ∧
  s (.stack 8) = initial.B ∧
  s (.stack 20) = X[13] ∧
  s (.stack 24) = X[8] ∧
  s (.stack 28) = X[4] ∧
  s (.stack 32) = X[11] ∧
  s (.stack 48) = X[15] ∧
  s (.stack 56) = X[6] ∧
  s (.stack 60) = initial.A ∧
  s (.stack 64) = X[5] ∧
  s (.stack 72) = X[3] ∧
  s (.stack 80) = X[1] ∧
  s (.stack 88) = X[0] ∧
  s (.stack 120) = initial.C ∧
  s (.stack 128) = initial.D ∧
  s (.reg 0) = working.B ∧
  s (.reg 1) = working.A ∧
  s (.reg 2) = working.D ∧
  s (.reg 3) = X[14] ∧
  s (.reg 8) = X[7] ∧
  s (.reg 9) = X[3] ∧
  s (.reg 10) = X[13] ∧
  s (.reg 11) = X[12] ∧
  s (.reg 12) = working.C ∧
  s (.reg 13) = X[2] ∧
  s (.reg 14) = X[10]

def segment40 : List WordInstruction := [
  .mov (.reg 14) (.location (.stack 40)),
  .add (.reg 5) (.location (.reg 14)),
  .xor (.reg 0) (.location (.reg 12)),
  .add (.reg 0) (.location (.reg 5)),
  .add (.reg 0) (.immediate 0xbebfbc70),
  .rol (.reg 0) 23,
  .add (.reg 0) (.location (.reg 12))]

theorem segment40_correct (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) (h : Invariant39 initial X working s) :
    Invariant40 initial X (operation H X[10] 0xbebfbc70 23 working) (executeWords segment40 s) := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    h18, h19, h20, h21, h22, h23, h24, h25, h26⟩
  with_unfolding_all change (s (.stack 4)) = X[9] ∧
    (s (.stack 8)) = initial.B ∧
    (s (.stack 20)) = X[13] ∧
    (s (.stack 24)) = X[8] ∧
    (s (.stack 28)) = X[4] ∧
    (s (.stack 32)) = X[11] ∧
    (s (.stack 48)) = X[15] ∧
    (s (.stack 56)) = X[6] ∧
    (s (.stack 60)) = initial.A ∧
    (s (.stack 64)) = X[5] ∧
    (s (.stack 72)) = X[3] ∧
    (s (.stack 80)) = X[1] ∧
    (s (.stack 88)) = X[0] ∧
    (s (.stack 120)) = initial.C ∧
    (s (.stack 128)) = initial.D ∧
    ((((((s (.reg 0)) ^^^ (s (.reg 12))) + ((s (.reg 5)) + (s (.stack 40)))) +
      0xbebfbc70)).rotateLeft 23 + (s (.reg 12))) = (operation H X[10] 0xbebfbc70 23 working).B ∧
    (s (.reg 1)) = (operation H X[10] 0xbebfbc70 23 working).A ∧
    (s (.reg 2)) = (operation H X[10] 0xbebfbc70 23 working).D ∧
    (s (.reg 3)) = X[14] ∧
    (s (.reg 8)) = X[7] ∧
    (s (.reg 9)) = X[3] ∧
    (s (.reg 10)) = X[13] ∧
    (s (.reg 11)) = X[12] ∧
    (s (.reg 12)) = (operation H X[10] 0xbebfbc70 23 working).C ∧
    (s (.reg 13)) = X[2] ∧
    (s (.stack 40)) = X[10]
  simp only [operation, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, true_and, and_true]
  md5_word_arithmetic

def Invariant41 (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) : Prop :=
  s (.stack 4) = X[9] ∧
  s (.stack 8) = initial.B ∧
  s (.stack 20) = X[13] ∧
  s (.stack 24) = X[8] ∧
  s (.stack 28) = X[4] ∧
  s (.stack 32) = X[11] ∧
  s (.stack 48) = X[15] ∧
  s (.stack 56) = X[6] ∧
  s (.stack 60) = initial.A ∧
  s (.stack 64) = X[5] ∧
  s (.stack 72) = X[3] ∧
  s (.stack 80) = X[1] ∧
  s (.stack 88) = X[0] ∧
  s (.stack 120) = initial.C ∧
  s (.stack 128) = initial.D ∧
  s (.reg 0) = working.C ∧
  s (.reg 1) = working.B ∧
  s (.reg 2) = working.A ∧
  s (.reg 3) = X[14] ∧
  s (.reg 8) = X[7] ∧
  s (.reg 9) = X[3] ∧
  s (.reg 11) = X[12] ∧
  s (.reg 12) = working.D ∧
  s (.reg 13) = X[2] ∧
  s (.reg 14) = X[10]

def segment41 : List WordInstruction := [
  .mov (.reg 15) (.location (.reg 12)),
  .xor (.reg 15) (.location (.reg 2)),
  .add (.reg 1) (.location (.reg 10)),
  .xor (.reg 15) (.location (.reg 0)),
  .add (.reg 1) (.location (.reg 15)),
  .add (.reg 1) (.immediate 0x289b7ec6),
  .rol (.reg 1) 4,
  .add (.reg 1) (.location (.reg 0))]

theorem segment41_correct (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) (h : Invariant40 initial X working s) :
    Invariant41 initial X (operation H X[13] 0x289b7ec6 4 working) (executeWords segment41 s) := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    h18, h19, h20, h21, h22, h23, h24, h25⟩
  with_unfolding_all change (s (.stack 4)) = X[9] ∧
    (s (.stack 8)) = initial.B ∧
    (s (.stack 20)) = X[13] ∧
    (s (.stack 24)) = X[8] ∧
    (s (.stack 28)) = X[4] ∧
    (s (.stack 32)) = X[11] ∧
    (s (.stack 48)) = X[15] ∧
    (s (.stack 56)) = X[6] ∧
    (s (.stack 60)) = initial.A ∧
    (s (.stack 64)) = X[5] ∧
    (s (.stack 72)) = X[3] ∧
    (s (.stack 80)) = X[1] ∧
    (s (.stack 88)) = X[0] ∧
    (s (.stack 120)) = initial.C ∧
    (s (.stack 128)) = initial.D ∧
    (s (.reg 0)) = (operation H X[13] 0x289b7ec6 4 working).C ∧
    ((((((s (.reg 1)) + (s (.reg 10))) + (((s (.reg 12)) ^^^ (s (.reg 2))) ^^^ (s (.reg 0)))) +
      0x289b7ec6)).rotateLeft 4 + (s (.reg 0))) = (operation H X[13] 0x289b7ec6 4 working).B ∧
    (s (.reg 2)) = (operation H X[13] 0x289b7ec6 4 working).A ∧
    (s (.reg 3)) = X[14] ∧
    (s (.reg 8)) = X[7] ∧
    (s (.reg 9)) = X[3] ∧
    (s (.reg 11)) = X[12] ∧
    (s (.reg 12)) = (operation H X[13] 0x289b7ec6 4 working).D ∧
    (s (.reg 13)) = X[2] ∧
    (s (.reg 14)) = X[10]
  simp only [operation, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18, h19, h20, h21, h22, h23, h24, h25, true_and, and_true]
  md5_word_arithmetic

def Invariant42 (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) : Prop :=
  s (.stack 4) = X[9] ∧
  s (.stack 8) = initial.B ∧
  s (.stack 20) = X[13] ∧
  s (.stack 24) = X[8] ∧
  s (.stack 28) = X[4] ∧
  s (.stack 32) = X[11] ∧
  s (.stack 48) = X[15] ∧
  s (.stack 56) = X[6] ∧
  s (.stack 60) = initial.A ∧
  s (.stack 64) = X[5] ∧
  s (.stack 72) = X[3] ∧
  s (.stack 80) = X[1] ∧
  s (.stack 120) = initial.C ∧
  s (.stack 128) = initial.D ∧
  s (.reg 0) = working.D ∧
  s (.reg 1) = working.C ∧
  s (.reg 2) = working.B ∧
  s (.reg 3) = X[14] ∧
  s (.reg 7) = X[0] ∧
  s (.reg 8) = X[7] ∧
  s (.reg 9) = X[3] ∧
  s (.reg 11) = X[12] ∧
  s (.reg 12) = working.A ∧
  s (.reg 13) = X[2] ∧
  s (.reg 14) = X[10]

def segment42 : List WordInstruction := [
  .mov (.reg 15) (.location (.reg 0)),
  .xor (.reg 15) (.location (.reg 12)),
  .mov (.reg 7) (.location (.stack 88)),
  .add (.reg 2) (.location (.reg 7)),
  .xor (.reg 15) (.location (.reg 1)),
  .add (.reg 2) (.location (.reg 15)),
  .add (.reg 2) (.immediate 0xeaa127fa),
  .rol (.reg 2) 11,
  .add (.reg 2) (.location (.reg 1))]

theorem segment42_correct (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) (h : Invariant41 initial X working s) :
    Invariant42 initial X (operation H X[0] 0xeaa127fa 11 working) (executeWords segment42 s) := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    h18, h19, h20, h21, h22, h23, h24⟩
  with_unfolding_all change (s (.stack 4)) = X[9] ∧
    (s (.stack 8)) = initial.B ∧
    (s (.stack 20)) = X[13] ∧
    (s (.stack 24)) = X[8] ∧
    (s (.stack 28)) = X[4] ∧
    (s (.stack 32)) = X[11] ∧
    (s (.stack 48)) = X[15] ∧
    (s (.stack 56)) = X[6] ∧
    (s (.stack 60)) = initial.A ∧
    (s (.stack 64)) = X[5] ∧
    (s (.stack 72)) = X[3] ∧
    (s (.stack 80)) = X[1] ∧
    (s (.stack 120)) = initial.C ∧
    (s (.stack 128)) = initial.D ∧
    (s (.reg 0)) = (operation H X[0] 0xeaa127fa 11 working).D ∧
    (s (.reg 1)) = (operation H X[0] 0xeaa127fa 11 working).C ∧
    ((((((s (.reg 2)) + (s (.stack 88))) + (((s (.reg 0)) ^^^ (s (.reg 12))) ^^^ (s (.reg 1)))) +
      0xeaa127fa)).rotateLeft 11 + (s (.reg 1))) = (operation H X[0] 0xeaa127fa 11 working).B ∧
    (s (.reg 3)) = X[14] ∧
    (s (.stack 88)) = X[0] ∧
    (s (.reg 8)) = X[7] ∧
    (s (.reg 9)) = X[3] ∧
    (s (.reg 11)) = X[12] ∧
    (s (.reg 12)) = (operation H X[0] 0xeaa127fa 11 working).A ∧
    (s (.reg 13)) = X[2] ∧
    (s (.reg 14)) = X[10]
  simp only [operation, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18, h19, h20, h21, h22, h23, h24, true_and, and_true]
  md5_word_arithmetic

def Invariant43 (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) : Prop :=
  s (.stack 4) = X[9] ∧
  s (.stack 8) = initial.B ∧
  s (.stack 20) = X[13] ∧
  s (.stack 24) = X[8] ∧
  s (.stack 28) = X[4] ∧
  s (.stack 32) = X[11] ∧
  s (.stack 48) = X[15] ∧
  s (.stack 56) = X[6] ∧
  s (.stack 60) = initial.A ∧
  s (.stack 64) = X[5] ∧
  s (.stack 72) = X[3] ∧
  s (.stack 80) = X[1] ∧
  s (.stack 120) = initial.C ∧
  s (.stack 128) = initial.D ∧
  s (.reg 0) = working.A ∧
  s (.reg 1) = working.D ∧
  s (.reg 2) = working.C ∧
  s (.reg 3) = X[14] ∧
  s (.reg 7) = X[0] ∧
  s (.reg 8) = X[7] ∧
  s (.reg 11) = X[12] ∧
  s (.reg 12) = working.B ∧
  s (.reg 13) = X[2] ∧
  s (.reg 14) = X[10]

def segment43 : List WordInstruction := [
  .mov (.reg 15) (.location (.reg 1)),
  .xor (.reg 15) (.location (.reg 0)),
  .add (.reg 12) (.location (.reg 9)),
  .xor (.reg 15) (.location (.reg 2)),
  .add (.reg 12) (.location (.reg 15)),
  .add (.reg 12) (.immediate 0xd4ef3085),
  .rol (.reg 12) 16,
  .add (.reg 12) (.location (.reg 2))]

theorem segment43_correct (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) (h : Invariant42 initial X working s) :
    Invariant43 initial X (operation H X[3] 0xd4ef3085 16 working) (executeWords segment43 s) := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    h18, h19, h20, h21, h22, h23, h24⟩
  with_unfolding_all change (s (.stack 4)) = X[9] ∧
    (s (.stack 8)) = initial.B ∧
    (s (.stack 20)) = X[13] ∧
    (s (.stack 24)) = X[8] ∧
    (s (.stack 28)) = X[4] ∧
    (s (.stack 32)) = X[11] ∧
    (s (.stack 48)) = X[15] ∧
    (s (.stack 56)) = X[6] ∧
    (s (.stack 60)) = initial.A ∧
    (s (.stack 64)) = X[5] ∧
    (s (.stack 72)) = X[3] ∧
    (s (.stack 80)) = X[1] ∧
    (s (.stack 120)) = initial.C ∧
    (s (.stack 128)) = initial.D ∧
    (s (.reg 0)) = (operation H X[3] 0xd4ef3085 16 working).A ∧
    (s (.reg 1)) = (operation H X[3] 0xd4ef3085 16 working).D ∧
    (s (.reg 2)) = (operation H X[3] 0xd4ef3085 16 working).C ∧
    (s (.reg 3)) = X[14] ∧
    (s (.reg 7)) = X[0] ∧
    (s (.reg 8)) = X[7] ∧
    (s (.reg 11)) = X[12] ∧
    ((((((s (.reg 12)) + (s (.reg 9))) + (((s (.reg 1)) ^^^ (s (.reg 0))) ^^^ (s (.reg 2)))) +
      0xd4ef3085)).rotateLeft 16 + (s (.reg 2))) = (operation H X[3] 0xd4ef3085 16 working).B ∧
    (s (.reg 13)) = X[2] ∧
    (s (.reg 14)) = X[10]
  simp only [operation, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18, h19, h20, h21, h22, h23, h24, true_and, and_true]
  md5_word_arithmetic

def Invariant44 (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) : Prop :=
  s (.stack 4) = X[9] ∧
  s (.stack 8) = initial.B ∧
  s (.stack 20) = X[13] ∧
  s (.stack 24) = X[8] ∧
  s (.stack 28) = X[4] ∧
  s (.stack 32) = X[11] ∧
  s (.stack 48) = X[15] ∧
  s (.stack 60) = initial.A ∧
  s (.stack 64) = X[5] ∧
  s (.stack 72) = X[3] ∧
  s (.stack 80) = X[1] ∧
  s (.stack 120) = initial.C ∧
  s (.stack 128) = initial.D ∧
  s (.reg 0) = working.B ∧
  s (.reg 1) = working.A ∧
  s (.reg 2) = working.D ∧
  s (.reg 3) = X[14] ∧
  s (.reg 5) = X[6] ∧
  s (.reg 7) = X[0] ∧
  s (.reg 8) = X[7] ∧
  s (.reg 11) = X[12] ∧
  s (.reg 12) = working.C ∧
  s (.reg 13) = X[2] ∧
  s (.reg 14) = X[10]

def segment44 : List WordInstruction := [
  .mov (.reg 15) (.location (.reg 2)),
  .xor (.reg 15) (.location (.reg 1)),
  .mov (.reg 5) (.location (.stack 56)),
  .add (.reg 0) (.location (.reg 5)),
  .xor (.reg 15) (.location (.reg 12)),
  .add (.reg 0) (.location (.reg 15)),
  .add (.reg 0) (.immediate 0x4881d05),
  .rol (.reg 0) 23,
  .add (.reg 0) (.location (.reg 12))]

theorem segment44_correct (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) (h : Invariant43 initial X working s) :
    Invariant44 initial X (operation H X[6] 0x4881d05 23 working) (executeWords segment44 s) := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    h18, h19, h20, h21, h22, h23⟩
  with_unfolding_all change (s (.stack 4)) = X[9] ∧
    (s (.stack 8)) = initial.B ∧
    (s (.stack 20)) = X[13] ∧
    (s (.stack 24)) = X[8] ∧
    (s (.stack 28)) = X[4] ∧
    (s (.stack 32)) = X[11] ∧
    (s (.stack 48)) = X[15] ∧
    (s (.stack 60)) = initial.A ∧
    (s (.stack 64)) = X[5] ∧
    (s (.stack 72)) = X[3] ∧
    (s (.stack 80)) = X[1] ∧
    (s (.stack 120)) = initial.C ∧
    (s (.stack 128)) = initial.D ∧
    ((((((s (.reg 0)) + (s (.stack 56))) + (((s (.reg 2)) ^^^ (s (.reg 1))) ^^^ (s (.reg 12)))) +
      0x4881d05)).rotateLeft 23 + (s (.reg 12))) = (operation H X[6] 0x4881d05 23 working).B ∧
    (s (.reg 1)) = (operation H X[6] 0x4881d05 23 working).A ∧
    (s (.reg 2)) = (operation H X[6] 0x4881d05 23 working).D ∧
    (s (.reg 3)) = X[14] ∧
    (s (.stack 56)) = X[6] ∧
    (s (.reg 7)) = X[0] ∧
    (s (.reg 8)) = X[7] ∧
    (s (.reg 11)) = X[12] ∧
    (s (.reg 12)) = (operation H X[6] 0x4881d05 23 working).C ∧
    (s (.reg 13)) = X[2] ∧
    (s (.reg 14)) = X[10]
  simp only [operation, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18, h19, h20, h21, h22, h23, true_and, and_true]
  md5_word_arithmetic

def Invariant45 (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) : Prop :=
  s (.stack 4) = X[9] ∧
  s (.stack 8) = initial.B ∧
  s (.stack 20) = X[13] ∧
  s (.stack 24) = X[8] ∧
  s (.stack 28) = X[4] ∧
  s (.stack 32) = X[11] ∧
  s (.stack 48) = X[15] ∧
  s (.stack 60) = initial.A ∧
  s (.stack 64) = X[5] ∧
  s (.stack 72) = X[3] ∧
  s (.stack 80) = X[1] ∧
  s (.stack 120) = initial.C ∧
  s (.stack 128) = initial.D ∧
  s (.reg 0) = working.C ∧
  s (.reg 1) = working.B ∧
  s (.reg 2) = working.A ∧
  s (.reg 3) = X[14] ∧
  s (.reg 5) = X[6] ∧
  s (.reg 7) = X[0] ∧
  s (.reg 8) = X[7] ∧
  s (.reg 11) = X[12] ∧
  s (.reg 12) = working.D ∧
  s (.reg 13) = X[2] ∧
  s (.reg 14) = X[10]

def segment45 : List WordInstruction := [
  .mov (.reg 15) (.location (.reg 12)),
  .xor (.reg 15) (.location (.reg 2)),
  .add (.reg 1) (.location (.stack 4)),
  .xor (.reg 15) (.location (.reg 0)),
  .add (.reg 1) (.location (.reg 15)),
  .add (.reg 1) (.immediate 0xd9d4d039),
  .rol (.reg 1) 4,
  .add (.reg 1) (.location (.reg 0))]

theorem segment45_correct (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) (h : Invariant44 initial X working s) :
    Invariant45 initial X (operation H X[9] 0xd9d4d039 4 working) (executeWords segment45 s) := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    h18, h19, h20, h21, h22, h23⟩
  with_unfolding_all change (s (.stack 4)) = X[9] ∧
    (s (.stack 8)) = initial.B ∧
    (s (.stack 20)) = X[13] ∧
    (s (.stack 24)) = X[8] ∧
    (s (.stack 28)) = X[4] ∧
    (s (.stack 32)) = X[11] ∧
    (s (.stack 48)) = X[15] ∧
    (s (.stack 60)) = initial.A ∧
    (s (.stack 64)) = X[5] ∧
    (s (.stack 72)) = X[3] ∧
    (s (.stack 80)) = X[1] ∧
    (s (.stack 120)) = initial.C ∧
    (s (.stack 128)) = initial.D ∧
    (s (.reg 0)) = (operation H X[9] 0xd9d4d039 4 working).C ∧
    ((((((s (.reg 1)) + (s (.stack 4))) + (((s (.reg 12)) ^^^ (s (.reg 2))) ^^^ (s (.reg 0)))) +
      0xd9d4d039)).rotateLeft 4 + (s (.reg 0))) = (operation H X[9] 0xd9d4d039 4 working).B ∧
    (s (.reg 2)) = (operation H X[9] 0xd9d4d039 4 working).A ∧
    (s (.reg 3)) = X[14] ∧
    (s (.reg 5)) = X[6] ∧
    (s (.reg 7)) = X[0] ∧
    (s (.reg 8)) = X[7] ∧
    (s (.reg 11)) = X[12] ∧
    (s (.reg 12)) = (operation H X[9] 0xd9d4d039 4 working).D ∧
    (s (.reg 13)) = X[2] ∧
    (s (.reg 14)) = X[10]
  simp only [operation, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18, h19, h20, h21, h22, h23, true_and, and_true]
  md5_word_arithmetic

def Invariant46 (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) : Prop :=
  s (.stack 4) = X[9] ∧
  s (.stack 8) = initial.B ∧
  s (.stack 20) = X[13] ∧
  s (.stack 24) = X[8] ∧
  s (.stack 28) = X[4] ∧
  s (.stack 32) = X[11] ∧
  s (.stack 48) = X[15] ∧
  s (.stack 60) = initial.A ∧
  s (.stack 64) = X[5] ∧
  s (.stack 72) = X[3] ∧
  s (.stack 80) = X[1] ∧
  s (.stack 120) = initial.C ∧
  s (.stack 128) = initial.D ∧
  s (.reg 0) = working.D ∧
  s (.reg 1) = working.C ∧
  s (.reg 2) = working.B ∧
  s (.reg 3) = X[14] ∧
  s (.reg 5) = X[6] ∧
  s (.reg 7) = X[0] ∧
  s (.reg 8) = X[7] ∧
  s (.reg 11) = X[12] ∧
  s (.reg 12) = working.A ∧
  s (.reg 13) = X[2] ∧
  s (.reg 14) = X[10]

def segment46 : List WordInstruction := [
  .mov (.reg 15) (.location (.reg 0)),
  .xor (.reg 15) (.location (.reg 12)),
  .add (.reg 2) (.location (.reg 11)),
  .xor (.reg 15) (.location (.reg 1)),
  .add (.reg 2) (.location (.reg 15)),
  .add (.reg 2) (.immediate 0xe6db99e5),
  .rol (.reg 2) 11,
  .add (.reg 2) (.location (.reg 1))]

theorem segment46_correct (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) (h : Invariant45 initial X working s) :
    Invariant46 initial X (operation H X[12] 0xe6db99e5 11 working) (executeWords segment46 s) := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    h18, h19, h20, h21, h22, h23⟩
  with_unfolding_all change (s (.stack 4)) = X[9] ∧
    (s (.stack 8)) = initial.B ∧
    (s (.stack 20)) = X[13] ∧
    (s (.stack 24)) = X[8] ∧
    (s (.stack 28)) = X[4] ∧
    (s (.stack 32)) = X[11] ∧
    (s (.stack 48)) = X[15] ∧
    (s (.stack 60)) = initial.A ∧
    (s (.stack 64)) = X[5] ∧
    (s (.stack 72)) = X[3] ∧
    (s (.stack 80)) = X[1] ∧
    (s (.stack 120)) = initial.C ∧
    (s (.stack 128)) = initial.D ∧
    (s (.reg 0)) = (operation H X[12] 0xe6db99e5 11 working).D ∧
    (s (.reg 1)) = (operation H X[12] 0xe6db99e5 11 working).C ∧
    ((((((s (.reg 2)) + (s (.reg 11))) + (((s (.reg 0)) ^^^ (s (.reg 12))) ^^^ (s (.reg 1)))) +
      0xe6db99e5)).rotateLeft 11 + (s (.reg 1))) = (operation H X[12] 0xe6db99e5 11 working).B ∧
    (s (.reg 3)) = X[14] ∧
    (s (.reg 5)) = X[6] ∧
    (s (.reg 7)) = X[0] ∧
    (s (.reg 8)) = X[7] ∧
    (s (.reg 11)) = X[12] ∧
    (s (.reg 12)) = (operation H X[12] 0xe6db99e5 11 working).A ∧
    (s (.reg 13)) = X[2] ∧
    (s (.reg 14)) = X[10]
  simp only [operation, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18, h19, h20, h21, h22, h23, true_and, and_true]
  md5_word_arithmetic

def Invariant47 (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) : Prop :=
  s (.stack 4) = X[9] ∧
  s (.stack 8) = initial.B ∧
  s (.stack 20) = X[13] ∧
  s (.stack 24) = X[8] ∧
  s (.stack 28) = X[4] ∧
  s (.stack 32) = X[11] ∧
  s (.stack 60) = initial.A ∧
  s (.stack 64) = X[5] ∧
  s (.stack 72) = X[3] ∧
  s (.stack 80) = X[1] ∧
  s (.stack 120) = initial.C ∧
  s (.stack 128) = initial.D ∧
  s (.reg 0) = working.A ∧
  s (.reg 1) = working.D ∧
  s (.reg 2) = working.C ∧
  s (.reg 3) = X[14] ∧
  s (.reg 5) = X[6] ∧
  s (.reg 7) = X[0] ∧
  s (.reg 8) = X[7] ∧
  s (.reg 10) = X[15] ∧
  s (.reg 11) = X[12] ∧
  s (.reg 12) = working.B ∧
  s (.reg 13) = X[2] ∧
  s (.reg 14) = X[10]

def segment47 : List WordInstruction := [
  .mov (.reg 15) (.location (.reg 1)),
  .xor (.reg 15) (.location (.reg 0)),
  .mov (.reg 10) (.location (.stack 48)),
  .add (.reg 12) (.location (.reg 10)),
  .xor (.reg 15) (.location (.reg 2)),
  .add (.reg 12) (.location (.reg 15)),
  .add (.reg 12) (.immediate 0x1fa27cf8),
  .rol (.reg 12) 16,
  .add (.reg 12) (.location (.reg 2))]

theorem segment47_correct (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) (h : Invariant46 initial X working s) :
    Invariant47 initial X (operation H X[15] 0x1fa27cf8 16 working) (executeWords segment47 s) := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    h18, h19, h20, h21, h22, h23⟩
  with_unfolding_all change (s (.stack 4)) = X[9] ∧
    (s (.stack 8)) = initial.B ∧
    (s (.stack 20)) = X[13] ∧
    (s (.stack 24)) = X[8] ∧
    (s (.stack 28)) = X[4] ∧
    (s (.stack 32)) = X[11] ∧
    (s (.stack 60)) = initial.A ∧
    (s (.stack 64)) = X[5] ∧
    (s (.stack 72)) = X[3] ∧
    (s (.stack 80)) = X[1] ∧
    (s (.stack 120)) = initial.C ∧
    (s (.stack 128)) = initial.D ∧
    (s (.reg 0)) = (operation H X[15] 0x1fa27cf8 16 working).A ∧
    (s (.reg 1)) = (operation H X[15] 0x1fa27cf8 16 working).D ∧
    (s (.reg 2)) = (operation H X[15] 0x1fa27cf8 16 working).C ∧
    (s (.reg 3)) = X[14] ∧
    (s (.reg 5)) = X[6] ∧
    (s (.reg 7)) = X[0] ∧
    (s (.reg 8)) = X[7] ∧
    (s (.stack 48)) = X[15] ∧
    (s (.reg 11)) = X[12] ∧
    ((((((s (.reg 12)) + (s (.stack 48))) + (((s (.reg 1)) ^^^ (s (.reg 0))) ^^^ (s (.reg 2)))) +
      0x1fa27cf8)).rotateLeft 16 + (s (.reg 2))) = (operation H X[15] 0x1fa27cf8 16 working).B ∧
    (s (.reg 13)) = X[2] ∧
    (s (.reg 14)) = X[10]
  simp only [operation, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18, h19, h20, h21, h22, h23, true_and, and_true]
  md5_word_arithmetic

def Invariant48 (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) : Prop :=
  s (.stack 4) = X[9] ∧
  s (.stack 8) = initial.B ∧
  s (.stack 20) = X[13] ∧
  s (.stack 24) = X[8] ∧
  s (.stack 28) = X[4] ∧
  s (.stack 32) = X[11] ∧
  s (.stack 60) = initial.A ∧
  s (.stack 64) = X[5] ∧
  s (.stack 72) = X[3] ∧
  s (.stack 80) = X[1] ∧
  s (.stack 120) = initial.C ∧
  s (.stack 128) = initial.D ∧
  s (.reg 0) = working.B ∧
  s (.reg 1) = (working.A + X[0]) ∧
  s (.reg 2) = working.D ∧
  s (.reg 3) = X[14] ∧
  s (.reg 5) = X[6] ∧
  s (.reg 8) = X[7] ∧
  s (.reg 10) = X[15] ∧
  s (.reg 11) = X[12] ∧
  s (.reg 12) = working.C ∧
  s (.reg 13) = X[2] ∧
  s (.reg 14) = X[10]

def segment48 : List WordInstruction := [
  .mov (.reg 15) (.location (.reg 2)),
  .xor (.reg 15) (.location (.reg 1)),
  .add (.reg 0) (.location (.reg 13)),
  .xor (.reg 15) (.location (.reg 12)),
  .add (.reg 0) (.location (.reg 15)),
  .add (.reg 0) (.immediate 0xc4ac5665),
  .add (.reg 1) (.location (.reg 7)),
  .rol (.reg 0) 23,
  .add (.reg 0) (.location (.reg 12))]

theorem segment48_correct (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) (h : Invariant47 initial X working s) :
    Invariant48 initial X (operation H X[2] 0xc4ac5665 23 working) (executeWords segment48 s) := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    h18, h19, h20, h21, h22, h23⟩
  with_unfolding_all change (s (.stack 4)) = X[9] ∧
    (s (.stack 8)) = initial.B ∧
    (s (.stack 20)) = X[13] ∧
    (s (.stack 24)) = X[8] ∧
    (s (.stack 28)) = X[4] ∧
    (s (.stack 32)) = X[11] ∧
    (s (.stack 60)) = initial.A ∧
    (s (.stack 64)) = X[5] ∧
    (s (.stack 72)) = X[3] ∧
    (s (.stack 80)) = X[1] ∧
    (s (.stack 120)) = initial.C ∧
    (s (.stack 128)) = initial.D ∧
    ((((((s (.reg 0)) + (s (.reg 13))) + (((s (.reg 2)) ^^^ (s (.reg 1))) ^^^ (s (.reg 12)))) +
      0xc4ac5665)).rotateLeft 23 + (s (.reg 12))) = (operation H X[2] 0xc4ac5665 23 working).B ∧
    ((s (.reg 1)) + (s (.reg 7))) = ((operation H X[2] 0xc4ac5665 23 working).A + X[0]) ∧
    (s (.reg 2)) = (operation H X[2] 0xc4ac5665 23 working).D ∧
    (s (.reg 3)) = X[14] ∧
    (s (.reg 5)) = X[6] ∧
    (s (.reg 8)) = X[7] ∧
    (s (.reg 10)) = X[15] ∧
    (s (.reg 11)) = X[12] ∧
    (s (.reg 12)) = (operation H X[2] 0xc4ac5665 23 working).C ∧
    (s (.reg 13)) = X[2] ∧
    (s (.reg 14)) = X[10]
  simp only [operation, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18, h19, h20, h21, h22, h23, true_and, and_true]
  md5_word_arithmetic

end Md5.Proofs.Block.Rounds
