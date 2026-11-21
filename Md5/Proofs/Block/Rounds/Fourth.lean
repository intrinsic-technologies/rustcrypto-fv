import Md5.Proofs.Block.Rounds.Third

namespace Md5.Proofs.Block.Rounds

open Standards.RFC.MD5

def Invariant49 (initial : Buffer) (X : Vector (BitVec 32) 16)
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
  s (.reg 0) = working.C ∧
  s (.reg 1) = working.B ∧
  s (.reg 2) = (working.A + X[7]) ∧
  s (.reg 3) = X[14] ∧
  s (.reg 5) = X[6] ∧
  s (.reg 9) = (~~~working.D) ∧
  s (.reg 10) = X[15] ∧
  s (.reg 11) = X[12] ∧
  s (.reg 12) = working.D ∧
  s (.reg 13) = X[2] ∧
  s (.reg 14) = X[10]

def segment49 : List WordInstruction := [
  .mov (.reg 15) (.location (.reg 2)),
  .not (.reg 15),
  .or (.reg 15) (.location (.reg 0)),
  .xor (.reg 15) (.location (.reg 12)),
  .add (.reg 1) (.location (.reg 15)),
  .add (.reg 1) (.immediate 0xf4292244),
  .rol (.reg 1) 6,
  .add (.reg 2) (.location (.reg 8)),
  .mov (.reg 9) (.location (.reg 12)),
  .not (.reg 9),
  .add (.reg 1) (.location (.reg 0))]

theorem segment49_correct (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) (h : Invariant48 initial X working s) :
    Invariant49 initial X (operation I X[0] 0xf4292244 6 working) (executeWords segment49 s) := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    h18, h19, h20, h21, h22⟩
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
    (s (.reg 0)) = (operation I X[0] 0xf4292244 6 working).C ∧
    (((((s (.reg 1)) + (((~~~(s (.reg 2))) ||| (s (.reg 0))) ^^^ (s (.reg 12)))) +
      0xf4292244)).rotateLeft 6 + (s (.reg 0))) = (operation I X[0] 0xf4292244 6 working).B ∧
    ((s (.reg 2)) + (s (.reg 8))) = ((operation I X[0] 0xf4292244 6 working).A + X[7]) ∧
    (s (.reg 3)) = X[14] ∧
    (s (.reg 5)) = X[6] ∧
    (~~~(s (.reg 12))) = (~~~(operation I X[0] 0xf4292244 6 working).D) ∧
    (s (.reg 10)) = X[15] ∧
    (s (.reg 11)) = X[12] ∧
    (s (.reg 12)) = (operation I X[0] 0xf4292244 6 working).D ∧
    (s (.reg 13)) = X[2] ∧
    (s (.reg 14)) = X[10]
  simp only [operation, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18, h19, h20, h21, h22, true_and, and_true]
  md5_word_arithmetic

def Invariant50 (initial : Buffer) (X : Vector (BitVec 32) 16)
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
  s (.reg 0) = working.D ∧
  s (.reg 1) = working.C ∧
  s (.reg 2) = working.B ∧
  s (.reg 5) = X[6] ∧
  s (.reg 10) = X[15] ∧
  s (.reg 11) = X[12] ∧
  s (.reg 12) = (working.A + X[14]) ∧
  s (.reg 13) = X[2] ∧
  s (.reg 14) = X[10]

def segment50 : List WordInstruction := [
  .or (.reg 9) (.location (.reg 1)),
  .xor (.reg 9) (.location (.reg 0)),
  .add (.reg 2) (.location (.reg 9)),
  .add (.reg 2) (.immediate 0x432aff97),
  .add (.reg 12) (.location (.reg 3)),
  .rol (.reg 2) 10,
  .add (.reg 2) (.location (.reg 1))]

theorem segment50_correct (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) (h : Invariant49 initial X working s) :
    Invariant50 initial X (operation I X[7] 0x432aff97 10 working) (executeWords segment50 s) := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    h18, h19, h20, h21, h22⟩
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
    (s (.reg 0)) = (operation I X[7] 0x432aff97 10 working).D ∧
    (s (.reg 1)) = (operation I X[7] 0x432aff97 10 working).C ∧
    (((((s (.reg 2)) + (((s (.reg 9)) ||| (s (.reg 1))) ^^^ (s (.reg 0)))) + 0x432aff97)).rotateLeft
      10 + (s (.reg 1))) = (operation I X[7] 0x432aff97 10 working).B ∧
    (s (.reg 5)) = X[6] ∧
    (s (.reg 10)) = X[15] ∧
    (s (.reg 11)) = X[12] ∧
    ((s (.reg 12)) + (s (.reg 3))) = ((operation I X[7] 0x432aff97 10 working).A + X[14]) ∧
    (s (.reg 13)) = X[2] ∧
    (s (.reg 14)) = X[10]
  simp only [operation, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18, h19, h20, h21, h22, true_and, and_true]
  md5_word_arithmetic

def Invariant51 (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) : Prop :=
  s (.stack 4) = X[9] ∧
  s (.stack 8) = initial.B ∧
  s (.stack 20) = X[13] ∧
  s (.stack 24) = X[8] ∧
  s (.stack 28) = X[4] ∧
  s (.stack 32) = X[11] ∧
  s (.stack 60) = initial.A ∧
  s (.stack 72) = X[3] ∧
  s (.stack 80) = X[1] ∧
  s (.stack 120) = initial.C ∧
  s (.stack 128) = initial.D ∧
  s (.reg 0) = (working.A + X[5]) ∧
  s (.reg 1) = working.D ∧
  s (.reg 2) = working.C ∧
  s (.reg 5) = X[6] ∧
  s (.reg 7) = working.B ∧
  s (.reg 10) = X[15] ∧
  s (.reg 11) = X[12] ∧
  s (.reg 13) = X[2] ∧
  s (.reg 14) = X[10]

def segment51 : List WordInstruction := [
  .mov (.reg 7) (.location (.reg 0)),
  .not (.reg 7),
  .or (.reg 7) (.location (.reg 2)),
  .xor (.reg 7) (.location (.reg 1)),
  .add (.reg 7) (.location (.reg 12)),
  .add (.reg 7) (.immediate 0xab9423a7),
  .add (.reg 0) (.location (.stack 64)),
  .rol (.reg 7) 15,
  .add (.reg 7) (.location (.reg 2))]

theorem segment51_correct (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) (h : Invariant50 initial X working s) :
    Invariant51 initial X (operation I X[14] 0xab9423a7 15 working) (executeWords segment51 s) := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    h18, h19, h20⟩
  with_unfolding_all change (s (.stack 4)) = X[9] ∧
    (s (.stack 8)) = initial.B ∧
    (s (.stack 20)) = X[13] ∧
    (s (.stack 24)) = X[8] ∧
    (s (.stack 28)) = X[4] ∧
    (s (.stack 32)) = X[11] ∧
    (s (.stack 60)) = initial.A ∧
    (s (.stack 72)) = X[3] ∧
    (s (.stack 80)) = X[1] ∧
    (s (.stack 120)) = initial.C ∧
    (s (.stack 128)) = initial.D ∧
    ((s (.reg 0)) + (s (.stack 64))) = ((operation I X[14] 0xab9423a7 15 working).A + X[5]) ∧
    (s (.reg 1)) = (operation I X[14] 0xab9423a7 15 working).D ∧
    (s (.reg 2)) = (operation I X[14] 0xab9423a7 15 working).C ∧
    (s (.reg 5)) = X[6] ∧
    (((((((~~~(s (.reg 0))) ||| (s (.reg 2))) ^^^ (s (.reg 1))) + (s (.reg 12))) +
      0xab9423a7)).rotateLeft 15 + (s (.reg 2))) = (operation I X[14] 0xab9423a7 15 working).B ∧
    (s (.reg 10)) = X[15] ∧
    (s (.reg 11)) = X[12] ∧
    (s (.reg 13)) = X[2] ∧
    (s (.reg 14)) = X[10]
  simp only [operation, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18, h19, h20, true_and, and_true]
  md5_word_arithmetic

def Invariant52 (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) : Prop :=
  s (.stack 4) = X[9] ∧
  s (.stack 8) = initial.B ∧
  s (.stack 20) = X[13] ∧
  s (.stack 24) = X[8] ∧
  s (.stack 28) = X[4] ∧
  s (.stack 32) = X[11] ∧
  s (.stack 60) = initial.A ∧
  s (.stack 72) = X[3] ∧
  s (.stack 80) = X[1] ∧
  s (.stack 120) = initial.C ∧
  s (.stack 128) = initial.D ∧
  s (.reg 0) = working.B ∧
  s (.reg 1) = (working.A + X[12]) ∧
  s (.reg 2) = working.D ∧
  s (.reg 5) = X[6] ∧
  s (.reg 7) = working.C ∧
  s (.reg 10) = X[15] ∧
  s (.reg 13) = X[2] ∧
  s (.reg 14) = X[10]

def segment52 : List WordInstruction := [
  .mov (.reg 9) (.location (.reg 1)),
  .not (.reg 9),
  .or (.reg 9) (.location (.reg 7)),
  .xor (.reg 9) (.location (.reg 2)),
  .add (.reg 0) (.location (.reg 9)),
  .add (.reg 0) (.immediate 0xfc93a039),
  .add (.reg 1) (.location (.reg 11)),
  .rol (.reg 0) 21,
  .add (.reg 0) (.location (.reg 7))]

theorem segment52_correct (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) (h : Invariant51 initial X working s) :
    Invariant52 initial X (operation I X[5] 0xfc93a039 21 working) (executeWords segment52 s) := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    h18, h19⟩
  with_unfolding_all change (s (.stack 4)) = X[9] ∧
    (s (.stack 8)) = initial.B ∧
    (s (.stack 20)) = X[13] ∧
    (s (.stack 24)) = X[8] ∧
    (s (.stack 28)) = X[4] ∧
    (s (.stack 32)) = X[11] ∧
    (s (.stack 60)) = initial.A ∧
    (s (.stack 72)) = X[3] ∧
    (s (.stack 80)) = X[1] ∧
    (s (.stack 120)) = initial.C ∧
    (s (.stack 128)) = initial.D ∧
    (((((s (.reg 0)) + (((~~~(s (.reg 1))) ||| (s (.reg 7))) ^^^ (s (.reg 2)))) +
      0xfc93a039)).rotateLeft 21 + (s (.reg 7))) = (operation I X[5] 0xfc93a039 21 working).B ∧
    ((s (.reg 1)) + (s (.reg 11))) = ((operation I X[5] 0xfc93a039 21 working).A + X[12]) ∧
    (s (.reg 2)) = (operation I X[5] 0xfc93a039 21 working).D ∧
    (s (.reg 5)) = X[6] ∧
    (s (.reg 7)) = (operation I X[5] 0xfc93a039 21 working).C ∧
    (s (.reg 10)) = X[15] ∧
    (s (.reg 13)) = X[2] ∧
    (s (.reg 14)) = X[10]
  simp only [operation, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18, h19, true_and, and_true]
  md5_word_arithmetic

def Invariant53 (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) : Prop :=
  s (.stack 4) = X[9] ∧
  s (.stack 8) = initial.B ∧
  s (.stack 20) = X[13] ∧
  s (.stack 24) = X[8] ∧
  s (.stack 28) = X[4] ∧
  s (.stack 32) = X[11] ∧
  s (.stack 60) = initial.A ∧
  s (.stack 80) = X[1] ∧
  s (.stack 120) = initial.C ∧
  s (.stack 128) = initial.D ∧
  s (.reg 0) = working.C ∧
  s (.reg 1) = working.B ∧
  s (.reg 2) = (working.A + X[3]) ∧
  s (.reg 5) = X[6] ∧
  s (.reg 7) = working.D ∧
  s (.reg 8) = (~~~working.D) ∧
  s (.reg 10) = X[15] ∧
  s (.reg 13) = X[2] ∧
  s (.reg 14) = X[10]

def segment53 : List WordInstruction := [
  .mov (.reg 8) (.location (.reg 2)),
  .not (.reg 8),
  .or (.reg 8) (.location (.reg 0)),
  .xor (.reg 8) (.location (.reg 7)),
  .add (.reg 1) (.location (.reg 8)),
  .add (.reg 1) (.immediate 0x655b59c3),
  .rol (.reg 1) 6,
  .add (.reg 2) (.location (.stack 72)),
  .mov (.reg 8) (.location (.reg 7)),
  .not (.reg 8),
  .add (.reg 1) (.location (.reg 0))]

theorem segment53_correct (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) (h : Invariant52 initial X working s) :
    Invariant53 initial X (operation I X[12] 0x655b59c3 6 working) (executeWords segment53 s) := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    h18⟩
  with_unfolding_all change (s (.stack 4)) = X[9] ∧
    (s (.stack 8)) = initial.B ∧
    (s (.stack 20)) = X[13] ∧
    (s (.stack 24)) = X[8] ∧
    (s (.stack 28)) = X[4] ∧
    (s (.stack 32)) = X[11] ∧
    (s (.stack 60)) = initial.A ∧
    (s (.stack 80)) = X[1] ∧
    (s (.stack 120)) = initial.C ∧
    (s (.stack 128)) = initial.D ∧
    (s (.reg 0)) = (operation I X[12] 0x655b59c3 6 working).C ∧
    (((((s (.reg 1)) + (((~~~(s (.reg 2))) ||| (s (.reg 0))) ^^^ (s (.reg 7)))) +
      0x655b59c3)).rotateLeft 6 + (s (.reg 0))) = (operation I X[12] 0x655b59c3 6 working).B ∧
    ((s (.reg 2)) + (s (.stack 72))) = ((operation I X[12] 0x655b59c3 6 working).A + X[3]) ∧
    (s (.reg 5)) = X[6] ∧
    (s (.reg 7)) = (operation I X[12] 0x655b59c3 6 working).D ∧
    (~~~(s (.reg 7))) = (~~~(operation I X[12] 0x655b59c3 6 working).D) ∧
    (s (.reg 10)) = X[15] ∧
    (s (.reg 13)) = X[2] ∧
    (s (.reg 14)) = X[10]
  simp only [operation, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18, true_and, and_true]
  md5_word_arithmetic

def Invariant54 (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) : Prop :=
  s (.stack 4) = X[9] ∧
  s (.stack 8) = initial.B ∧
  s (.stack 20) = X[13] ∧
  s (.stack 24) = X[8] ∧
  s (.stack 28) = X[4] ∧
  s (.stack 32) = X[11] ∧
  s (.stack 60) = initial.A ∧
  s (.stack 80) = X[1] ∧
  s (.stack 120) = initial.C ∧
  s (.stack 128) = initial.D ∧
  s (.reg 0) = working.D ∧
  s (.reg 1) = working.C ∧
  s (.reg 2) = working.B ∧
  s (.reg 5) = X[6] ∧
  s (.reg 7) = (working.A + X[10]) ∧
  s (.reg 10) = X[15] ∧
  s (.reg 13) = X[2]

def segment54 : List WordInstruction := [
  .or (.reg 8) (.location (.reg 1)),
  .xor (.reg 8) (.location (.reg 0)),
  .add (.reg 2) (.location (.reg 8)),
  .add (.reg 2) (.immediate 0x8f0ccc92),
  .add (.reg 7) (.location (.reg 14)),
  .rol (.reg 2) 10,
  .add (.reg 2) (.location (.reg 1))]

theorem segment54_correct (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) (h : Invariant53 initial X working s) :
    Invariant54 initial X (operation I X[3] 0x8f0ccc92 10 working) (executeWords segment54 s) := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    h18⟩
  with_unfolding_all change (s (.stack 4)) = X[9] ∧
    (s (.stack 8)) = initial.B ∧
    (s (.stack 20)) = X[13] ∧
    (s (.stack 24)) = X[8] ∧
    (s (.stack 28)) = X[4] ∧
    (s (.stack 32)) = X[11] ∧
    (s (.stack 60)) = initial.A ∧
    (s (.stack 80)) = X[1] ∧
    (s (.stack 120)) = initial.C ∧
    (s (.stack 128)) = initial.D ∧
    (s (.reg 0)) = (operation I X[3] 0x8f0ccc92 10 working).D ∧
    (s (.reg 1)) = (operation I X[3] 0x8f0ccc92 10 working).C ∧
    (((((s (.reg 2)) + (((s (.reg 8)) ||| (s (.reg 1))) ^^^ (s (.reg 0)))) + 0x8f0ccc92)).rotateLeft
      10 + (s (.reg 1))) = (operation I X[3] 0x8f0ccc92 10 working).B ∧
    (s (.reg 5)) = X[6] ∧
    ((s (.reg 7)) + (s (.reg 14))) = ((operation I X[3] 0x8f0ccc92 10 working).A + X[10]) ∧
    (s (.reg 10)) = X[15] ∧
    (s (.reg 13)) = X[2]
  simp only [operation, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18, true_and, and_true]
  md5_word_arithmetic

def Invariant55 (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) : Prop :=
  s (.stack 4) = X[9] ∧
  s (.stack 8) = initial.B ∧
  s (.stack 20) = X[13] ∧
  s (.stack 24) = X[8] ∧
  s (.stack 28) = X[4] ∧
  s (.stack 32) = X[11] ∧
  s (.stack 60) = initial.A ∧
  s (.stack 120) = initial.C ∧
  s (.stack 128) = initial.D ∧
  s (.reg 0) = (working.A + X[1]) ∧
  s (.reg 1) = working.D ∧
  s (.reg 2) = working.C ∧
  s (.reg 5) = X[6] ∧
  s (.reg 7) = working.B ∧
  s (.reg 10) = X[15] ∧
  s (.reg 13) = X[2]

def segment55 : List WordInstruction := [
  .mov (.reg 8) (.location (.reg 0)),
  .not (.reg 8),
  .or (.reg 8) (.location (.reg 2)),
  .xor (.reg 8) (.location (.reg 1)),
  .add (.reg 7) (.location (.reg 8)),
  .add (.reg 7) (.immediate 0xffeff47d),
  .add (.reg 0) (.location (.stack 80)),
  .rol (.reg 7) 15,
  .add (.reg 7) (.location (.reg 2))]

theorem segment55_correct (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) (h : Invariant54 initial X working s) :
    Invariant55 initial X (operation I X[10] 0xffeff47d 15 working) (executeWords segment55 s) := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩
  with_unfolding_all change (s (.stack 4)) = X[9] ∧
    (s (.stack 8)) = initial.B ∧
    (s (.stack 20)) = X[13] ∧
    (s (.stack 24)) = X[8] ∧
    (s (.stack 28)) = X[4] ∧
    (s (.stack 32)) = X[11] ∧
    (s (.stack 60)) = initial.A ∧
    (s (.stack 120)) = initial.C ∧
    (s (.stack 128)) = initial.D ∧
    ((s (.reg 0)) + (s (.stack 80))) = ((operation I X[10] 0xffeff47d 15 working).A + X[1]) ∧
    (s (.reg 1)) = (operation I X[10] 0xffeff47d 15 working).D ∧
    (s (.reg 2)) = (operation I X[10] 0xffeff47d 15 working).C ∧
    (s (.reg 5)) = X[6] ∧
    (((((s (.reg 7)) + (((~~~(s (.reg 0))) ||| (s (.reg 2))) ^^^ (s (.reg 1)))) +
      0xffeff47d)).rotateLeft 15 + (s (.reg 2))) = (operation I X[10] 0xffeff47d 15 working).B ∧
    (s (.reg 10)) = X[15] ∧
    (s (.reg 13)) = X[2]
  simp only [operation, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    true_and, and_true]
  md5_word_arithmetic

def Invariant56 (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) : Prop :=
  s (.stack 4) = X[9] ∧
  s (.stack 8) = initial.B ∧
  s (.stack 20) = X[13] ∧
  s (.stack 24) = X[8] ∧
  s (.stack 28) = X[4] ∧
  s (.stack 32) = X[11] ∧
  s (.stack 60) = initial.A ∧
  s (.stack 120) = initial.C ∧
  s (.stack 128) = initial.D ∧
  s (.reg 1) = working.A ∧
  s (.reg 2) = working.D ∧
  s (.reg 5) = X[6] ∧
  s (.reg 7) = working.C ∧
  s (.reg 8) = working.B ∧
  s (.reg 10) = X[15] ∧
  s (.reg 13) = X[2]

def segment56 : List WordInstruction := [
  .mov (.reg 8) (.location (.reg 1)),
  .not (.reg 8),
  .or (.reg 8) (.location (.reg 7)),
  .xor (.reg 8) (.location (.reg 2)),
  .add (.reg 8) (.location (.reg 0)),
  .add (.reg 8) (.immediate 0x85845dd1),
  .rol (.reg 8) 21,
  .add (.reg 8) (.location (.reg 7))]

theorem segment56_correct (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) (h : Invariant55 initial X working s) :
    Invariant56 initial X (operation I X[1] 0x85845dd1 21 working) (executeWords segment56 s) := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
  with_unfolding_all change (s (.stack 4)) = X[9] ∧
    (s (.stack 8)) = initial.B ∧
    (s (.stack 20)) = X[13] ∧
    (s (.stack 24)) = X[8] ∧
    (s (.stack 28)) = X[4] ∧
    (s (.stack 32)) = X[11] ∧
    (s (.stack 60)) = initial.A ∧
    (s (.stack 120)) = initial.C ∧
    (s (.stack 128)) = initial.D ∧
    (s (.reg 1)) = (operation I X[1] 0x85845dd1 21 working).A ∧
    (s (.reg 2)) = (operation I X[1] 0x85845dd1 21 working).D ∧
    (s (.reg 5)) = X[6] ∧
    (s (.reg 7)) = (operation I X[1] 0x85845dd1 21 working).C ∧
    (((((((~~~(s (.reg 1))) ||| (s (.reg 7))) ^^^ (s (.reg 2))) + (s (.reg 0))) +
      0x85845dd1)).rotateLeft 21 + (s (.reg 7))) = (operation I X[1] 0x85845dd1 21 working).B ∧
    (s (.reg 10)) = X[15] ∧
    (s (.reg 13)) = X[2]
  simp only [operation, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
    true_and, and_true]
  md5_word_arithmetic

def Invariant57 (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) : Prop :=
  s (.stack 4) = X[9] ∧
  s (.stack 8) = initial.B ∧
  s (.stack 20) = X[13] ∧
  s (.stack 28) = X[4] ∧
  s (.stack 32) = X[11] ∧
  s (.stack 60) = initial.A ∧
  s (.stack 120) = initial.C ∧
  s (.stack 128) = initial.D ∧
  s (.reg 0) = working.B ∧
  s (.reg 1) = working.D ∧
  s (.reg 2) = (working.A + X[15]) ∧
  s (.reg 5) = X[6] ∧
  s (.reg 7) = working.D ∧
  s (.reg 8) = working.C ∧
  s (.reg 13) = X[2]

def segment57 : List WordInstruction := [
  .add (.reg 1) (.location (.stack 24)),
  .mov (.reg 0) (.location (.reg 2)),
  .not (.reg 0),
  .or (.reg 0) (.location (.reg 8)),
  .xor (.reg 0) (.location (.reg 7)),
  .add (.reg 0) (.location (.reg 1)),
  .add (.reg 0) (.immediate 0x6fa87e4f),
  .rol (.reg 0) 6,
  .add (.reg 2) (.location (.reg 10)),
  .mov (.reg 1) (.location (.reg 7)),
  .add (.reg 0) (.location (.reg 8))]

theorem segment57_correct (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) (h : Invariant56 initial X working s) :
    Invariant57 initial X (operation I X[8] 0x6fa87e4f 6 working) (executeWords segment57 s) := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
  with_unfolding_all change (s (.stack 4)) = X[9] ∧
    (s (.stack 8)) = initial.B ∧
    (s (.stack 20)) = X[13] ∧
    (s (.stack 28)) = X[4] ∧
    (s (.stack 32)) = X[11] ∧
    (s (.stack 60)) = initial.A ∧
    (s (.stack 120)) = initial.C ∧
    (s (.stack 128)) = initial.D ∧
    (((((((~~~(s (.reg 2))) ||| (s (.reg 8))) ^^^ (s (.reg 7))) + ((s (.reg 1)) + (s (.stack 24))))
      + 0x6fa87e4f)).rotateLeft 6 + (s (.reg 8))) = (operation I X[8] 0x6fa87e4f 6 working).B ∧
    (s (.reg 7)) = (operation I X[8] 0x6fa87e4f 6 working).D ∧
    ((s (.reg 2)) + (s (.reg 10))) = ((operation I X[8] 0x6fa87e4f 6 working).A + X[15]) ∧
    (s (.reg 5)) = X[6] ∧
    (s (.reg 7)) = (operation I X[8] 0x6fa87e4f 6 working).D ∧
    (s (.reg 8)) = (operation I X[8] 0x6fa87e4f 6 working).C ∧
    (s (.reg 13)) = X[2]
  simp only [operation, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
    true_and, and_true]
  md5_word_arithmetic

def Invariant58 (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) : Prop :=
  s (.stack 4) = X[9] ∧
  s (.stack 8) = initial.B ∧
  s (.stack 20) = X[13] ∧
  s (.stack 28) = X[4] ∧
  s (.stack 32) = X[11] ∧
  s (.stack 60) = initial.A ∧
  s (.stack 120) = initial.C ∧
  s (.stack 128) = initial.D ∧
  s (.reg 0) = working.C ∧
  s (.reg 2) = working.B ∧
  s (.reg 7) = (working.A + X[6]) ∧
  s (.reg 8) = working.D ∧
  s (.reg 13) = X[2]

def segment58 : List WordInstruction := [
  .not (.reg 1),
  .or (.reg 1) (.location (.reg 0)),
  .xor (.reg 1) (.location (.reg 8)),
  .add (.reg 2) (.location (.reg 1)),
  .add (.reg 2) (.immediate 0xfe2ce6e0),
  .rol (.reg 2) 10,
  .add (.reg 7) (.location (.reg 5)),
  .add (.reg 2) (.location (.reg 0))]

theorem segment58_correct (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) (h : Invariant57 initial X working s) :
    Invariant58 initial X (operation I X[15] 0xfe2ce6e0 10 working) (executeWords segment58 s) := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
  with_unfolding_all change (s (.stack 4)) = X[9] ∧
    (s (.stack 8)) = initial.B ∧
    (s (.stack 20)) = X[13] ∧
    (s (.stack 28)) = X[4] ∧
    (s (.stack 32)) = X[11] ∧
    (s (.stack 60)) = initial.A ∧
    (s (.stack 120)) = initial.C ∧
    (s (.stack 128)) = initial.D ∧
    (s (.reg 0)) = (operation I X[15] 0xfe2ce6e0 10 working).C ∧
    (((((s (.reg 2)) + (((~~~(s (.reg 1))) ||| (s (.reg 0))) ^^^ (s (.reg 8)))) +
      0xfe2ce6e0)).rotateLeft 10 + (s (.reg 0))) = (operation I X[15] 0xfe2ce6e0 10 working).B ∧
    ((s (.reg 7)) + (s (.reg 5))) = ((operation I X[15] 0xfe2ce6e0 10 working).A + X[6]) ∧
    (s (.reg 8)) = (operation I X[15] 0xfe2ce6e0 10 working).D ∧
    (s (.reg 13)) = X[2]
  simp only [operation, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, true_and,
    and_true]
  md5_word_arithmetic

def Invariant59 (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) : Prop :=
  s (.stack 4) = X[9] ∧
  s (.stack 8) = initial.B ∧
  s (.stack 20) = X[13] ∧
  s (.stack 28) = X[4] ∧
  s (.stack 32) = X[11] ∧
  s (.stack 60) = initial.A ∧
  s (.stack 120) = initial.C ∧
  s (.stack 128) = initial.D ∧
  s (.reg 0) = working.D ∧
  s (.reg 2) = working.C ∧
  s (.reg 8) = working.A ∧
  s (.reg 9) = working.B ∧
  s (.reg 13) = X[2]

def segment59 : List WordInstruction := [
  .mov (.reg 1) (.location (.reg 8)),
  .not (.reg 1),
  .or (.reg 1) (.location (.reg 2)),
  .xor (.reg 1) (.location (.reg 0)),
  .lea (.reg 9) (.reg 1) (.reg 7),
  .add (.reg 9) (.immediate 0xa3014314),
  .rol (.reg 9) 15,
  .add (.reg 9) (.location (.reg 2))]

theorem segment59_correct (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) (h : Invariant58 initial X working s) :
    Invariant59 initial X (operation I X[6] 0xa3014314 15 working) (executeWords segment59 s) := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
  with_unfolding_all change (s (.stack 4)) = X[9] ∧
    (s (.stack 8)) = initial.B ∧
    (s (.stack 20)) = X[13] ∧
    (s (.stack 28)) = X[4] ∧
    (s (.stack 32)) = X[11] ∧
    (s (.stack 60)) = initial.A ∧
    (s (.stack 120)) = initial.C ∧
    (s (.stack 128)) = initial.D ∧
    (s (.reg 0)) = (operation I X[6] 0xa3014314 15 working).D ∧
    (s (.reg 2)) = (operation I X[6] 0xa3014314 15 working).C ∧
    (s (.reg 8)) = (operation I X[6] 0xa3014314 15 working).A ∧
    (((((((~~~(s (.reg 8))) ||| (s (.reg 2))) ^^^ (s (.reg 0))) + (s (.reg 7))) +
      0xa3014314)).rotateLeft 15 + (s (.reg 2))) = (operation I X[6] 0xa3014314 15 working).B ∧
    (s (.reg 13)) = X[2]
  simp only [operation, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, true_and, and_true]
  md5_word_arithmetic

def Invariant60 (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) : Prop :=
  s (.stack 4) = X[9] ∧
  s (.stack 8) = initial.B ∧
  s (.stack 32) = X[11] ∧
  s (.stack 60) = initial.A ∧
  s (.stack 120) = initial.C ∧
  s (.stack 128) = initial.D ∧
  s (.reg 0) = (working.A + X[4]) ∧
  s (.reg 1) = working.D ∧
  s (.reg 2) = working.D ∧
  s (.reg 7) = working.B ∧
  s (.reg 9) = working.C ∧
  s (.reg 13) = X[2]

def segment60 : List WordInstruction := [
  .add (.reg 8) (.location (.stack 20)),
  .mov (.reg 1) (.location (.reg 0)),
  .not (.reg 1),
  .or (.reg 1) (.location (.reg 9)),
  .xor (.reg 1) (.location (.reg 2)),
  .lea (.reg 7) (.reg 1) (.reg 8),
  .add (.reg 7) (.immediate 0x4e0811a1),
  .rol (.reg 7) 21,
  .add (.reg 0) (.location (.stack 28)),
  .mov (.reg 1) (.location (.reg 2)),
  .add (.reg 7) (.location (.reg 9))]

theorem segment60_correct (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) (h : Invariant59 initial X working s) :
    Invariant60 initial X (operation I X[13] 0x4e0811a1 21 working) (executeWords segment60 s) := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
  with_unfolding_all change (s (.stack 4)) = X[9] ∧
    (s (.stack 8)) = initial.B ∧
    (s (.stack 32)) = X[11] ∧
    (s (.stack 60)) = initial.A ∧
    (s (.stack 120)) = initial.C ∧
    (s (.stack 128)) = initial.D ∧
    ((s (.reg 0)) + (s (.stack 28))) = ((operation I X[13] 0x4e0811a1 21 working).A + X[4]) ∧
    (s (.reg 2)) = (operation I X[13] 0x4e0811a1 21 working).D ∧
    (s (.reg 2)) = (operation I X[13] 0x4e0811a1 21 working).D ∧
    (((((((~~~(s (.reg 0))) ||| (s (.reg 9))) ^^^ (s (.reg 2))) + ((s (.reg 8)) + (s (.stack 20))))
      + 0x4e0811a1)).rotateLeft 21 + (s (.reg 9))) = (operation I X[13] 0x4e0811a1 21 working).B ∧
    (s (.reg 9)) = (operation I X[13] 0x4e0811a1 21 working).C ∧
    (s (.reg 13)) = X[2]
  simp only [operation, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, true_and, and_true]
  md5_word_arithmetic

def Invariant61 (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) : Prop :=
  s (.stack 4) = X[9] ∧
  s (.stack 8) = initial.B ∧
  s (.stack 60) = initial.A ∧
  s (.stack 120) = initial.C ∧
  s (.stack 128) = initial.D ∧
  s (.reg 1) = working.B ∧
  s (.reg 2) = (working.A + X[11]) ∧
  s (.reg 7) = working.C ∧
  s (.reg 9) = working.D ∧
  s (.reg 13) = X[2]

def segment61 : List WordInstruction := [
  .not (.reg 1),
  .or (.reg 1) (.location (.reg 7)),
  .xor (.reg 1) (.location (.reg 9)),
  .add (.reg 1) (.location (.reg 0)),
  .add (.reg 1) (.immediate 0xf7537e82),
  .rol (.reg 1) 6,
  .add (.reg 2) (.location (.stack 32)),
  .add (.reg 1) (.location (.reg 7))]

theorem segment61_correct (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) (h : Invariant60 initial X working s) :
    Invariant61 initial X (operation I X[4] 0xf7537e82 6 working) (executeWords segment61 s) := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  with_unfolding_all change (s (.stack 4)) = X[9] ∧
    (s (.stack 8)) = initial.B ∧
    (s (.stack 60)) = initial.A ∧
    (s (.stack 120)) = initial.C ∧
    (s (.stack 128)) = initial.D ∧
    (((((((~~~(s (.reg 1))) ||| (s (.reg 7))) ^^^ (s (.reg 9))) + (s (.reg 0))) +
      0xf7537e82)).rotateLeft 6 + (s (.reg 7))) = (operation I X[4] 0xf7537e82 6 working).B ∧
    ((s (.reg 2)) + (s (.stack 32))) = ((operation I X[4] 0xf7537e82 6 working).A + X[11]) ∧
    (s (.reg 7)) = (operation I X[4] 0xf7537e82 6 working).C ∧
    (s (.reg 9)) = (operation I X[4] 0xf7537e82 6 working).D ∧
    (s (.reg 13)) = X[2]
  simp only [operation, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, true_and, and_true]
  md5_word_arithmetic

def Invariant62 (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) : Prop :=
  s (.stack 4) = X[9] ∧
  s (.stack 8) = initial.B ∧
  s (.stack 60) = initial.A ∧
  s (.stack 120) = initial.C ∧
  s (.stack 128) = initial.D ∧
  s (.reg 0) = working.B ∧
  s (.reg 1) = working.C ∧
  s (.reg 7) = working.D ∧
  s (.reg 9) = working.A ∧
  s (.reg 13) = X[2]

def segment62 : List WordInstruction := [
  .mov (.reg 0) (.location (.reg 9)),
  .not (.reg 0),
  .or (.reg 0) (.location (.reg 1)),
  .xor (.reg 0) (.location (.reg 7)),
  .add (.reg 0) (.location (.reg 2)),
  .add (.reg 0) (.immediate 0xbd3af235),
  .rol (.reg 0) 10,
  .add (.reg 0) (.location (.reg 1))]

theorem segment62_correct (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) (h : Invariant61 initial X working s) :
    Invariant62 initial X (operation I X[11] 0xbd3af235 10 working) (executeWords segment62 s) := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  with_unfolding_all change (s (.stack 4)) = X[9] ∧
    (s (.stack 8)) = initial.B ∧
    (s (.stack 60)) = initial.A ∧
    (s (.stack 120)) = initial.C ∧
    (s (.stack 128)) = initial.D ∧
    (((((((~~~(s (.reg 9))) ||| (s (.reg 1))) ^^^ (s (.reg 7))) + (s (.reg 2))) +
      0xbd3af235)).rotateLeft 10 + (s (.reg 1))) = (operation I X[11] 0xbd3af235 10 working).B ∧
    (s (.reg 1)) = (operation I X[11] 0xbd3af235 10 working).C ∧
    (s (.reg 7)) = (operation I X[11] 0xbd3af235 10 working).D ∧
    (s (.reg 9)) = (operation I X[11] 0xbd3af235 10 working).A ∧
    (s (.reg 13)) = X[2]
  simp only [operation, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, true_and, and_true]
  md5_word_arithmetic

def Invariant63 (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) : Prop :=
  s (.stack 8) = initial.B ∧
  s (.stack 60) = initial.A ∧
  s (.stack 120) = initial.C ∧
  s (.stack 128) = initial.D ∧
  s (.reg 0) = working.C ∧
  s (.reg 1) = working.D ∧
  s (.reg 2) = working.B ∧
  s (.reg 7) = (working.A + X[9]) ∧
  s (.reg 8) = (~~~working.D)

def segment63 : List WordInstruction := [
  .add (.reg 9) (.location (.reg 13)),
  .mov (.reg 2) (.location (.reg 7)),
  .not (.reg 2),
  .or (.reg 2) (.location (.reg 0)),
  .xor (.reg 2) (.location (.reg 1)),
  .add (.reg 2) (.location (.reg 9)),
  .add (.reg 2) (.immediate 0x2ad7d2bb),
  .rol (.reg 2) 15,
  .add (.reg 7) (.location (.stack 4)),
  .mov (.reg 8) (.location (.reg 1)),
  .not (.reg 8),
  .add (.reg 2) (.location (.reg 0))]

theorem segment63_correct (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) (h : Invariant62 initial X working s) :
    Invariant63 initial X (operation I X[2] 0x2ad7d2bb 15 working) (executeWords segment63 s) := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  with_unfolding_all change (s (.stack 8)) = initial.B ∧
    (s (.stack 60)) = initial.A ∧
    (s (.stack 120)) = initial.C ∧
    (s (.stack 128)) = initial.D ∧
    (s (.reg 0)) = (operation I X[2] 0x2ad7d2bb 15 working).C ∧
    (s (.reg 1)) = (operation I X[2] 0x2ad7d2bb 15 working).D ∧
    (((((((~~~(s (.reg 7))) ||| (s (.reg 0))) ^^^ (s (.reg 1))) + ((s (.reg 9)) + (s (.reg 13)))) +
      0x2ad7d2bb)).rotateLeft 15 + (s (.reg 0))) = (operation I X[2] 0x2ad7d2bb 15 working).B ∧
    ((s (.reg 7)) + (s (.stack 4))) = ((operation I X[2] 0x2ad7d2bb 15 working).A + X[9]) ∧
    (~~~(s (.reg 1))) = (~~~(operation I X[2] 0x2ad7d2bb 15 working).D)
  simp only [operation, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, true_and, and_true]
  md5_word_arithmetic

def Invariant64 (initial : Buffer) (_X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) : Prop :=
  s (.reg 0) = (working.D + initial.D) ∧
  s (.reg 1) = (working.A + initial.A) ∧
  s (.reg 2) = (working.C + initial.C) ∧
  s (.reg 8) = (initial.B + working.B)

def segment64 : List WordInstruction := [
  .or (.reg 8) (.location (.reg 2)),
  .xor (.reg 8) (.location (.reg 0)),
  .add (.reg 7) (.location (.reg 8)),
  .add (.reg 7) (.immediate 0xeb86d391),
  .mov (.reg 8) (.location (.stack 8)),
  .add (.reg 1) (.location (.stack 60)),
  .rol (.reg 7) 21,
  .add (.reg 8) (.location (.reg 2)),
  .add (.reg 8) (.location (.reg 7)),
  .add (.reg 2) (.location (.stack 120)),
  .add (.reg 0) (.location (.stack 128))]

theorem segment64_correct (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) (h : Invariant63 initial X working s) :
    Invariant64 initial X (operation I X[9] 0xeb86d391 21 working) (executeWords segment64 s) := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  with_unfolding_all change ((s (.reg 0)) + (s (.stack 128))) = ((operation I X[9] 0xeb86d391 21
    working).D + initial.D) ∧
    ((s (.reg 1)) + (s (.stack 60))) = ((operation I X[9] 0xeb86d391 21 working).A + initial.A) ∧
    ((s (.reg 2)) + (s (.stack 120))) = ((operation I X[9] 0xeb86d391 21 working).C + initial.C) ∧
    (((s (.stack 8)) + (s (.reg 2))) + ((((s (.reg 7)) + (((s (.reg 8)) ||| (s (.reg 2))) ^^^ (s
      (.reg 0)))) + 0xeb86d391)).rotateLeft 21) = (initial.B + (operation I X[9] 0xeb86d391 21
      working).B)
  simp only [operation, h0, h1, h2, h3, h4, h5, h6, h7, h8, true_and]
  md5_word_arithmetic

end Md5.Proofs.Block.Rounds
