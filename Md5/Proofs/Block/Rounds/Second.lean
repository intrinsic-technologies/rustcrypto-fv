import Md5.Proofs.Block.Rounds.First

namespace Md5.Proofs.Block.Rounds

open Standards.RFC.MD5

def Invariant17 (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) : Prop :=
  s (.stack 4) = X[9] ∧
  s (.stack 8) = initial.B ∧
  s (.stack 20) = X[13] ∧
  s (.stack 24) = X[8] ∧
  s (.stack 28) = X[4] ∧
  s (.stack 32) = X[11] ∧
  s (.stack 36) = X[14] ∧
  s (.stack 40) = X[10] ∧
  s (.stack 44) = X[12] ∧
  s (.stack 48) = X[15] ∧
  s (.stack 52) = X[7] ∧
  s (.stack 56) = X[6] ∧
  s (.stack 60) = initial.A ∧
  s (.stack 64) = X[5] ∧
  s (.stack 72) = X[3] ∧
  s (.stack 80) = X[1] ∧
  s (.stack 88) = X[0] ∧
  s (.stack 112) = X[2] ∧
  s (.stack 120) = initial.C ∧
  s (.stack 128) = initial.D ∧
  s (.reg 0) = ((working.A + X[6]) + ((~~~working.D) &&& working.C)) ∧
  s (.reg 1) = working.D ∧
  s (.reg 2) = working.C ∧
  s (.reg 7) = X[15] ∧
  s (.reg 8) = X[14] ∧
  s (.reg 11) = X[10] ∧
  s (.reg 12) = working.B ∧
  s (.reg 14) = X[11]

def segment17 : List WordInstruction := [
  .mov (.reg 15) (.location (.reg 2)),
  .and (.reg 15) (.location (.reg 0)),
  .lea (.reg 12) (.reg 15) (.reg 5),
  .add (.reg 12) (.immediate 0xf61e2562),
  .and (.reg 13) (.location (.reg 2)),
  .add (.reg 0) (.location (.reg 9)),
  .add (.reg 0) (.location (.reg 13)),
  .rol (.reg 12) 5,
  .add (.reg 12) (.location (.reg 2))]

theorem segment17_correct (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) (h : Invariant16 initial X working s) :
    Invariant17 initial X (operation G X[1] 0xf61e2562 5 working) (executeWords segment17 s) := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29⟩
  with_unfolding_all change (s (.stack 4)) = X[9] ∧
    (s (.stack 8)) = initial.B ∧
    (s (.stack 20)) = X[13] ∧
    (s (.stack 24)) = X[8] ∧
    (s (.stack 28)) = X[4] ∧
    (s (.stack 32)) = X[11] ∧
    (s (.stack 36)) = X[14] ∧
    (s (.stack 40)) = X[10] ∧
    (s (.stack 44)) = X[12] ∧
    (s (.stack 48)) = X[15] ∧
    (s (.stack 52)) = X[7] ∧
    (s (.stack 56)) = X[6] ∧
    (s (.stack 60)) = initial.A ∧
    (s (.stack 64)) = X[5] ∧
    (s (.stack 72)) = X[3] ∧
    (s (.stack 80)) = X[1] ∧
    (s (.stack 88)) = X[0] ∧
    (s (.stack 112)) = X[2] ∧
    (s (.stack 120)) = initial.C ∧
    (s (.stack 128)) = initial.D ∧
    (((s (.reg 0)) + (s (.reg 9))) + ((s (.reg 13)) &&& (s (.reg 2)))) = (((operation G X[1]
      0xf61e2562 5 working).A + X[6]) + ((~~~(operation G X[1] 0xf61e2562 5 working).D) &&&
      (operation G X[1] 0xf61e2562 5 working).C)) ∧
    (s (.reg 1)) = (operation G X[1] 0xf61e2562 5 working).D ∧
    (s (.reg 2)) = (operation G X[1] 0xf61e2562 5 working).C ∧
    (s (.reg 7)) = X[15] ∧
    (s (.reg 8)) = X[14] ∧
    (s (.reg 11)) = X[10] ∧
    ((((((s (.reg 2)) &&& (s (.reg 0))) + (s (.reg 5))) + 0xf61e2562)).rotateLeft 5 + (s (.reg 2)))
      = (operation G X[1] 0xf61e2562 5 working).B ∧
    (s (.reg 14)) = X[11]
  simp only [operation, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, true_and, and_true]
  md5_word_arithmetic

def Invariant18 (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) : Prop :=
  s (.stack 4) = X[9] ∧
  s (.stack 8) = initial.B ∧
  s (.stack 20) = X[13] ∧
  s (.stack 24) = X[8] ∧
  s (.stack 28) = X[4] ∧
  s (.stack 32) = X[11] ∧
  s (.stack 36) = X[14] ∧
  s (.stack 40) = X[10] ∧
  s (.stack 44) = X[12] ∧
  s (.stack 48) = X[15] ∧
  s (.stack 52) = X[7] ∧
  s (.stack 56) = X[6] ∧
  s (.stack 60) = initial.A ∧
  s (.stack 64) = X[5] ∧
  s (.stack 72) = X[3] ∧
  s (.stack 80) = X[1] ∧
  s (.stack 88) = X[0] ∧
  s (.stack 112) = X[2] ∧
  s (.stack 120) = initial.C ∧
  s (.stack 128) = initial.D ∧
  s (.reg 0) = working.B ∧
  s (.reg 1) = ((working.A + X[11]) + ((~~~working.D) &&& working.C)) ∧
  s (.reg 2) = working.D ∧
  s (.reg 7) = X[15] ∧
  s (.reg 8) = X[14] ∧
  s (.reg 11) = X[10] ∧
  s (.reg 12) = working.C

def segment18 : List WordInstruction := [
  .mov (.reg 15) (.location (.reg 12)),
  .and (.reg 15) (.location (.reg 1)),
  .add (.reg 0) (.location (.reg 15)),
  .add (.reg 0) (.immediate 0xc040b340),
  .mov (.reg 5) (.location (.reg 2)),
  .not (.reg 5),
  .and (.reg 5) (.location (.reg 12)),
  .add (.reg 1) (.location (.reg 14)),
  .add (.reg 1) (.location (.reg 5)),
  .rol (.reg 0) 9,
  .add (.reg 0) (.location (.reg 12))]

theorem segment18_correct (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) (h : Invariant17 initial X working s) :
    Invariant18 initial X (operation G X[6] 0xc040b340 9 working) (executeWords segment18 s) := by
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
    (s (.stack 44)) = X[12] ∧
    (s (.stack 48)) = X[15] ∧
    (s (.stack 52)) = X[7] ∧
    (s (.stack 56)) = X[6] ∧
    (s (.stack 60)) = initial.A ∧
    (s (.stack 64)) = X[5] ∧
    (s (.stack 72)) = X[3] ∧
    (s (.stack 80)) = X[1] ∧
    (s (.stack 88)) = X[0] ∧
    (s (.stack 112)) = X[2] ∧
    (s (.stack 120)) = initial.C ∧
    (s (.stack 128)) = initial.D ∧
    (((((s (.reg 0)) + ((s (.reg 12)) &&& (s (.reg 1)))) + 0xc040b340)).rotateLeft 9 + (s (.reg
      12))) = (operation G X[6] 0xc040b340 9 working).B ∧
    (((s (.reg 1)) + (s (.reg 14))) + ((~~~(s (.reg 2))) &&& (s (.reg 12)))) = (((operation G X[6]
      0xc040b340 9 working).A + X[11]) + ((~~~(operation G X[6] 0xc040b340 9 working).D) &&&
      (operation G X[6] 0xc040b340 9 working).C)) ∧
    (s (.reg 2)) = (operation G X[6] 0xc040b340 9 working).D ∧
    (s (.reg 7)) = X[15] ∧
    (s (.reg 8)) = X[14] ∧
    (s (.reg 11)) = X[10] ∧
    (s (.reg 12)) = (operation G X[6] 0xc040b340 9 working).C
  simp only [operation, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, true_and, and_true]
  md5_word_arithmetic

def Invariant19 (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) : Prop :=
  s (.stack 4) = X[9] ∧
  s (.stack 8) = initial.B ∧
  s (.stack 20) = X[13] ∧
  s (.stack 24) = X[8] ∧
  s (.stack 28) = X[4] ∧
  s (.stack 32) = X[11] ∧
  s (.stack 36) = X[14] ∧
  s (.stack 40) = X[10] ∧
  s (.stack 44) = X[12] ∧
  s (.stack 48) = X[15] ∧
  s (.stack 52) = X[7] ∧
  s (.stack 56) = X[6] ∧
  s (.stack 60) = initial.A ∧
  s (.stack 64) = X[5] ∧
  s (.stack 72) = X[3] ∧
  s (.stack 80) = X[1] ∧
  s (.stack 88) = X[0] ∧
  s (.stack 112) = X[2] ∧
  s (.stack 120) = initial.C ∧
  s (.stack 128) = initial.D ∧
  s (.reg 0) = working.C ∧
  s (.reg 1) = working.B ∧
  s (.reg 2) = ((working.A + X[0]) + ((~~~working.D) &&& working.C)) ∧
  s (.reg 7) = X[15] ∧
  s (.reg 8) = X[14] ∧
  s (.reg 11) = X[10] ∧
  s (.reg 12) = working.D

def segment19 : List WordInstruction := [
  .mov (.reg 15) (.location (.reg 0)),
  .and (.reg 15) (.location (.reg 2)),
  .add (.reg 1) (.location (.reg 15)),
  .add (.reg 1) (.immediate 0x265e5a51),
  .rol (.reg 1) 14,
  .mov (.reg 5) (.location (.reg 12)),
  .not (.reg 5),
  .and (.reg 5) (.location (.reg 0)),
  .add (.reg 2) (.location (.stack 88)),
  .add (.reg 2) (.location (.reg 5)),
  .add (.reg 1) (.location (.reg 0))]

theorem segment19_correct (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) (h : Invariant18 initial X working s) :
    Invariant19 initial X (operation G X[11] 0x265e5a51 14 working) (executeWords segment19 s) := by
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
    (s (.stack 44)) = X[12] ∧
    (s (.stack 48)) = X[15] ∧
    (s (.stack 52)) = X[7] ∧
    (s (.stack 56)) = X[6] ∧
    (s (.stack 60)) = initial.A ∧
    (s (.stack 64)) = X[5] ∧
    (s (.stack 72)) = X[3] ∧
    (s (.stack 80)) = X[1] ∧
    (s (.stack 88)) = X[0] ∧
    (s (.stack 112)) = X[2] ∧
    (s (.stack 120)) = initial.C ∧
    (s (.stack 128)) = initial.D ∧
    (s (.reg 0)) = (operation G X[11] 0x265e5a51 14 working).C ∧
    (((((s (.reg 1)) + ((s (.reg 0)) &&& (s (.reg 2)))) + 0x265e5a51)).rotateLeft 14 + (s (.reg 0)))
      = (operation G X[11] 0x265e5a51 14 working).B ∧
    (((s (.reg 2)) + (s (.stack 88))) + ((~~~(s (.reg 12))) &&& (s (.reg 0)))) = (((operation G
      X[11] 0x265e5a51 14 working).A + X[0]) + ((~~~(operation G X[11] 0x265e5a51 14 working).D) &&&
      (operation G X[11] 0x265e5a51 14 working).C)) ∧
    (s (.reg 7)) = X[15] ∧
    (s (.reg 8)) = X[14] ∧
    (s (.reg 11)) = X[10] ∧
    (s (.reg 12)) = (operation G X[11] 0x265e5a51 14 working).D
  simp only [operation, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, true_and, and_true]
  md5_word_arithmetic

def Invariant20 (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) : Prop :=
  s (.stack 4) = X[9] ∧
  s (.stack 8) = initial.B ∧
  s (.stack 20) = X[13] ∧
  s (.stack 24) = X[8] ∧
  s (.stack 28) = X[4] ∧
  s (.stack 32) = X[11] ∧
  s (.stack 36) = X[14] ∧
  s (.stack 40) = X[10] ∧
  s (.stack 44) = X[12] ∧
  s (.stack 48) = X[15] ∧
  s (.stack 52) = X[7] ∧
  s (.stack 56) = X[6] ∧
  s (.stack 60) = initial.A ∧
  s (.stack 64) = X[5] ∧
  s (.stack 72) = X[3] ∧
  s (.stack 80) = X[1] ∧
  s (.stack 88) = X[0] ∧
  s (.stack 112) = X[2] ∧
  s (.stack 120) = initial.C ∧
  s (.stack 128) = initial.D ∧
  s (.reg 0) = working.D ∧
  s (.reg 1) = working.C ∧
  s (.reg 2) = working.B ∧
  s (.reg 3) = X[5] ∧
  s (.reg 7) = X[15] ∧
  s (.reg 8) = X[14] ∧
  s (.reg 11) = X[10] ∧
  s (.reg 12) = ((working.A + X[5]) + ((~~~working.D) &&& working.C))

def segment20 : List WordInstruction := [
  .mov (.reg 15) (.location (.reg 1)),
  .and (.reg 15) (.location (.reg 12)),
  .add (.reg 2) (.location (.reg 15)),
  .add (.reg 2) (.immediate 0xe9b6c7aa),
  .mov (.reg 5) (.location (.reg 0)),
  .not (.reg 5),
  .and (.reg 5) (.location (.reg 1)),
  .mov (.reg 3) (.location (.stack 64)),
  .add (.reg 12) (.location (.reg 3)),
  .add (.reg 12) (.location (.reg 5)),
  .rol (.reg 2) 20,
  .add (.reg 2) (.location (.reg 1))]

theorem segment20_correct (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) (h : Invariant19 initial X working s) :
    Invariant20 initial X (operation G X[0] 0xe9b6c7aa 20 working) (executeWords segment20 s) := by
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
    (s (.stack 44)) = X[12] ∧
    (s (.stack 48)) = X[15] ∧
    (s (.stack 52)) = X[7] ∧
    (s (.stack 56)) = X[6] ∧
    (s (.stack 60)) = initial.A ∧
    (s (.stack 64)) = X[5] ∧
    (s (.stack 72)) = X[3] ∧
    (s (.stack 80)) = X[1] ∧
    (s (.stack 88)) = X[0] ∧
    (s (.stack 112)) = X[2] ∧
    (s (.stack 120)) = initial.C ∧
    (s (.stack 128)) = initial.D ∧
    (s (.reg 0)) = (operation G X[0] 0xe9b6c7aa 20 working).D ∧
    (s (.reg 1)) = (operation G X[0] 0xe9b6c7aa 20 working).C ∧
    (((((s (.reg 2)) + ((s (.reg 1)) &&& (s (.reg 12)))) + 0xe9b6c7aa)).rotateLeft 20 + (s (.reg
      1))) = (operation G X[0] 0xe9b6c7aa 20 working).B ∧
    (s (.stack 64)) = X[5] ∧
    (s (.reg 7)) = X[15] ∧
    (s (.reg 8)) = X[14] ∧
    (s (.reg 11)) = X[10] ∧
    (((s (.reg 12)) + (s (.stack 64))) + ((~~~(s (.reg 0))) &&& (s (.reg 1)))) = (((operation G X[0]
      0xe9b6c7aa 20 working).A + X[5]) + ((~~~(operation G X[0] 0xe9b6c7aa 20 working).D) &&&
      (operation G X[0] 0xe9b6c7aa 20 working).C))
  simp only [operation, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, true_and, and_true]
  md5_word_arithmetic

def Invariant21 (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) : Prop :=
  s (.stack 4) = X[9] ∧
  s (.stack 8) = initial.B ∧
  s (.stack 20) = X[13] ∧
  s (.stack 24) = X[8] ∧
  s (.stack 28) = X[4] ∧
  s (.stack 32) = X[11] ∧
  s (.stack 36) = X[14] ∧
  s (.stack 40) = X[10] ∧
  s (.stack 44) = X[12] ∧
  s (.stack 48) = X[15] ∧
  s (.stack 52) = X[7] ∧
  s (.stack 56) = X[6] ∧
  s (.stack 60) = initial.A ∧
  s (.stack 64) = X[5] ∧
  s (.stack 72) = X[3] ∧
  s (.stack 80) = X[1] ∧
  s (.stack 88) = X[0] ∧
  s (.stack 112) = X[2] ∧
  s (.stack 120) = initial.C ∧
  s (.stack 128) = initial.D ∧
  s (.reg 0) = ((working.A + X[10]) + ((~~~working.D) &&& working.C)) ∧
  s (.reg 1) = working.D ∧
  s (.reg 2) = working.C ∧
  s (.reg 3) = X[5] ∧
  s (.reg 5) = working.B ∧
  s (.reg 7) = X[15] ∧
  s (.reg 8) = X[14]

def segment21 : List WordInstruction := [
  .mov (.reg 15) (.location (.reg 2)),
  .and (.reg 15) (.location (.reg 0)),
  .lea (.reg 5) (.reg 15) (.reg 12),
  .add (.reg 5) (.immediate 0xd62f105d),
  .mov (.reg 15) (.location (.reg 1)),
  .not (.reg 15),
  .and (.reg 15) (.location (.reg 2)),
  .add (.reg 0) (.location (.reg 11)),
  .add (.reg 0) (.location (.reg 15)),
  .rol (.reg 5) 5,
  .add (.reg 5) (.location (.reg 2))]

theorem segment21_correct (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) (h : Invariant20 initial X working s) :
    Invariant21 initial X (operation G X[5] 0xd62f105d 5 working) (executeWords segment21 s) := by
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
    (s (.stack 44)) = X[12] ∧
    (s (.stack 48)) = X[15] ∧
    (s (.stack 52)) = X[7] ∧
    (s (.stack 56)) = X[6] ∧
    (s (.stack 60)) = initial.A ∧
    (s (.stack 64)) = X[5] ∧
    (s (.stack 72)) = X[3] ∧
    (s (.stack 80)) = X[1] ∧
    (s (.stack 88)) = X[0] ∧
    (s (.stack 112)) = X[2] ∧
    (s (.stack 120)) = initial.C ∧
    (s (.stack 128)) = initial.D ∧
    (((s (.reg 0)) + (s (.reg 11))) + ((~~~(s (.reg 1))) &&& (s (.reg 2)))) = (((operation G X[5]
      0xd62f105d 5 working).A + X[10]) + ((~~~(operation G X[5] 0xd62f105d 5 working).D) &&&
      (operation G X[5] 0xd62f105d 5 working).C)) ∧
    (s (.reg 1)) = (operation G X[5] 0xd62f105d 5 working).D ∧
    (s (.reg 2)) = (operation G X[5] 0xd62f105d 5 working).C ∧
    (s (.reg 3)) = X[5] ∧
    ((((((s (.reg 2)) &&& (s (.reg 0))) + (s (.reg 12))) + 0xd62f105d)).rotateLeft 5 + (s (.reg 2)))
      = (operation G X[5] 0xd62f105d 5 working).B ∧
    (s (.reg 7)) = X[15] ∧
    (s (.reg 8)) = X[14]
  simp only [operation, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, true_and, and_true]
  md5_word_arithmetic

def Invariant22 (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) : Prop :=
  s (.stack 4) = X[9] ∧
  s (.stack 8) = initial.B ∧
  s (.stack 20) = X[13] ∧
  s (.stack 24) = X[8] ∧
  s (.stack 28) = X[4] ∧
  s (.stack 32) = X[11] ∧
  s (.stack 36) = X[14] ∧
  s (.stack 40) = X[10] ∧
  s (.stack 44) = X[12] ∧
  s (.stack 48) = X[15] ∧
  s (.stack 52) = X[7] ∧
  s (.stack 56) = X[6] ∧
  s (.stack 60) = initial.A ∧
  s (.stack 64) = X[5] ∧
  s (.stack 72) = X[3] ∧
  s (.stack 80) = X[1] ∧
  s (.stack 88) = X[0] ∧
  s (.stack 112) = X[2] ∧
  s (.stack 120) = initial.C ∧
  s (.stack 128) = initial.D ∧
  s (.reg 0) = working.B ∧
  s (.reg 1) = ((working.A + X[15]) + ((~~~working.D) &&& working.C)) ∧
  s (.reg 2) = working.D ∧
  s (.reg 3) = X[5] ∧
  s (.reg 5) = working.C ∧
  s (.reg 8) = X[14]

def segment22 : List WordInstruction := [
  .mov (.reg 15) (.location (.reg 5)),
  .and (.reg 15) (.location (.reg 1)),
  .add (.reg 0) (.location (.reg 15)),
  .add (.reg 0) (.immediate 0x2441453),
  .mov (.reg 15) (.location (.reg 2)),
  .not (.reg 15),
  .and (.reg 15) (.location (.reg 5)),
  .add (.reg 1) (.location (.reg 7)),
  .add (.reg 1) (.location (.reg 15)),
  .rol (.reg 0) 9,
  .add (.reg 0) (.location (.reg 5))]

theorem segment22_correct (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) (h : Invariant21 initial X working s) :
    Invariant22 initial X (operation G X[10] 0x2441453 9 working) (executeWords segment22 s) := by
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
    (s (.stack 44)) = X[12] ∧
    (s (.stack 48)) = X[15] ∧
    (s (.stack 52)) = X[7] ∧
    (s (.stack 56)) = X[6] ∧
    (s (.stack 60)) = initial.A ∧
    (s (.stack 64)) = X[5] ∧
    (s (.stack 72)) = X[3] ∧
    (s (.stack 80)) = X[1] ∧
    (s (.stack 88)) = X[0] ∧
    (s (.stack 112)) = X[2] ∧
    (s (.stack 120)) = initial.C ∧
    (s (.stack 128)) = initial.D ∧
    (((((s (.reg 0)) + ((s (.reg 5)) &&& (s (.reg 1)))) + 0x2441453)).rotateLeft 9 + (s (.reg 5))) =
      (operation G X[10] 0x2441453 9 working).B ∧
    (((s (.reg 1)) + (s (.reg 7))) + ((~~~(s (.reg 2))) &&& (s (.reg 5)))) = (((operation G X[10]
      0x2441453 9 working).A + X[15]) + ((~~~(operation G X[10] 0x2441453 9 working).D) &&&
      (operation G X[10] 0x2441453 9 working).C)) ∧
    (s (.reg 2)) = (operation G X[10] 0x2441453 9 working).D ∧
    (s (.reg 3)) = X[5] ∧
    (s (.reg 5)) = (operation G X[10] 0x2441453 9 working).C ∧
    (s (.reg 8)) = X[14]
  simp only [operation, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, true_and, and_true]
  md5_word_arithmetic

def Invariant23 (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) : Prop :=
  s (.stack 4) = X[9] ∧
  s (.stack 8) = initial.B ∧
  s (.stack 20) = X[13] ∧
  s (.stack 24) = X[8] ∧
  s (.stack 28) = X[4] ∧
  s (.stack 32) = X[11] ∧
  s (.stack 36) = X[14] ∧
  s (.stack 40) = X[10] ∧
  s (.stack 44) = X[12] ∧
  s (.stack 48) = X[15] ∧
  s (.stack 52) = X[7] ∧
  s (.stack 56) = X[6] ∧
  s (.stack 60) = initial.A ∧
  s (.stack 64) = X[5] ∧
  s (.stack 72) = X[3] ∧
  s (.stack 80) = X[1] ∧
  s (.stack 88) = X[0] ∧
  s (.stack 112) = X[2] ∧
  s (.stack 120) = initial.C ∧
  s (.stack 128) = initial.D ∧
  s (.reg 0) = working.C ∧
  s (.reg 1) = working.B ∧
  s (.reg 2) = ((working.A + X[4]) + ((~~~working.D) &&& working.C)) ∧
  s (.reg 3) = X[5] ∧
  s (.reg 5) = working.D ∧
  s (.reg 7) = X[4] ∧
  s (.reg 8) = X[14]

def segment23 : List WordInstruction := [
  .mov (.reg 15) (.location (.reg 0)),
  .and (.reg 15) (.location (.reg 2)),
  .add (.reg 1) (.location (.reg 15)),
  .add (.reg 1) (.immediate 0xd8a1e681),
  .rol (.reg 1) 14,
  .mov (.reg 15) (.location (.reg 5)),
  .not (.reg 15),
  .and (.reg 15) (.location (.reg 0)),
  .mov (.reg 7) (.location (.stack 28)),
  .add (.reg 2) (.location (.reg 7)),
  .add (.reg 2) (.location (.reg 15)),
  .add (.reg 1) (.location (.reg 0))]

theorem segment23_correct (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) (h : Invariant22 initial X working s) :
    Invariant23 initial X (operation G X[15] 0xd8a1e681 14 working) (executeWords segment23 s) := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    h18, h19, h20, h21, h22, h23, h24, h25⟩
  with_unfolding_all change (s (.stack 4)) = X[9] ∧
    (s (.stack 8)) = initial.B ∧
    (s (.stack 20)) = X[13] ∧
    (s (.stack 24)) = X[8] ∧
    (s (.stack 28)) = X[4] ∧
    (s (.stack 32)) = X[11] ∧
    (s (.stack 36)) = X[14] ∧
    (s (.stack 40)) = X[10] ∧
    (s (.stack 44)) = X[12] ∧
    (s (.stack 48)) = X[15] ∧
    (s (.stack 52)) = X[7] ∧
    (s (.stack 56)) = X[6] ∧
    (s (.stack 60)) = initial.A ∧
    (s (.stack 64)) = X[5] ∧
    (s (.stack 72)) = X[3] ∧
    (s (.stack 80)) = X[1] ∧
    (s (.stack 88)) = X[0] ∧
    (s (.stack 112)) = X[2] ∧
    (s (.stack 120)) = initial.C ∧
    (s (.stack 128)) = initial.D ∧
    (s (.reg 0)) = (operation G X[15] 0xd8a1e681 14 working).C ∧
    (((((s (.reg 1)) + ((s (.reg 0)) &&& (s (.reg 2)))) + 0xd8a1e681)).rotateLeft 14 + (s (.reg 0)))
      = (operation G X[15] 0xd8a1e681 14 working).B ∧
    (((s (.reg 2)) + (s (.stack 28))) + ((~~~(s (.reg 5))) &&& (s (.reg 0)))) = (((operation G X[15]
      0xd8a1e681 14 working).A + X[4]) + ((~~~(operation G X[15] 0xd8a1e681 14 working).D) &&&
      (operation G X[15] 0xd8a1e681 14 working).C)) ∧
    (s (.reg 3)) = X[5] ∧
    (s (.reg 5)) = (operation G X[15] 0xd8a1e681 14 working).D ∧
    (s (.stack 28)) = X[4] ∧
    (s (.reg 8)) = X[14]
  simp only [operation, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18, h19, h20, h21, h22, h23, h24, h25, true_and, and_true]
  md5_word_arithmetic

def Invariant24 (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) : Prop :=
  s (.stack 4) = X[9] ∧
  s (.stack 8) = initial.B ∧
  s (.stack 20) = X[13] ∧
  s (.stack 24) = X[8] ∧
  s (.stack 28) = X[4] ∧
  s (.stack 32) = X[11] ∧
  s (.stack 36) = X[14] ∧
  s (.stack 40) = X[10] ∧
  s (.stack 44) = X[12] ∧
  s (.stack 48) = X[15] ∧
  s (.stack 52) = X[7] ∧
  s (.stack 56) = X[6] ∧
  s (.stack 60) = initial.A ∧
  s (.stack 64) = X[5] ∧
  s (.stack 72) = X[3] ∧
  s (.stack 80) = X[1] ∧
  s (.stack 88) = X[0] ∧
  s (.stack 112) = X[2] ∧
  s (.stack 120) = initial.C ∧
  s (.stack 128) = initial.D ∧
  s (.reg 0) = working.D ∧
  s (.reg 1) = working.C ∧
  s (.reg 2) = working.B ∧
  s (.reg 3) = X[5] ∧
  s (.reg 5) = ((working.A + X[9]) + ((~~~working.D) &&& working.C)) ∧
  s (.reg 7) = X[4] ∧
  s (.reg 8) = X[14]

def segment24 : List WordInstruction := [
  .mov (.reg 15) (.location (.reg 1)),
  .and (.reg 15) (.location (.reg 5)),
  .add (.reg 2) (.location (.reg 15)),
  .add (.reg 2) (.immediate 0xe7d3fbc8),
  .mov (.reg 15) (.location (.reg 0)),
  .not (.reg 15),
  .and (.reg 15) (.location (.reg 1)),
  .add (.reg 5) (.location (.stack 4)),
  .add (.reg 5) (.location (.reg 15)),
  .rol (.reg 2) 20,
  .add (.reg 2) (.location (.reg 1))]

theorem segment24_correct (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) (h : Invariant23 initial X working s) :
    Invariant24 initial X (operation G X[4] 0xe7d3fbc8 20 working) (executeWords segment24 s) := by
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
    (s (.stack 44)) = X[12] ∧
    (s (.stack 48)) = X[15] ∧
    (s (.stack 52)) = X[7] ∧
    (s (.stack 56)) = X[6] ∧
    (s (.stack 60)) = initial.A ∧
    (s (.stack 64)) = X[5] ∧
    (s (.stack 72)) = X[3] ∧
    (s (.stack 80)) = X[1] ∧
    (s (.stack 88)) = X[0] ∧
    (s (.stack 112)) = X[2] ∧
    (s (.stack 120)) = initial.C ∧
    (s (.stack 128)) = initial.D ∧
    (s (.reg 0)) = (operation G X[4] 0xe7d3fbc8 20 working).D ∧
    (s (.reg 1)) = (operation G X[4] 0xe7d3fbc8 20 working).C ∧
    (((((s (.reg 2)) + ((s (.reg 1)) &&& (s (.reg 5)))) + 0xe7d3fbc8)).rotateLeft 20 + (s (.reg 1)))
      = (operation G X[4] 0xe7d3fbc8 20 working).B ∧
    (s (.reg 3)) = X[5] ∧
    (((s (.reg 5)) + (s (.stack 4))) + ((~~~(s (.reg 0))) &&& (s (.reg 1)))) = (((operation G X[4]
      0xe7d3fbc8 20 working).A + X[9]) + ((~~~(operation G X[4] 0xe7d3fbc8 20 working).D) &&&
      (operation G X[4] 0xe7d3fbc8 20 working).C)) ∧
    (s (.reg 7)) = X[4] ∧
    (s (.reg 8)) = X[14]
  simp only [operation, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, true_and, and_true]
  md5_word_arithmetic

def Invariant25 (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) : Prop :=
  s (.stack 4) = X[9] ∧
  s (.stack 8) = initial.B ∧
  s (.stack 20) = X[13] ∧
  s (.stack 24) = X[8] ∧
  s (.stack 28) = X[4] ∧
  s (.stack 32) = X[11] ∧
  s (.stack 36) = X[14] ∧
  s (.stack 40) = X[10] ∧
  s (.stack 44) = X[12] ∧
  s (.stack 48) = X[15] ∧
  s (.stack 52) = X[7] ∧
  s (.stack 56) = X[6] ∧
  s (.stack 60) = initial.A ∧
  s (.stack 64) = X[5] ∧
  s (.stack 72) = X[3] ∧
  s (.stack 80) = X[1] ∧
  s (.stack 88) = X[0] ∧
  s (.stack 112) = X[2] ∧
  s (.stack 120) = initial.C ∧
  s (.stack 128) = initial.D ∧
  s (.reg 0) = ((working.A + X[14]) + ((~~~working.D) &&& working.C)) ∧
  s (.reg 1) = working.D ∧
  s (.reg 2) = working.C ∧
  s (.reg 3) = X[5] ∧
  s (.reg 5) = working.B ∧
  s (.reg 7) = X[4]

def segment25 : List WordInstruction := [
  .mov (.reg 15) (.location (.reg 2)),
  .and (.reg 15) (.location (.reg 0)),
  .add (.reg 5) (.location (.reg 15)),
  .add (.reg 5) (.immediate 0x21e1cde6),
  .mov (.reg 15) (.location (.reg 1)),
  .not (.reg 15),
  .and (.reg 15) (.location (.reg 2)),
  .add (.reg 0) (.location (.reg 8)),
  .add (.reg 0) (.location (.reg 15)),
  .rol (.reg 5) 5,
  .add (.reg 5) (.location (.reg 2))]

theorem segment25_correct (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) (h : Invariant24 initial X working s) :
    Invariant25 initial X (operation G X[9] 0x21e1cde6 5 working) (executeWords segment25 s) := by
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
    (s (.stack 44)) = X[12] ∧
    (s (.stack 48)) = X[15] ∧
    (s (.stack 52)) = X[7] ∧
    (s (.stack 56)) = X[6] ∧
    (s (.stack 60)) = initial.A ∧
    (s (.stack 64)) = X[5] ∧
    (s (.stack 72)) = X[3] ∧
    (s (.stack 80)) = X[1] ∧
    (s (.stack 88)) = X[0] ∧
    (s (.stack 112)) = X[2] ∧
    (s (.stack 120)) = initial.C ∧
    (s (.stack 128)) = initial.D ∧
    (((s (.reg 0)) + (s (.reg 8))) + ((~~~(s (.reg 1))) &&& (s (.reg 2)))) = (((operation G X[9]
      0x21e1cde6 5 working).A + X[14]) + ((~~~(operation G X[9] 0x21e1cde6 5 working).D) &&&
      (operation G X[9] 0x21e1cde6 5 working).C)) ∧
    (s (.reg 1)) = (operation G X[9] 0x21e1cde6 5 working).D ∧
    (s (.reg 2)) = (operation G X[9] 0x21e1cde6 5 working).C ∧
    (s (.reg 3)) = X[5] ∧
    (((((s (.reg 5)) + ((s (.reg 2)) &&& (s (.reg 0)))) + 0x21e1cde6)).rotateLeft 5 + (s (.reg 2)))
      = (operation G X[9] 0x21e1cde6 5 working).B ∧
    (s (.reg 7)) = X[4]
  simp only [operation, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, true_and, and_true]
  md5_word_arithmetic

def Invariant26 (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) : Prop :=
  s (.stack 4) = X[9] ∧
  s (.stack 8) = initial.B ∧
  s (.stack 20) = X[13] ∧
  s (.stack 24) = X[8] ∧
  s (.stack 28) = X[4] ∧
  s (.stack 32) = X[11] ∧
  s (.stack 36) = X[14] ∧
  s (.stack 40) = X[10] ∧
  s (.stack 44) = X[12] ∧
  s (.stack 48) = X[15] ∧
  s (.stack 52) = X[7] ∧
  s (.stack 56) = X[6] ∧
  s (.stack 60) = initial.A ∧
  s (.stack 64) = X[5] ∧
  s (.stack 72) = X[3] ∧
  s (.stack 80) = X[1] ∧
  s (.stack 88) = X[0] ∧
  s (.stack 112) = X[2] ∧
  s (.stack 120) = initial.C ∧
  s (.stack 128) = initial.D ∧
  s (.reg 1) = ((working.A + X[3]) + ((~~~working.D) &&& working.C)) ∧
  s (.reg 2) = working.D ∧
  s (.reg 3) = X[5] ∧
  s (.reg 5) = working.C ∧
  s (.reg 7) = X[4] ∧
  s (.reg 9) = X[3] ∧
  s (.reg 12) = working.B

def segment26 : List WordInstruction := [
  .mov (.reg 15) (.location (.reg 5)),
  .and (.reg 15) (.location (.reg 1)),
  .lea (.reg 12) (.reg 15) (.reg 0),
  .add (.reg 12) (.immediate 0xc33707d6),
  .mov (.reg 0) (.location (.reg 2)),
  .not (.reg 0),
  .and (.reg 0) (.location (.reg 5)),
  .mov (.reg 9) (.location (.stack 72)),
  .add (.reg 1) (.location (.reg 9)),
  .add (.reg 1) (.location (.reg 0)),
  .rol (.reg 12) 9,
  .add (.reg 12) (.location (.reg 5))]

theorem segment26_correct (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) (h : Invariant25 initial X working s) :
    Invariant26 initial X (operation G X[14] 0xc33707d6 9 working) (executeWords segment26 s) := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    h18, h19, h20, h21, h22, h23, h24, h25⟩
  with_unfolding_all change (s (.stack 4)) = X[9] ∧
    (s (.stack 8)) = initial.B ∧
    (s (.stack 20)) = X[13] ∧
    (s (.stack 24)) = X[8] ∧
    (s (.stack 28)) = X[4] ∧
    (s (.stack 32)) = X[11] ∧
    (s (.stack 36)) = X[14] ∧
    (s (.stack 40)) = X[10] ∧
    (s (.stack 44)) = X[12] ∧
    (s (.stack 48)) = X[15] ∧
    (s (.stack 52)) = X[7] ∧
    (s (.stack 56)) = X[6] ∧
    (s (.stack 60)) = initial.A ∧
    (s (.stack 64)) = X[5] ∧
    (s (.stack 72)) = X[3] ∧
    (s (.stack 80)) = X[1] ∧
    (s (.stack 88)) = X[0] ∧
    (s (.stack 112)) = X[2] ∧
    (s (.stack 120)) = initial.C ∧
    (s (.stack 128)) = initial.D ∧
    (((s (.reg 1)) + (s (.stack 72))) + ((~~~(s (.reg 2))) &&& (s (.reg 5)))) = (((operation G X[14]
      0xc33707d6 9 working).A + X[3]) + ((~~~(operation G X[14] 0xc33707d6 9 working).D) &&&
      (operation G X[14] 0xc33707d6 9 working).C)) ∧
    (s (.reg 2)) = (operation G X[14] 0xc33707d6 9 working).D ∧
    (s (.reg 3)) = X[5] ∧
    (s (.reg 5)) = (operation G X[14] 0xc33707d6 9 working).C ∧
    (s (.reg 7)) = X[4] ∧
    (s (.stack 72)) = X[3] ∧
    ((((((s (.reg 5)) &&& (s (.reg 1))) + (s (.reg 0))) + 0xc33707d6)).rotateLeft 9 + (s (.reg 5)))
      = (operation G X[14] 0xc33707d6 9 working).B
  simp only [operation, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18, h19, h20, h21, h22, h23, h24, h25, true_and]
  md5_word_arithmetic

def Invariant27 (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) : Prop :=
  s (.stack 4) = X[9] ∧
  s (.stack 8) = initial.B ∧
  s (.stack 20) = X[13] ∧
  s (.stack 24) = X[8] ∧
  s (.stack 28) = X[4] ∧
  s (.stack 32) = X[11] ∧
  s (.stack 36) = X[14] ∧
  s (.stack 40) = X[10] ∧
  s (.stack 44) = X[12] ∧
  s (.stack 48) = X[15] ∧
  s (.stack 52) = X[7] ∧
  s (.stack 56) = X[6] ∧
  s (.stack 60) = initial.A ∧
  s (.stack 64) = X[5] ∧
  s (.stack 72) = X[3] ∧
  s (.stack 80) = X[1] ∧
  s (.stack 88) = X[0] ∧
  s (.stack 112) = X[2] ∧
  s (.stack 120) = initial.C ∧
  s (.stack 128) = initial.D ∧
  s (.reg 1) = working.B ∧
  s (.reg 2) = ((working.A + X[8]) + ((~~~working.D) &&& working.C)) ∧
  s (.reg 3) = X[5] ∧
  s (.reg 5) = working.D ∧
  s (.reg 7) = X[4] ∧
  s (.reg 9) = X[3] ∧
  s (.reg 12) = working.C ∧
  s (.reg 14) = X[8]

def segment27 : List WordInstruction := [
  .mov (.reg 0) (.location (.reg 12)),
  .and (.reg 0) (.location (.reg 2)),
  .add (.reg 1) (.location (.reg 0)),
  .add (.reg 1) (.immediate 0xf4d50d87),
  .rol (.reg 1) 14,
  .mov (.reg 0) (.location (.reg 5)),
  .not (.reg 0),
  .and (.reg 0) (.location (.reg 12)),
  .mov (.reg 14) (.location (.stack 24)),
  .add (.reg 2) (.location (.reg 14)),
  .add (.reg 2) (.location (.reg 0)),
  .add (.reg 1) (.location (.reg 12))]

theorem segment27_correct (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) (h : Invariant26 initial X working s) :
    Invariant27 initial X (operation G X[3] 0xf4d50d87 14 working) (executeWords segment27 s) := by
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
    (s (.stack 44)) = X[12] ∧
    (s (.stack 48)) = X[15] ∧
    (s (.stack 52)) = X[7] ∧
    (s (.stack 56)) = X[6] ∧
    (s (.stack 60)) = initial.A ∧
    (s (.stack 64)) = X[5] ∧
    (s (.stack 72)) = X[3] ∧
    (s (.stack 80)) = X[1] ∧
    (s (.stack 88)) = X[0] ∧
    (s (.stack 112)) = X[2] ∧
    (s (.stack 120)) = initial.C ∧
    (s (.stack 128)) = initial.D ∧
    (((((s (.reg 1)) + ((s (.reg 12)) &&& (s (.reg 2)))) + 0xf4d50d87)).rotateLeft 14 + (s (.reg
      12))) = (operation G X[3] 0xf4d50d87 14 working).B ∧
    (((s (.reg 2)) + (s (.stack 24))) + ((~~~(s (.reg 5))) &&& (s (.reg 12)))) = (((operation G X[3]
      0xf4d50d87 14 working).A + X[8]) + ((~~~(operation G X[3] 0xf4d50d87 14 working).D) &&&
      (operation G X[3] 0xf4d50d87 14 working).C)) ∧
    (s (.reg 3)) = X[5] ∧
    (s (.reg 5)) = (operation G X[3] 0xf4d50d87 14 working).D ∧
    (s (.reg 7)) = X[4] ∧
    (s (.reg 9)) = X[3] ∧
    (s (.reg 12)) = (operation G X[3] 0xf4d50d87 14 working).C ∧
    (s (.stack 24)) = X[8]
  simp only [operation, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, true_and, and_true]
  md5_word_arithmetic

def Invariant28 (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) : Prop :=
  s (.stack 4) = X[9] ∧
  s (.stack 8) = initial.B ∧
  s (.stack 20) = X[13] ∧
  s (.stack 24) = X[8] ∧
  s (.stack 28) = X[4] ∧
  s (.stack 32) = X[11] ∧
  s (.stack 36) = X[14] ∧
  s (.stack 40) = X[10] ∧
  s (.stack 44) = X[12] ∧
  s (.stack 48) = X[15] ∧
  s (.stack 52) = X[7] ∧
  s (.stack 56) = X[6] ∧
  s (.stack 60) = initial.A ∧
  s (.stack 64) = X[5] ∧
  s (.stack 72) = X[3] ∧
  s (.stack 80) = X[1] ∧
  s (.stack 88) = X[0] ∧
  s (.stack 112) = X[2] ∧
  s (.stack 120) = initial.C ∧
  s (.stack 128) = initial.D ∧
  s (.reg 0) = working.B ∧
  s (.reg 1) = working.C ∧
  s (.reg 3) = X[5] ∧
  s (.reg 5) = ((working.A + X[13]) + ((~~~working.D) &&& working.C)) ∧
  s (.reg 7) = X[4] ∧
  s (.reg 9) = X[3] ∧
  s (.reg 10) = X[13] ∧
  s (.reg 12) = working.D ∧
  s (.reg 14) = X[8]

def segment28 : List WordInstruction := [
  .mov (.reg 0) (.location (.reg 1)),
  .and (.reg 0) (.location (.reg 5)),
  .add (.reg 0) (.location (.reg 2)),
  .add (.reg 0) (.immediate 0x455a14ed),
  .mov (.reg 2) (.location (.reg 12)),
  .not (.reg 2),
  .and (.reg 2) (.location (.reg 1)),
  .mov (.reg 10) (.location (.stack 20)),
  .add (.reg 5) (.location (.reg 10)),
  .add (.reg 5) (.location (.reg 2)),
  .rol (.reg 0) 20,
  .add (.reg 0) (.location (.reg 1))]

theorem segment28_correct (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) (h : Invariant27 initial X working s) :
    Invariant28 initial X (operation G X[8] 0x455a14ed 20 working) (executeWords segment28 s) := by
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
    (s (.stack 44)) = X[12] ∧
    (s (.stack 48)) = X[15] ∧
    (s (.stack 52)) = X[7] ∧
    (s (.stack 56)) = X[6] ∧
    (s (.stack 60)) = initial.A ∧
    (s (.stack 64)) = X[5] ∧
    (s (.stack 72)) = X[3] ∧
    (s (.stack 80)) = X[1] ∧
    (s (.stack 88)) = X[0] ∧
    (s (.stack 112)) = X[2] ∧
    (s (.stack 120)) = initial.C ∧
    (s (.stack 128)) = initial.D ∧
    ((((((s (.reg 1)) &&& (s (.reg 5))) + (s (.reg 2))) + 0x455a14ed)).rotateLeft 20 + (s (.reg 1)))
      = (operation G X[8] 0x455a14ed 20 working).B ∧
    (s (.reg 1)) = (operation G X[8] 0x455a14ed 20 working).C ∧
    (s (.reg 3)) = X[5] ∧
    (((s (.reg 5)) + (s (.stack 20))) + ((~~~(s (.reg 12))) &&& (s (.reg 1)))) = (((operation G X[8]
      0x455a14ed 20 working).A + X[13]) + ((~~~(operation G X[8] 0x455a14ed 20 working).D) &&&
      (operation G X[8] 0x455a14ed 20 working).C)) ∧
    (s (.reg 7)) = X[4] ∧
    (s (.reg 9)) = X[3] ∧
    (s (.stack 20)) = X[13] ∧
    (s (.reg 12)) = (operation G X[8] 0x455a14ed 20 working).D ∧
    (s (.reg 14)) = X[8]
  simp only [operation, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, true_and, and_true]
  md5_word_arithmetic

def Invariant29 (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) : Prop :=
  s (.stack 4) = X[9] ∧
  s (.stack 8) = initial.B ∧
  s (.stack 20) = X[13] ∧
  s (.stack 24) = X[8] ∧
  s (.stack 28) = X[4] ∧
  s (.stack 32) = X[11] ∧
  s (.stack 36) = X[14] ∧
  s (.stack 40) = X[10] ∧
  s (.stack 44) = X[12] ∧
  s (.stack 48) = X[15] ∧
  s (.stack 52) = X[7] ∧
  s (.stack 56) = X[6] ∧
  s (.stack 60) = initial.A ∧
  s (.stack 64) = X[5] ∧
  s (.stack 72) = X[3] ∧
  s (.stack 80) = X[1] ∧
  s (.stack 88) = X[0] ∧
  s (.stack 120) = initial.C ∧
  s (.stack 128) = initial.D ∧
  s (.reg 0) = working.C ∧
  s (.reg 1) = working.D ∧
  s (.reg 3) = X[5] ∧
  s (.reg 5) = working.B ∧
  s (.reg 7) = X[4] ∧
  s (.reg 9) = X[3] ∧
  s (.reg 10) = X[13] ∧
  s (.reg 12) = ((working.A + X[2]) + ((~~~working.D) &&& working.C)) ∧
  s (.reg 13) = X[2] ∧
  s (.reg 14) = X[8]

def segment29 : List WordInstruction := [
  .mov (.reg 2) (.location (.reg 0)),
  .and (.reg 2) (.location (.reg 12)),
  .add (.reg 5) (.location (.reg 2)),
  .add (.reg 5) (.immediate 0xa9e3e905),
  .mov (.reg 2) (.location (.reg 1)),
  .not (.reg 2),
  .and (.reg 2) (.location (.reg 0)),
  .mov (.reg 13) (.location (.stack 112)),
  .add (.reg 12) (.location (.reg 13)),
  .add (.reg 12) (.location (.reg 2)),
  .rol (.reg 5) 5,
  .add (.reg 5) (.location (.reg 0))]

theorem segment29_correct (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) (h : Invariant28 initial X working s) :
    Invariant29 initial X (operation G X[13] 0xa9e3e905 5 working) (executeWords segment29 s) := by
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
    (s (.stack 44)) = X[12] ∧
    (s (.stack 48)) = X[15] ∧
    (s (.stack 52)) = X[7] ∧
    (s (.stack 56)) = X[6] ∧
    (s (.stack 60)) = initial.A ∧
    (s (.stack 64)) = X[5] ∧
    (s (.stack 72)) = X[3] ∧
    (s (.stack 80)) = X[1] ∧
    (s (.stack 88)) = X[0] ∧
    (s (.stack 120)) = initial.C ∧
    (s (.stack 128)) = initial.D ∧
    (s (.reg 0)) = (operation G X[13] 0xa9e3e905 5 working).C ∧
    (s (.reg 1)) = (operation G X[13] 0xa9e3e905 5 working).D ∧
    (s (.reg 3)) = X[5] ∧
    (((((s (.reg 5)) + ((s (.reg 0)) &&& (s (.reg 12)))) + 0xa9e3e905)).rotateLeft 5 + (s (.reg 0)))
      = (operation G X[13] 0xa9e3e905 5 working).B ∧
    (s (.reg 7)) = X[4] ∧
    (s (.reg 9)) = X[3] ∧
    (s (.reg 10)) = X[13] ∧
    (((s (.reg 12)) + (s (.stack 112))) + ((~~~(s (.reg 1))) &&& (s (.reg 0)))) = (((operation G
      X[13] 0xa9e3e905 5 working).A + X[2]) + ((~~~(operation G X[13] 0xa9e3e905 5 working).D) &&&
      (operation G X[13] 0xa9e3e905 5 working).C)) ∧
    (s (.stack 112)) = X[2] ∧
    (s (.reg 14)) = X[8]
  simp only [operation, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, true_and, and_true]
  md5_word_arithmetic

def Invariant30 (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) : Prop :=
  s (.stack 4) = X[9] ∧
  s (.stack 8) = initial.B ∧
  s (.stack 20) = X[13] ∧
  s (.stack 24) = X[8] ∧
  s (.stack 28) = X[4] ∧
  s (.stack 32) = X[11] ∧
  s (.stack 36) = X[14] ∧
  s (.stack 40) = X[10] ∧
  s (.stack 44) = X[12] ∧
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
  s (.reg 1) = ((working.A + X[7]) + ((~~~working.D) &&& working.C)) ∧
  s (.reg 2) = working.B ∧
  s (.reg 3) = X[5] ∧
  s (.reg 5) = working.C ∧
  s (.reg 7) = X[4] ∧
  s (.reg 8) = X[7] ∧
  s (.reg 9) = X[3] ∧
  s (.reg 10) = X[13] ∧
  s (.reg 13) = X[2] ∧
  s (.reg 14) = X[8]

def segment30 : List WordInstruction := [
  .mov (.reg 2) (.location (.reg 5)),
  .and (.reg 2) (.location (.reg 1)),
  .add (.reg 2) (.location (.reg 12)),
  .add (.reg 2) (.immediate 0xfcefa3f8),
  .mov (.reg 15) (.location (.reg 0)),
  .not (.reg 15),
  .and (.reg 15) (.location (.reg 5)),
  .mov (.reg 8) (.location (.stack 52)),
  .add (.reg 1) (.location (.reg 8)),
  .add (.reg 1) (.location (.reg 15)),
  .rol (.reg 2) 9,
  .add (.reg 2) (.location (.reg 5))]

theorem segment30_correct (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) (h : Invariant29 initial X working s) :
    Invariant30 initial X (operation G X[2] 0xfcefa3f8 9 working) (executeWords segment30 s) := by
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
    (s (.stack 44)) = X[12] ∧
    (s (.stack 48)) = X[15] ∧
    (s (.stack 56)) = X[6] ∧
    (s (.stack 60)) = initial.A ∧
    (s (.stack 64)) = X[5] ∧
    (s (.stack 72)) = X[3] ∧
    (s (.stack 80)) = X[1] ∧
    (s (.stack 88)) = X[0] ∧
    (s (.stack 120)) = initial.C ∧
    (s (.stack 128)) = initial.D ∧
    (s (.reg 0)) = (operation G X[2] 0xfcefa3f8 9 working).D ∧
    (((s (.reg 1)) + (s (.stack 52))) + ((~~~(s (.reg 0))) &&& (s (.reg 5)))) = (((operation G X[2]
      0xfcefa3f8 9 working).A + X[7]) + ((~~~(operation G X[2] 0xfcefa3f8 9 working).D) &&&
      (operation G X[2] 0xfcefa3f8 9 working).C)) ∧
    ((((((s (.reg 5)) &&& (s (.reg 1))) + (s (.reg 12))) + 0xfcefa3f8)).rotateLeft 9 + (s (.reg 5)))
      = (operation G X[2] 0xfcefa3f8 9 working).B ∧
    (s (.reg 3)) = X[5] ∧
    (s (.reg 5)) = (operation G X[2] 0xfcefa3f8 9 working).C ∧
    (s (.reg 7)) = X[4] ∧
    (s (.stack 52)) = X[7] ∧
    (s (.reg 9)) = X[3] ∧
    (s (.reg 10)) = X[13] ∧
    (s (.reg 13)) = X[2] ∧
    (s (.reg 14)) = X[8]
  simp only [operation, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, true_and, and_true]
  md5_word_arithmetic

def Invariant31 (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) : Prop :=
  s (.stack 4) = X[9] ∧
  s (.stack 8) = initial.B ∧
  s (.stack 20) = X[13] ∧
  s (.stack 24) = X[8] ∧
  s (.stack 28) = X[4] ∧
  s (.stack 32) = X[11] ∧
  s (.stack 36) = X[14] ∧
  s (.stack 40) = X[10] ∧
  s (.stack 44) = X[12] ∧
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
  s (.reg 1) = working.B ∧
  s (.reg 2) = working.C ∧
  s (.reg 3) = X[5] ∧
  s (.reg 5) = working.D ∧
  s (.reg 7) = X[4] ∧
  s (.reg 8) = X[7] ∧
  s (.reg 9) = X[3] ∧
  s (.reg 10) = X[13] ∧
  s (.reg 13) = X[2] ∧
  s (.reg 14) = X[8]

def segment31 : List WordInstruction := [
  .mov (.reg 15) (.location (.reg 2)),
  .and (.reg 15) (.location (.reg 0)),
  .add (.reg 1) (.location (.reg 15)),
  .add (.reg 1) (.immediate 0x676f02d9),
  .rol (.reg 1) 14,
  .add (.reg 1) (.location (.reg 2))]

theorem segment31_correct (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) (h : Invariant30 initial X working s) :
    Invariant31 initial X (operation G X[7] 0x676f02d9 14 working) (executeWords segment31 s) := by
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
    (s (.stack 44)) = X[12] ∧
    (s (.stack 48)) = X[15] ∧
    (s (.stack 56)) = X[6] ∧
    (s (.stack 60)) = initial.A ∧
    (s (.stack 64)) = X[5] ∧
    (s (.stack 72)) = X[3] ∧
    (s (.stack 80)) = X[1] ∧
    (s (.stack 88)) = X[0] ∧
    (s (.stack 120)) = initial.C ∧
    (s (.stack 128)) = initial.D ∧
    (s (.reg 0)) = (operation G X[7] 0x676f02d9 14 working).A ∧
    (((((s (.reg 1)) + ((s (.reg 2)) &&& (s (.reg 0)))) + 0x676f02d9)).rotateLeft 14 + (s (.reg 2)))
      = (operation G X[7] 0x676f02d9 14 working).B ∧
    (s (.reg 2)) = (operation G X[7] 0x676f02d9 14 working).C ∧
    (s (.reg 3)) = X[5] ∧
    (s (.reg 5)) = (operation G X[7] 0x676f02d9 14 working).D ∧
    (s (.reg 7)) = X[4] ∧
    (s (.reg 8)) = X[7] ∧
    (s (.reg 9)) = X[3] ∧
    (s (.reg 10)) = X[13] ∧
    (s (.reg 13)) = X[2] ∧
    (s (.reg 14)) = X[8]
  simp only [operation, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, true_and, and_true]
  md5_word_arithmetic

def Invariant32 (initial : Buffer) (X : Vector (BitVec 32) 16)
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
  s (.reg 1) = working.C ∧
  s (.reg 2) = working.D ∧
  s (.reg 5) = working.B ∧
  s (.reg 7) = X[4] ∧
  s (.reg 8) = X[7] ∧
  s (.reg 9) = X[3] ∧
  s (.reg 10) = X[13] ∧
  s (.reg 11) = X[12] ∧
  s (.reg 12) = (X[5] + working.A) ∧
  s (.reg 13) = X[2] ∧
  s (.reg 14) = X[8]

def segment32 : List WordInstruction := [
  .mov (.reg 15) (.location (.reg 1)),
  .and (.reg 15) (.location (.reg 5)),
  .lea (.reg 12) (.reg 3) (.reg 5),
  .not (.reg 5),
  .mov (.reg 11) (.location (.stack 44)),
  .add (.reg 0) (.location (.reg 11)),
  .and (.reg 5) (.location (.reg 2)),
  .add (.reg 0) (.location (.reg 5)),
  .lea (.reg 5) (.reg 15) (.reg 0),
  .add (.reg 5) (.immediate 0x8d2a4c8a),
  .rol (.reg 5) 20,
  .add (.reg 5) (.location (.reg 1))]

theorem segment32_correct (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) (h : Invariant31 initial X working s) :
    Invariant32 initial X (operation G X[12] 0x8d2a4c8a 20 working) (executeWords segment32 s) := by
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
    (s (.reg 1)) = (operation G X[12] 0x8d2a4c8a 20 working).C ∧
    (s (.reg 2)) = (operation G X[12] 0x8d2a4c8a 20 working).D ∧
    ((((((s (.reg 1)) &&& (s (.reg 5))) + (((s (.reg 0)) + (s (.stack 44))) + ((~~~(s (.reg 5))) &&&
      (s (.reg 2))))) + 0x8d2a4c8a)).rotateLeft 20 + (s (.reg 1))) = (operation G X[12] 0x8d2a4c8a
      20 working).B ∧
    (s (.reg 7)) = X[4] ∧
    (s (.reg 8)) = X[7] ∧
    (s (.reg 9)) = X[3] ∧
    (s (.reg 10)) = X[13] ∧
    (s (.stack 44)) = X[12] ∧
    ((s (.reg 3)) + (s (.reg 5))) = (X[5] + (operation G X[12] 0x8d2a4c8a 20 working).A) ∧
    (s (.reg 13)) = X[2] ∧
    (s (.reg 14)) = X[8]
  simp only [operation, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, true_and, and_true]
  md5_word_arithmetic

end Md5.Proofs.Block.Rounds
