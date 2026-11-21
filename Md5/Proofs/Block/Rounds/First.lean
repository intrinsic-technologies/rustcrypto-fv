import Md5.Proofs.Block.Rounds.Word

namespace Md5.Proofs.Block.Rounds

open Standards.RFC.MD5

def Invariant0 (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) : Prop :=
  working.A = initial.A ∧
  working.B = initial.B ∧
  working.C = initial.C ∧
  working.D = initial.D ∧
  s (.reg 0) = initial.D ∧
  s (.reg 1) = initial.A ∧
  s (.reg 2) = initial.C ∧
  s (.reg 8) = initial.B ∧
  s (.input 0) = X[0] ∧
  s (.input 1) = X[1] ∧
  s (.input 2) = X[2] ∧
  s (.input 3) = X[3] ∧
  s (.input 4) = X[4] ∧
  s (.input 5) = X[5] ∧
  s (.input 6) = X[6] ∧
  s (.input 7) = X[7] ∧
  s (.input 8) = X[8] ∧
  s (.input 9) = X[9] ∧
  s (.input 10) = X[10] ∧
  s (.input 11) = X[11] ∧
  s (.input 12) = X[12] ∧
  s (.input 13) = X[13] ∧
  s (.input 14) = X[14] ∧
  s (.input 15) = X[15]

def Invariant1 (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) : Prop :=
  working.A = initial.D ∧
  working.C = initial.B ∧
  working.D = initial.C ∧
  s (.stack 8) = initial.B ∧
  s (.stack 60) = initial.A ∧
  s (.stack 88) = X[0] ∧
  s (.stack 128) = initial.D ∧
  s (.reg 0) = working.B ∧
  s (.reg 3) = X[1] ∧
  s (.reg 7) = initial.C ∧
  s (.reg 8) = initial.D ∧
  s (.input 2) = X[2] ∧
  s (.input 3) = X[3] ∧
  s (.input 4) = X[4] ∧
  s (.input 5) = X[5] ∧
  s (.input 6) = X[6] ∧
  s (.input 7) = X[7] ∧
  s (.input 8) = X[8] ∧
  s (.input 9) = X[9] ∧
  s (.input 10) = X[10] ∧
  s (.input 11) = X[11] ∧
  s (.input 12) = X[12] ∧
  s (.input 13) = X[13] ∧
  s (.input 14) = X[14] ∧
  s (.input 15) = X[15]

def segment1 : List WordInstruction := [
  .mov (.stack 8) (.location (.reg 8)),
  .mov (.reg 7) (.location (.reg 2)),
  .mov (.reg 2) (.location (.reg 0)),
  .mov (.reg 9) (.location (.input 0)),
  .mov (.stack 88) (.location (.reg 9)),
  .mov (.reg 0) (.location (.reg 7)),
  .xor (.reg 0) (.location (.reg 2)),
  .mov (.stack 60) (.location (.reg 1)),
  .and (.reg 0) (.location (.reg 8)),
  .xor (.reg 0) (.location (.reg 2)),
  .mov (.reg 8) (.location (.reg 2)),
  .mov (.stack 128) (.location (.reg 2)),
  .add (.reg 0) (.location (.reg 1)),
  .mov (.reg 3) (.location (.input 1)),
  .add (.reg 0) (.location (.reg 9)),
  .add (.reg 0) (.immediate 0xd76aa478),
  .rol (.reg 0) 7,
  .add (.reg 0) (.location (.stack 8))]

theorem segment1_correct (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) (h : Invariant0 initial X working s) :
    Invariant1 initial X (operation F X[0] 0xd76aa478 7 working) (executeWords segment1 s) := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    h18, h19, h20, h21, h22, h23⟩
  with_unfolding_all change (operation F X[0] 0xd76aa478 7 working).A = initial.D ∧
    (operation F X[0] 0xd76aa478 7 working).C = initial.B ∧
    (operation F X[0] 0xd76aa478 7 working).D = initial.C ∧
    (s (.reg 8)) = initial.B ∧
    (s (.reg 1)) = initial.A ∧
    (s (.input 0)) = X[0] ∧
    (s (.reg 0)) = initial.D ∧
    (((((((((s (.reg 2)) ^^^ (s (.reg 0))) &&& (s (.reg 8))) ^^^ (s (.reg 0))) + (s (.reg 1))) + (s
      (.input 0))) + 0xd76aa478)).rotateLeft 7 + (s (.reg 8))) = (operation F X[0] 0xd76aa478 7
      working).B ∧
    (s (.input 1)) = X[1] ∧
    (s (.reg 2)) = initial.C ∧
    (s (.reg 0)) = initial.D ∧
    (s (.input 2)) = X[2] ∧
    (s (.input 3)) = X[3] ∧
    (s (.input 4)) = X[4] ∧
    (s (.input 5)) = X[5] ∧
    (s (.input 6)) = X[6] ∧
    (s (.input 7)) = X[7] ∧
    (s (.input 8)) = X[8] ∧
    (s (.input 9)) = X[9] ∧
    (s (.input 10)) = X[10] ∧
    (s (.input 11)) = X[11] ∧
    (s (.input 12)) = X[12] ∧
    (s (.input 13)) = X[13] ∧
    (s (.input 14)) = X[14] ∧
    (s (.input 15)) = X[15]
  simp only [operation, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18, h19, h20, h21, h22, h23, true_and, and_true]
  md5_word_arithmetic

def Invariant2 (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) : Prop :=
  working.A = initial.C ∧
  working.D = initial.B ∧
  s (.stack 8) = initial.B ∧
  s (.stack 60) = initial.A ∧
  s (.stack 80) = X[1] ∧
  s (.stack 88) = X[0] ∧
  s (.stack 112) = X[2] ∧
  s (.stack 120) = initial.C ∧
  s (.stack 128) = initial.D ∧
  s (.reg 0) = working.C ∧
  s (.reg 1) = working.B ∧
  s (.reg 3) = X[1] ∧
  s (.reg 8) = X[2] ∧
  s (.reg 9) = initial.C ∧
  s (.input 3) = X[3] ∧
  s (.input 4) = X[4] ∧
  s (.input 5) = X[5] ∧
  s (.input 6) = X[6] ∧
  s (.input 7) = X[7] ∧
  s (.input 8) = X[8] ∧
  s (.input 9) = X[9] ∧
  s (.input 10) = X[10] ∧
  s (.input 11) = X[11] ∧
  s (.input 12) = X[12] ∧
  s (.input 13) = X[13] ∧
  s (.input 14) = X[14] ∧
  s (.input 15) = X[15]

def segment2 : List WordInstruction := [
  .mov (.reg 1) (.location (.reg 0)),
  .mov (.reg 2) (.location (.reg 0)),
  .not (.reg 2),
  .and (.reg 1) (.location (.stack 8)),
  .and (.reg 2) (.location (.reg 7)),
  .mov (.reg 9) (.location (.reg 7)),
  .mov (.stack 120) (.location (.reg 7)),
  .mov (.stack 80) (.location (.reg 3)),
  .add (.reg 2) (.location (.reg 8)),
  .add (.reg 2) (.location (.reg 3)),
  .mov (.reg 8) (.location (.input 2)),
  .mov (.stack 112) (.location (.reg 8)),
  .add (.reg 1) (.location (.reg 2)),
  .add (.reg 1) (.immediate 0xe8c7b756),
  .rol (.reg 1) 12,
  .add (.reg 1) (.location (.reg 0))]

theorem segment2_correct (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) (h : Invariant1 initial X working s) :
    Invariant2 initial X (operation F X[1] 0xe8c7b756 12 working) (executeWords segment2 s) := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    h18, h19, h20, h21, h22, h23, h24⟩
  with_unfolding_all change (operation F X[1] 0xe8c7b756 12 working).A = initial.C ∧
    (operation F X[1] 0xe8c7b756 12 working).D = initial.B ∧
    (s (.stack 8)) = initial.B ∧
    (s (.stack 60)) = initial.A ∧
    (s (.reg 3)) = X[1] ∧
    (s (.stack 88)) = X[0] ∧
    (s (.input 2)) = X[2] ∧
    (s (.reg 7)) = initial.C ∧
    (s (.stack 128)) = initial.D ∧
    (s (.reg 0)) = (operation F X[1] 0xe8c7b756 12 working).C ∧
    ((((((s (.reg 0)) &&& (s (.stack 8))) + ((((~~~(s (.reg 0))) &&& (s (.reg 7))) + (s (.reg 8))) +
      (s (.reg 3)))) + 0xe8c7b756)).rotateLeft 12 + (s (.reg 0))) = (operation F X[1] 0xe8c7b756 12
      working).B ∧
    (s (.reg 3)) = X[1] ∧
    (s (.input 2)) = X[2] ∧
    (s (.reg 7)) = initial.C ∧
    (s (.input 3)) = X[3] ∧
    (s (.input 4)) = X[4] ∧
    (s (.input 5)) = X[5] ∧
    (s (.input 6)) = X[6] ∧
    (s (.input 7)) = X[7] ∧
    (s (.input 8)) = X[8] ∧
    (s (.input 9)) = X[9] ∧
    (s (.input 10)) = X[10] ∧
    (s (.input 11)) = X[11] ∧
    (s (.input 12)) = X[12] ∧
    (s (.input 13)) = X[13] ∧
    (s (.input 14)) = X[14] ∧
    (s (.input 15)) = X[15]
  simp only [operation, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18, h19, h20, h21, h22, h23, h24, true_and, and_true]
  md5_word_arithmetic

def Invariant3 (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) : Prop :=
  working.A = initial.B ∧
  s (.stack 8) = initial.B ∧
  s (.stack 60) = initial.A ∧
  s (.stack 72) = X[3] ∧
  s (.stack 80) = X[1] ∧
  s (.stack 88) = X[0] ∧
  s (.stack 112) = X[2] ∧
  s (.stack 120) = initial.C ∧
  s (.stack 128) = initial.D ∧
  s (.reg 0) = working.D ∧
  s (.reg 1) = working.C ∧
  s (.reg 2) = working.B ∧
  s (.reg 3) = X[1] ∧
  s (.reg 10) = X[3] ∧
  s (.input 4) = X[4] ∧
  s (.input 5) = X[5] ∧
  s (.input 6) = X[6] ∧
  s (.input 7) = X[7] ∧
  s (.input 8) = X[8] ∧
  s (.input 9) = X[9] ∧
  s (.input 10) = X[10] ∧
  s (.input 11) = X[11] ∧
  s (.input 12) = X[12] ∧
  s (.input 13) = X[13] ∧
  s (.input 14) = X[14] ∧
  s (.input 15) = X[15]

def segment3 : List WordInstruction := [
  .mov (.reg 2) (.location (.reg 1)),
  .mov (.reg 7) (.location (.reg 1)),
  .not (.reg 7),
  .and (.reg 2) (.location (.reg 0)),
  .and (.reg 7) (.location (.stack 8)),
  .add (.reg 8) (.location (.reg 9)),
  .add (.reg 7) (.location (.reg 8)),
  .mov (.reg 10) (.location (.input 3)),
  .mov (.stack 72) (.location (.reg 10)),
  .add (.reg 2) (.location (.reg 7)),
  .add (.reg 2) (.immediate 0x242070db),
  .rol (.reg 2) 17,
  .add (.reg 2) (.location (.reg 1))]

theorem segment3_correct (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) (h : Invariant2 initial X working s) :
    Invariant3 initial X (operation F X[2] 0x242070db 17 working) (executeWords segment3 s) := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    h18, h19, h20, h21, h22, h23, h24, h25, h26⟩
  with_unfolding_all change (operation F X[2] 0x242070db 17 working).A = initial.B ∧
    (s (.stack 8)) = initial.B ∧
    (s (.stack 60)) = initial.A ∧
    (s (.input 3)) = X[3] ∧
    (s (.stack 80)) = X[1] ∧
    (s (.stack 88)) = X[0] ∧
    (s (.stack 112)) = X[2] ∧
    (s (.stack 120)) = initial.C ∧
    (s (.stack 128)) = initial.D ∧
    (s (.reg 0)) = (operation F X[2] 0x242070db 17 working).D ∧
    (s (.reg 1)) = (operation F X[2] 0x242070db 17 working).C ∧
    ((((((s (.reg 1)) &&& (s (.reg 0))) + (((~~~(s (.reg 1))) &&& (s (.stack 8))) + ((s (.reg 8)) +
      (s (.reg 9))))) + 0x242070db)).rotateLeft 17 + (s (.reg 1))) = (operation F X[2] 0x242070db 17
      working).B ∧
    (s (.reg 3)) = X[1] ∧
    (s (.input 3)) = X[3] ∧
    (s (.input 4)) = X[4] ∧
    (s (.input 5)) = X[5] ∧
    (s (.input 6)) = X[6] ∧
    (s (.input 7)) = X[7] ∧
    (s (.input 8)) = X[8] ∧
    (s (.input 9)) = X[9] ∧
    (s (.input 10)) = X[10] ∧
    (s (.input 11)) = X[11] ∧
    (s (.input 12)) = X[12] ∧
    (s (.input 13)) = X[13] ∧
    (s (.input 14)) = X[14] ∧
    (s (.input 15)) = X[15]
  simp only [operation, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, true_and, and_true]
  md5_word_arithmetic

def Invariant4 (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) : Prop :=
  s (.stack 8) = initial.B ∧
  s (.stack 28) = X[4] ∧
  s (.stack 60) = initial.A ∧
  s (.stack 72) = X[3] ∧
  s (.stack 80) = X[1] ∧
  s (.stack 88) = X[0] ∧
  s (.stack 112) = X[2] ∧
  s (.stack 120) = initial.C ∧
  s (.stack 128) = initial.D ∧
  s (.reg 0) = working.A ∧
  s (.reg 1) = working.D ∧
  s (.reg 2) = working.C ∧
  s (.reg 3) = X[1] ∧
  s (.reg 7) = working.B ∧
  s (.reg 10) = X[4] ∧
  s (.input 5) = X[5] ∧
  s (.input 6) = X[6] ∧
  s (.input 7) = X[7] ∧
  s (.input 8) = X[8] ∧
  s (.input 9) = X[9] ∧
  s (.input 10) = X[10] ∧
  s (.input 11) = X[11] ∧
  s (.input 12) = X[12] ∧
  s (.input 13) = X[13] ∧
  s (.input 14) = X[14] ∧
  s (.input 15) = X[15]

def segment4 : List WordInstruction := [
  .mov (.reg 7) (.location (.reg 2)),
  .mov (.reg 8) (.location (.reg 2)),
  .not (.reg 8),
  .and (.reg 7) (.location (.reg 1)),
  .and (.reg 8) (.location (.reg 0)),
  .mov (.reg 9) (.location (.stack 8)),
  .add (.reg 9) (.location (.reg 10)),
  .add (.reg 8) (.location (.reg 9)),
  .mov (.reg 10) (.location (.input 4)),
  .mov (.stack 28) (.location (.reg 10)),
  .add (.reg 7) (.location (.reg 8)),
  .add (.reg 7) (.immediate 0xc1bdceee),
  .rol (.reg 7) 22,
  .add (.reg 7) (.location (.reg 2))]

theorem segment4_correct (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) (h : Invariant3 initial X working s) :
    Invariant4 initial X (operation F X[3] 0xc1bdceee 22 working) (executeWords segment4 s) := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    h18, h19, h20, h21, h22, h23, h24, h25⟩
  with_unfolding_all change (s (.stack 8)) = initial.B ∧
    (s (.input 4)) = X[4] ∧
    (s (.stack 60)) = initial.A ∧
    (s (.stack 72)) = X[3] ∧
    (s (.stack 80)) = X[1] ∧
    (s (.stack 88)) = X[0] ∧
    (s (.stack 112)) = X[2] ∧
    (s (.stack 120)) = initial.C ∧
    (s (.stack 128)) = initial.D ∧
    (s (.reg 0)) = (operation F X[3] 0xc1bdceee 22 working).A ∧
    (s (.reg 1)) = (operation F X[3] 0xc1bdceee 22 working).D ∧
    (s (.reg 2)) = (operation F X[3] 0xc1bdceee 22 working).C ∧
    (s (.reg 3)) = X[1] ∧
    ((((((s (.reg 2)) &&& (s (.reg 1))) + (((~~~(s (.reg 2))) &&& (s (.reg 0))) + ((s (.stack 8)) +
      (s (.reg 10))))) + 0xc1bdceee)).rotateLeft 22 + (s (.reg 2))) = (operation F X[3] 0xc1bdceee
      22 working).B ∧
    (s (.input 4)) = X[4] ∧
    (s (.input 5)) = X[5] ∧
    (s (.input 6)) = X[6] ∧
    (s (.input 7)) = X[7] ∧
    (s (.input 8)) = X[8] ∧
    (s (.input 9)) = X[9] ∧
    (s (.input 10)) = X[10] ∧
    (s (.input 11)) = X[11] ∧
    (s (.input 12)) = X[12] ∧
    (s (.input 13)) = X[13] ∧
    (s (.input 14)) = X[14] ∧
    (s (.input 15)) = X[15]
  simp only [operation, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18, h19, h20, h21, h22, h23, h24, h25, true_and, and_true]
  md5_word_arithmetic

def Invariant5 (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) : Prop :=
  s (.stack 8) = initial.B ∧
  s (.stack 28) = X[4] ∧
  s (.stack 60) = initial.A ∧
  s (.stack 64) = X[5] ∧
  s (.stack 72) = X[3] ∧
  s (.stack 80) = X[1] ∧
  s (.stack 88) = X[0] ∧
  s (.stack 112) = X[2] ∧
  s (.stack 120) = initial.C ∧
  s (.stack 128) = initial.D ∧
  s (.reg 0) = working.B ∧
  s (.reg 1) = working.A ∧
  s (.reg 2) = working.D ∧
  s (.reg 3) = X[1] ∧
  s (.reg 7) = working.C ∧
  s (.reg 10) = X[5] ∧
  s (.input 6) = X[6] ∧
  s (.input 7) = X[7] ∧
  s (.input 8) = X[8] ∧
  s (.input 9) = X[9] ∧
  s (.input 10) = X[10] ∧
  s (.input 11) = X[11] ∧
  s (.input 12) = X[12] ∧
  s (.input 13) = X[13] ∧
  s (.input 14) = X[14] ∧
  s (.input 15) = X[15]

def segment5 : List WordInstruction := [
  .mov (.reg 8) (.location (.reg 7)),
  .mov (.reg 9) (.location (.reg 7)),
  .not (.reg 9),
  .and (.reg 8) (.location (.reg 2)),
  .and (.reg 9) (.location (.reg 1)),
  .add (.reg 0) (.location (.reg 10)),
  .add (.reg 0) (.location (.reg 9)),
  .mov (.reg 10) (.location (.input 5)),
  .mov (.stack 64) (.location (.reg 10)),
  .add (.reg 0) (.location (.reg 8)),
  .add (.reg 0) (.immediate 0xf57c0faf),
  .rol (.reg 0) 7,
  .add (.reg 0) (.location (.reg 7))]

theorem segment5_correct (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) (h : Invariant4 initial X working s) :
    Invariant5 initial X (operation F X[4] 0xf57c0faf 7 working) (executeWords segment5 s) := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    h18, h19, h20, h21, h22, h23, h24, h25⟩
  with_unfolding_all change (s (.stack 8)) = initial.B ∧
    (s (.stack 28)) = X[4] ∧
    (s (.stack 60)) = initial.A ∧
    (s (.input 5)) = X[5] ∧
    (s (.stack 72)) = X[3] ∧
    (s (.stack 80)) = X[1] ∧
    (s (.stack 88)) = X[0] ∧
    (s (.stack 112)) = X[2] ∧
    (s (.stack 120)) = initial.C ∧
    (s (.stack 128)) = initial.D ∧
    (((((((s (.reg 0)) + (s (.reg 10))) + ((~~~(s (.reg 7))) &&& (s (.reg 1)))) + ((s (.reg 7)) &&&
      (s (.reg 2)))) + 0xf57c0faf)).rotateLeft 7 + (s (.reg 7))) = (operation F X[4] 0xf57c0faf 7
      working).B ∧
    (s (.reg 1)) = (operation F X[4] 0xf57c0faf 7 working).A ∧
    (s (.reg 2)) = (operation F X[4] 0xf57c0faf 7 working).D ∧
    (s (.reg 3)) = X[1] ∧
    (s (.reg 7)) = (operation F X[4] 0xf57c0faf 7 working).C ∧
    (s (.input 5)) = X[5] ∧
    (s (.input 6)) = X[6] ∧
    (s (.input 7)) = X[7] ∧
    (s (.input 8)) = X[8] ∧
    (s (.input 9)) = X[9] ∧
    (s (.input 10)) = X[10] ∧
    (s (.input 11)) = X[11] ∧
    (s (.input 12)) = X[12] ∧
    (s (.input 13)) = X[13] ∧
    (s (.input 14)) = X[14] ∧
    (s (.input 15)) = X[15]
  simp only [operation, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18, h19, h20, h21, h22, h23, h24, h25, true_and, and_true]
  md5_word_arithmetic

def Invariant6 (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) : Prop :=
  s (.stack 8) = initial.B ∧
  s (.stack 28) = X[4] ∧
  s (.stack 60) = initial.A ∧
  s (.stack 64) = X[5] ∧
  s (.stack 72) = X[3] ∧
  s (.stack 80) = X[1] ∧
  s (.stack 88) = X[0] ∧
  s (.stack 112) = X[2] ∧
  s (.stack 120) = initial.C ∧
  s (.stack 128) = initial.D ∧
  s (.reg 0) = working.C ∧
  s (.reg 2) = working.A ∧
  s (.reg 3) = X[1] ∧
  s (.reg 7) = working.D ∧
  s (.reg 8) = working.B ∧
  s (.reg 9) = X[6] ∧
  s (.input 7) = X[7] ∧
  s (.input 8) = X[8] ∧
  s (.input 9) = X[9] ∧
  s (.input 10) = X[10] ∧
  s (.input 11) = X[11] ∧
  s (.input 12) = X[12] ∧
  s (.input 13) = X[13] ∧
  s (.input 14) = X[14] ∧
  s (.input 15) = X[15]

def segment6 : List WordInstruction := [
  .mov (.reg 8) (.location (.reg 0)),
  .mov (.reg 9) (.location (.reg 0)),
  .not (.reg 9),
  .and (.reg 8) (.location (.reg 7)),
  .and (.reg 9) (.location (.reg 2)),
  .add (.reg 1) (.location (.reg 10)),
  .add (.reg 1) (.location (.reg 9)),
  .mov (.reg 9) (.location (.input 6)),
  .add (.reg 8) (.location (.reg 1)),
  .add (.reg 8) (.immediate 0x4787c62a),
  .rol (.reg 8) 12,
  .add (.reg 8) (.location (.reg 0))]

theorem segment6_correct (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) (h : Invariant5 initial X working s) :
    Invariant6 initial X (operation F X[5] 0x4787c62a 12 working) (executeWords segment6 s) := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    h18, h19, h20, h21, h22, h23, h24, h25⟩
  with_unfolding_all change (s (.stack 8)) = initial.B ∧
    (s (.stack 28)) = X[4] ∧
    (s (.stack 60)) = initial.A ∧
    (s (.stack 64)) = X[5] ∧
    (s (.stack 72)) = X[3] ∧
    (s (.stack 80)) = X[1] ∧
    (s (.stack 88)) = X[0] ∧
    (s (.stack 112)) = X[2] ∧
    (s (.stack 120)) = initial.C ∧
    (s (.stack 128)) = initial.D ∧
    (s (.reg 0)) = (operation F X[5] 0x4787c62a 12 working).C ∧
    (s (.reg 2)) = (operation F X[5] 0x4787c62a 12 working).A ∧
    (s (.reg 3)) = X[1] ∧
    (s (.reg 7)) = (operation F X[5] 0x4787c62a 12 working).D ∧
    ((((((s (.reg 0)) &&& (s (.reg 7))) + (((s (.reg 1)) + (s (.reg 10))) + ((~~~(s (.reg 0))) &&&
      (s (.reg 2))))) + 0x4787c62a)).rotateLeft 12 + (s (.reg 0))) = (operation F X[5] 0x4787c62a 12
      working).B ∧
    (s (.input 6)) = X[6] ∧
    (s (.input 7)) = X[7] ∧
    (s (.input 8)) = X[8] ∧
    (s (.input 9)) = X[9] ∧
    (s (.input 10)) = X[10] ∧
    (s (.input 11)) = X[11] ∧
    (s (.input 12)) = X[12] ∧
    (s (.input 13)) = X[13] ∧
    (s (.input 14)) = X[14] ∧
    (s (.input 15)) = X[15]
  simp only [operation, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18, h19, h20, h21, h22, h23, h24, h25, true_and, and_true]
  md5_word_arithmetic

def Invariant7 (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) : Prop :=
  s (.stack 8) = initial.B ∧
  s (.stack 28) = X[4] ∧
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
  s (.reg 1) = working.B ∧
  s (.reg 3) = X[1] ∧
  s (.reg 7) = working.A ∧
  s (.reg 8) = working.C ∧
  s (.reg 9) = X[6] ∧
  s (.input 7) = X[7] ∧
  s (.input 8) = X[8] ∧
  s (.input 9) = X[9] ∧
  s (.input 10) = X[10] ∧
  s (.input 11) = X[11] ∧
  s (.input 12) = X[12] ∧
  s (.input 13) = X[13] ∧
  s (.input 14) = X[14] ∧
  s (.input 15) = X[15]

def segment7 : List WordInstruction := [
  .mov (.reg 1) (.location (.reg 0)),
  .xor (.reg 1) (.location (.reg 7)),
  .and (.reg 1) (.location (.reg 8)),
  .xor (.reg 1) (.location (.reg 7)),
  .add (.reg 2) (.location (.reg 9)),
  .mov (.stack 56) (.location (.reg 9)),
  .add (.reg 1) (.location (.reg 2)),
  .add (.reg 1) (.immediate 0xa8304613),
  .rol (.reg 1) 17,
  .add (.reg 1) (.location (.reg 8))]

theorem segment7_correct (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) (h : Invariant6 initial X working s) :
    Invariant7 initial X (operation F X[6] 0xa8304613 17 working) (executeWords segment7 s) := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    h18, h19, h20, h21, h22, h23, h24⟩
  with_unfolding_all change (s (.stack 8)) = initial.B ∧
    (s (.stack 28)) = X[4] ∧
    (s (.reg 9)) = X[6] ∧
    (s (.stack 60)) = initial.A ∧
    (s (.stack 64)) = X[5] ∧
    (s (.stack 72)) = X[3] ∧
    (s (.stack 80)) = X[1] ∧
    (s (.stack 88)) = X[0] ∧
    (s (.stack 112)) = X[2] ∧
    (s (.stack 120)) = initial.C ∧
    (s (.stack 128)) = initial.D ∧
    (s (.reg 0)) = (operation F X[6] 0xa8304613 17 working).D ∧
    ((((((((s (.reg 0)) ^^^ (s (.reg 7))) &&& (s (.reg 8))) ^^^ (s (.reg 7))) + ((s (.reg 2)) + (s
      (.reg 9)))) + 0xa8304613)).rotateLeft 17 + (s (.reg 8))) = (operation F X[6] 0xa8304613 17
      working).B ∧
    (s (.reg 3)) = X[1] ∧
    (s (.reg 7)) = (operation F X[6] 0xa8304613 17 working).A ∧
    (s (.reg 8)) = (operation F X[6] 0xa8304613 17 working).C ∧
    (s (.reg 9)) = X[6] ∧
    (s (.input 7)) = X[7] ∧
    (s (.input 8)) = X[8] ∧
    (s (.input 9)) = X[9] ∧
    (s (.input 10)) = X[10] ∧
    (s (.input 11)) = X[11] ∧
    (s (.input 12)) = X[12] ∧
    (s (.input 13)) = X[13] ∧
    (s (.input 14)) = X[14] ∧
    (s (.input 15)) = X[15]
  simp only [operation, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18, h19, h20, h21, h22, h23, h24, true_and, and_true]
  md5_word_arithmetic

def Invariant8 (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) : Prop :=
  s (.stack 8) = initial.B ∧
  s (.stack 28) = X[4] ∧
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
  s (.reg 0) = working.A ∧
  s (.reg 1) = working.C ∧
  s (.reg 2) = working.B ∧
  s (.reg 3) = X[1] ∧
  s (.reg 8) = working.D ∧
  s (.reg 9) = X[6] ∧
  s (.input 8) = X[8] ∧
  s (.input 9) = X[9] ∧
  s (.input 10) = X[10] ∧
  s (.input 11) = X[11] ∧
  s (.input 12) = X[12] ∧
  s (.input 13) = X[13] ∧
  s (.input 14) = X[14] ∧
  s (.input 15) = X[15]

def segment8 : List WordInstruction := [
  .mov (.reg 2) (.location (.reg 8)),
  .xor (.reg 2) (.location (.reg 0)),
  .and (.reg 2) (.location (.reg 1)),
  .xor (.reg 2) (.location (.reg 0)),
  .mov (.reg 10) (.location (.input 7)),
  .mov (.stack 52) (.location (.reg 10)),
  .add (.reg 7) (.location (.reg 10)),
  .add (.reg 2) (.location (.reg 7)),
  .add (.reg 2) (.immediate 0xfd469501),
  .rol (.reg 2) 22,
  .add (.reg 2) (.location (.reg 1))]

theorem segment8_correct (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) (h : Invariant7 initial X working s) :
    Invariant8 initial X (operation F X[7] 0xfd469501 22 working) (executeWords segment8 s) := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    h18, h19, h20, h21, h22, h23, h24, h25⟩
  with_unfolding_all change (s (.stack 8)) = initial.B ∧
    (s (.stack 28)) = X[4] ∧
    (s (.input 7)) = X[7] ∧
    (s (.stack 56)) = X[6] ∧
    (s (.stack 60)) = initial.A ∧
    (s (.stack 64)) = X[5] ∧
    (s (.stack 72)) = X[3] ∧
    (s (.stack 80)) = X[1] ∧
    (s (.stack 88)) = X[0] ∧
    (s (.stack 112)) = X[2] ∧
    (s (.stack 120)) = initial.C ∧
    (s (.stack 128)) = initial.D ∧
    (s (.reg 0)) = (operation F X[7] 0xfd469501 22 working).A ∧
    (s (.reg 1)) = (operation F X[7] 0xfd469501 22 working).C ∧
    ((((((((s (.reg 8)) ^^^ (s (.reg 0))) &&& (s (.reg 1))) ^^^ (s (.reg 0))) + ((s (.reg 7)) + (s
      (.input 7)))) + 0xfd469501)).rotateLeft 22 + (s (.reg 1))) = (operation F X[7] 0xfd469501 22
      working).B ∧
    (s (.reg 3)) = X[1] ∧
    (s (.reg 8)) = (operation F X[7] 0xfd469501 22 working).D ∧
    (s (.reg 9)) = X[6] ∧
    (s (.input 8)) = X[8] ∧
    (s (.input 9)) = X[9] ∧
    (s (.input 10)) = X[10] ∧
    (s (.input 11)) = X[11] ∧
    (s (.input 12)) = X[12] ∧
    (s (.input 13)) = X[13] ∧
    (s (.input 14)) = X[14] ∧
    (s (.input 15)) = X[15]
  simp only [operation, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18, h19, h20, h21, h22, h23, h24, h25, true_and, and_true]
  md5_word_arithmetic

def Invariant9 (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) : Prop :=
  s (.stack 8) = initial.B ∧
  s (.stack 24) = X[8] ∧
  s (.stack 28) = X[4] ∧
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
  s (.reg 1) = working.D ∧
  s (.reg 2) = working.C ∧
  s (.reg 3) = X[1] ∧
  s (.reg 8) = working.A ∧
  s (.reg 9) = X[6] ∧
  s (.input 9) = X[9] ∧
  s (.input 10) = X[10] ∧
  s (.input 11) = X[11] ∧
  s (.input 12) = X[12] ∧
  s (.input 13) = X[13] ∧
  s (.input 14) = X[14] ∧
  s (.input 15) = X[15]

def segment9 : List WordInstruction := [
  .mov (.reg 7) (.location (.reg 1)),
  .xor (.reg 7) (.location (.reg 8)),
  .and (.reg 7) (.location (.reg 2)),
  .xor (.reg 7) (.location (.reg 8)),
  .mov (.reg 10) (.location (.input 8)),
  .mov (.stack 24) (.location (.reg 10)),
  .add (.reg 0) (.location (.reg 10)),
  .add (.reg 0) (.location (.reg 7)),
  .add (.reg 0) (.immediate 0x698098d8),
  .rol (.reg 0) 7,
  .add (.reg 0) (.location (.reg 2))]

theorem segment9_correct (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) (h : Invariant8 initial X working s) :
    Invariant9 initial X (operation F X[8] 0x698098d8 7 working) (executeWords segment9 s) := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    h18, h19, h20, h21, h22, h23, h24, h25⟩
  with_unfolding_all change (s (.stack 8)) = initial.B ∧
    (s (.input 8)) = X[8] ∧
    (s (.stack 28)) = X[4] ∧
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
    ((((((s (.reg 0)) + (s (.input 8))) + ((((s (.reg 1)) ^^^ (s (.reg 8))) &&& (s (.reg 2))) ^^^ (s
      (.reg 8)))) + 0x698098d8)).rotateLeft 7 + (s (.reg 2))) = (operation F X[8] 0x698098d8 7
      working).B ∧
    (s (.reg 1)) = (operation F X[8] 0x698098d8 7 working).D ∧
    (s (.reg 2)) = (operation F X[8] 0x698098d8 7 working).C ∧
    (s (.reg 3)) = X[1] ∧
    (s (.reg 8)) = (operation F X[8] 0x698098d8 7 working).A ∧
    (s (.reg 9)) = X[6] ∧
    (s (.input 9)) = X[9] ∧
    (s (.input 10)) = X[10] ∧
    (s (.input 11)) = X[11] ∧
    (s (.input 12)) = X[12] ∧
    (s (.input 13)) = X[13] ∧
    (s (.input 14)) = X[14] ∧
    (s (.input 15)) = X[15]
  simp only [operation, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18, h19, h20, h21, h22, h23, h24, h25, true_and, and_true]
  md5_word_arithmetic

def Invariant10 (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) : Prop :=
  s (.stack 4) = X[9] ∧
  s (.stack 8) = initial.B ∧
  s (.stack 24) = X[8] ∧
  s (.stack 28) = X[4] ∧
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
  s (.reg 1) = working.A ∧
  s (.reg 2) = working.D ∧
  s (.reg 3) = X[1] ∧
  s (.reg 7) = working.B ∧
  s (.reg 9) = X[6] ∧
  s (.input 10) = X[10] ∧
  s (.input 11) = X[11] ∧
  s (.input 12) = X[12] ∧
  s (.input 13) = X[13] ∧
  s (.input 14) = X[14] ∧
  s (.input 15) = X[15]

def segment10 : List WordInstruction := [
  .mov (.reg 7) (.location (.reg 2)),
  .xor (.reg 7) (.location (.reg 1)),
  .and (.reg 7) (.location (.reg 0)),
  .xor (.reg 7) (.location (.reg 1)),
  .mov (.reg 10) (.location (.input 9)),
  .mov (.stack 4) (.location (.reg 10)),
  .add (.reg 8) (.location (.reg 10)),
  .add (.reg 7) (.location (.reg 8)),
  .add (.reg 7) (.immediate 0x8b44f7af),
  .rol (.reg 7) 12,
  .add (.reg 7) (.location (.reg 0))]

theorem segment10_correct (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) (h : Invariant9 initial X working s) :
    Invariant10 initial X (operation F X[9] 0x8b44f7af 12 working) (executeWords segment10 s) := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    h18, h19, h20, h21, h22, h23, h24, h25⟩
  with_unfolding_all change (s (.input 9)) = X[9] ∧
    (s (.stack 8)) = initial.B ∧
    (s (.stack 24)) = X[8] ∧
    (s (.stack 28)) = X[4] ∧
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
    (s (.reg 0)) = (operation F X[9] 0x8b44f7af 12 working).C ∧
    (s (.reg 1)) = (operation F X[9] 0x8b44f7af 12 working).A ∧
    (s (.reg 2)) = (operation F X[9] 0x8b44f7af 12 working).D ∧
    (s (.reg 3)) = X[1] ∧
    ((((((((s (.reg 2)) ^^^ (s (.reg 1))) &&& (s (.reg 0))) ^^^ (s (.reg 1))) + ((s (.reg 8)) + (s
      (.input 9)))) + 0x8b44f7af)).rotateLeft 12 + (s (.reg 0))) = (operation F X[9] 0x8b44f7af 12
      working).B ∧
    (s (.reg 9)) = X[6] ∧
    (s (.input 10)) = X[10] ∧
    (s (.input 11)) = X[11] ∧
    (s (.input 12)) = X[12] ∧
    (s (.input 13)) = X[13] ∧
    (s (.input 14)) = X[14] ∧
    (s (.input 15)) = X[15]
  simp only [operation, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18, h19, h20, h21, h22, h23, h24, h25, true_and, and_true]
  md5_word_arithmetic

def Invariant11 (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) : Prop :=
  s (.stack 4) = X[9] ∧
  s (.stack 8) = initial.B ∧
  s (.stack 24) = X[8] ∧
  s (.stack 28) = X[4] ∧
  s (.stack 40) = X[10] ∧
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
  s (.reg 1) = working.B ∧
  s (.reg 2) = working.A ∧
  s (.reg 3) = X[1] ∧
  s (.reg 7) = working.C ∧
  s (.reg 9) = X[6] ∧
  s (.reg 11) = X[10] ∧
  s (.input 11) = X[11] ∧
  s (.input 12) = X[12] ∧
  s (.input 13) = X[13] ∧
  s (.input 14) = X[14] ∧
  s (.input 15) = X[15]

def segment11 : List WordInstruction := [
  .mov (.reg 8) (.location (.reg 0)),
  .xor (.reg 8) (.location (.reg 2)),
  .and (.reg 8) (.location (.reg 7)),
  .xor (.reg 8) (.location (.reg 2)),
  .mov (.reg 11) (.location (.input 10)),
  .add (.reg 1) (.location (.reg 11)),
  .mov (.stack 40) (.location (.reg 11)),
  .add (.reg 1) (.location (.reg 8)),
  .add (.reg 1) (.immediate 0xffff5bb1),
  .rol (.reg 1) 17,
  .add (.reg 1) (.location (.reg 7))]

theorem segment11_correct (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) (h : Invariant10 initial X working s) :
    Invariant11 initial X (operation F X[10] 0xffff5bb1 17 working) (executeWords segment11 s) := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    h18, h19, h20, h21, h22, h23, h24, h25⟩
  with_unfolding_all change (s (.stack 4)) = X[9] ∧
    (s (.stack 8)) = initial.B ∧
    (s (.stack 24)) = X[8] ∧
    (s (.stack 28)) = X[4] ∧
    (s (.input 10)) = X[10] ∧
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
    (s (.reg 0)) = (operation F X[10] 0xffff5bb1 17 working).D ∧
    ((((((s (.reg 1)) + (s (.input 10))) + ((((s (.reg 0)) ^^^ (s (.reg 2))) &&& (s (.reg 7))) ^^^
      (s (.reg 2)))) + 0xffff5bb1)).rotateLeft 17 + (s (.reg 7))) = (operation F X[10] 0xffff5bb1 17
      working).B ∧
    (s (.reg 2)) = (operation F X[10] 0xffff5bb1 17 working).A ∧
    (s (.reg 3)) = X[1] ∧
    (s (.reg 7)) = (operation F X[10] 0xffff5bb1 17 working).C ∧
    (s (.reg 9)) = X[6] ∧
    (s (.input 10)) = X[10] ∧
    (s (.input 11)) = X[11] ∧
    (s (.input 12)) = X[12] ∧
    (s (.input 13)) = X[13] ∧
    (s (.input 14)) = X[14] ∧
    (s (.input 15)) = X[15]
  simp only [operation, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18, h19, h20, h21, h22, h23, h24, h25, true_and, and_true]
  md5_word_arithmetic

def Invariant12 (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) : Prop :=
  s (.stack 4) = X[9] ∧
  s (.stack 8) = initial.B ∧
  s (.stack 24) = X[8] ∧
  s (.stack 28) = X[4] ∧
  s (.stack 32) = X[11] ∧
  s (.stack 40) = X[10] ∧
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
  s (.reg 0) = working.A ∧
  s (.reg 1) = working.C ∧
  s (.reg 2) = working.B ∧
  s (.reg 3) = X[1] ∧
  s (.reg 7) = working.D ∧
  s (.reg 9) = X[6] ∧
  s (.reg 11) = X[10] ∧
  s (.reg 14) = X[11] ∧
  s (.input 12) = X[12] ∧
  s (.input 13) = X[13] ∧
  s (.input 14) = X[14] ∧
  s (.input 15) = X[15]

def segment12 : List WordInstruction := [
  .mov (.reg 8) (.location (.reg 7)),
  .xor (.reg 8) (.location (.reg 0)),
  .and (.reg 8) (.location (.reg 1)),
  .xor (.reg 8) (.location (.reg 0)),
  .mov (.reg 14) (.location (.input 11)),
  .add (.reg 2) (.location (.reg 14)),
  .mov (.stack 32) (.location (.reg 14)),
  .add (.reg 2) (.location (.reg 8)),
  .add (.reg 2) (.immediate 0x895cd7be),
  .rol (.reg 2) 22,
  .add (.reg 2) (.location (.reg 1))]

theorem segment12_correct (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) (h : Invariant11 initial X working s) :
    Invariant12 initial X (operation F X[11] 0x895cd7be 22 working) (executeWords segment12 s) := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    h18, h19, h20, h21, h22, h23, h24, h25, h26⟩
  with_unfolding_all change (s (.stack 4)) = X[9] ∧
    (s (.stack 8)) = initial.B ∧
    (s (.stack 24)) = X[8] ∧
    (s (.stack 28)) = X[4] ∧
    (s (.input 11)) = X[11] ∧
    (s (.stack 40)) = X[10] ∧
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
    (s (.reg 0)) = (operation F X[11] 0x895cd7be 22 working).A ∧
    (s (.reg 1)) = (operation F X[11] 0x895cd7be 22 working).C ∧
    ((((((s (.reg 2)) + (s (.input 11))) + ((((s (.reg 7)) ^^^ (s (.reg 0))) &&& (s (.reg 1))) ^^^
      (s (.reg 0)))) + 0x895cd7be)).rotateLeft 22 + (s (.reg 1))) = (operation F X[11] 0x895cd7be 22
      working).B ∧
    (s (.reg 3)) = X[1] ∧
    (s (.reg 7)) = (operation F X[11] 0x895cd7be 22 working).D ∧
    (s (.reg 9)) = X[6] ∧
    (s (.reg 11)) = X[10] ∧
    (s (.input 11)) = X[11] ∧
    (s (.input 12)) = X[12] ∧
    (s (.input 13)) = X[13] ∧
    (s (.input 14)) = X[14] ∧
    (s (.input 15)) = X[15]
  simp only [operation, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, true_and, and_true]
  md5_word_arithmetic

def Invariant13 (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) : Prop :=
  s (.stack 4) = X[9] ∧
  s (.stack 8) = initial.B ∧
  s (.stack 24) = X[8] ∧
  s (.stack 28) = X[4] ∧
  s (.stack 32) = X[11] ∧
  s (.stack 40) = X[10] ∧
  s (.stack 44) = X[12] ∧
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
  s (.reg 1) = working.D ∧
  s (.reg 2) = working.C ∧
  s (.reg 3) = X[1] ∧
  s (.reg 7) = working.A ∧
  s (.reg 9) = X[6] ∧
  s (.reg 11) = X[10] ∧
  s (.reg 12) = working.B ∧
  s (.reg 14) = X[11] ∧
  s (.input 13) = X[13] ∧
  s (.input 14) = X[14] ∧
  s (.input 15) = X[15]

def segment13 : List WordInstruction := [
  .mov (.reg 10) (.location (.reg 1)),
  .xor (.reg 10) (.location (.reg 7)),
  .and (.reg 10) (.location (.reg 2)),
  .xor (.reg 10) (.location (.reg 7)),
  .mov (.reg 8) (.location (.input 12)),
  .mov (.stack 44) (.location (.reg 8)),
  .add (.reg 0) (.location (.reg 8)),
  .lea (.reg 12) (.reg 10) (.reg 0),
  .add (.reg 12) (.immediate 0x6b901122),
  .rol (.reg 12) 7,
  .add (.reg 12) (.location (.reg 2))]

theorem segment13_correct (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) (h : Invariant12 initial X working s) :
    Invariant13 initial X (operation F X[12] 0x6b901122 7 working) (executeWords segment13 s) := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    h18, h19, h20, h21, h22, h23, h24, h25, h26, h27⟩
  with_unfolding_all change (s (.stack 4)) = X[9] ∧
    (s (.stack 8)) = initial.B ∧
    (s (.stack 24)) = X[8] ∧
    (s (.stack 28)) = X[4] ∧
    (s (.stack 32)) = X[11] ∧
    (s (.stack 40)) = X[10] ∧
    (s (.input 12)) = X[12] ∧
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
    (s (.reg 1)) = (operation F X[12] 0x6b901122 7 working).D ∧
    (s (.reg 2)) = (operation F X[12] 0x6b901122 7 working).C ∧
    (s (.reg 3)) = X[1] ∧
    (s (.reg 7)) = (operation F X[12] 0x6b901122 7 working).A ∧
    (s (.reg 9)) = X[6] ∧
    (s (.reg 11)) = X[10] ∧
    ((((((((s (.reg 1)) ^^^ (s (.reg 7))) &&& (s (.reg 2))) ^^^ (s (.reg 7))) + ((s (.reg 0)) + (s
      (.input 12)))) + 0x6b901122)).rotateLeft 7 + (s (.reg 2))) = (operation F X[12] 0x6b901122 7
      working).B ∧
    (s (.reg 14)) = X[11] ∧
    (s (.input 13)) = X[13] ∧
    (s (.input 14)) = X[14] ∧
    (s (.input 15)) = X[15]
  simp only [operation, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, true_and, and_true]
  md5_word_arithmetic

def Invariant14 (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) : Prop :=
  s (.stack 4) = X[9] ∧
  s (.stack 8) = initial.B ∧
  s (.stack 20) = X[13] ∧
  s (.stack 24) = X[8] ∧
  s (.stack 28) = X[4] ∧
  s (.stack 32) = X[11] ∧
  s (.stack 40) = X[10] ∧
  s (.stack 44) = X[12] ∧
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
  s (.reg 1) = working.A ∧
  s (.reg 2) = working.D ∧
  s (.reg 3) = X[1] ∧
  s (.reg 9) = X[6] ∧
  s (.reg 11) = X[10] ∧
  s (.reg 12) = working.C ∧
  s (.reg 14) = X[11] ∧
  s (.input 14) = X[14] ∧
  s (.input 15) = X[15]

def segment14 : List WordInstruction := [
  .mov (.reg 0) (.location (.reg 2)),
  .xor (.reg 0) (.location (.reg 1)),
  .and (.reg 0) (.location (.reg 12)),
  .xor (.reg 0) (.location (.reg 1)),
  .mov (.reg 8) (.location (.input 13)),
  .mov (.stack 20) (.location (.reg 8)),
  .add (.reg 7) (.location (.reg 8)),
  .add (.reg 0) (.location (.reg 7)),
  .add (.reg 0) (.immediate 0xfd987193),
  .rol (.reg 0) 12,
  .add (.reg 0) (.location (.reg 12))]

theorem segment14_correct (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) (h : Invariant13 initial X working s) :
    Invariant14 initial X (operation F X[13] 0xfd987193 12 working) (executeWords segment14 s) := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    h18, h19, h20, h21, h22, h23, h24, h25, h26, h27⟩
  with_unfolding_all change (s (.stack 4)) = X[9] ∧
    (s (.stack 8)) = initial.B ∧
    (s (.input 13)) = X[13] ∧
    (s (.stack 24)) = X[8] ∧
    (s (.stack 28)) = X[4] ∧
    (s (.stack 32)) = X[11] ∧
    (s (.stack 40)) = X[10] ∧
    (s (.stack 44)) = X[12] ∧
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
    ((((((((s (.reg 2)) ^^^ (s (.reg 1))) &&& (s (.reg 12))) ^^^ (s (.reg 1))) + ((s (.reg 7)) + (s
      (.input 13)))) + 0xfd987193)).rotateLeft 12 + (s (.reg 12))) = (operation F X[13] 0xfd987193
      12 working).B ∧
    (s (.reg 1)) = (operation F X[13] 0xfd987193 12 working).A ∧
    (s (.reg 2)) = (operation F X[13] 0xfd987193 12 working).D ∧
    (s (.reg 3)) = X[1] ∧
    (s (.reg 9)) = X[6] ∧
    (s (.reg 11)) = X[10] ∧
    (s (.reg 12)) = (operation F X[13] 0xfd987193 12 working).C ∧
    (s (.reg 14)) = X[11] ∧
    (s (.input 14)) = X[14] ∧
    (s (.input 15)) = X[15]
  simp only [operation, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, true_and, and_true]
  md5_word_arithmetic

def Invariant15 (initial : Buffer) (X : Vector (BitVec 32) 16)
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
  s (.reg 2) = working.A ∧
  s (.reg 3) = X[1] ∧
  s (.reg 5) = (~~~working.C) ∧
  s (.reg 8) = X[14] ∧
  s (.reg 9) = X[6] ∧
  s (.reg 11) = X[10] ∧
  s (.reg 12) = working.D ∧
  s (.reg 14) = X[11] ∧
  s (.input 15) = X[15]

def segment15 : List WordInstruction := [
  .mov (.reg 7) (.location (.reg 0)),
  .and (.reg 7) (.location (.reg 12)),
  .mov (.reg 5) (.location (.reg 0)),
  .not (.reg 5),
  .mov (.reg 10) (.location (.reg 2)),
  .and (.reg 10) (.location (.reg 5)),
  .or (.reg 10) (.location (.reg 7)),
  .mov (.reg 8) (.location (.input 14)),
  .add (.reg 1) (.location (.reg 8)),
  .mov (.stack 36) (.location (.reg 8)),
  .add (.reg 1) (.location (.reg 10)),
  .add (.reg 1) (.immediate 0xa679438e),
  .rol (.reg 1) 17,
  .add (.reg 1) (.location (.reg 0))]

theorem segment15_correct (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) (h : Invariant14 initial X working s) :
    Invariant15 initial X (operation F X[14] 0xa679438e 17 working) (executeWords segment15 s) := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    h18, h19, h20, h21, h22, h23, h24, h25, h26, h27⟩
  with_unfolding_all change (s (.stack 4)) = X[9] ∧
    (s (.stack 8)) = initial.B ∧
    (s (.stack 20)) = X[13] ∧
    (s (.stack 24)) = X[8] ∧
    (s (.stack 28)) = X[4] ∧
    (s (.stack 32)) = X[11] ∧
    (s (.input 14)) = X[14] ∧
    (s (.stack 40)) = X[10] ∧
    (s (.stack 44)) = X[12] ∧
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
    (s (.reg 0)) = (operation F X[14] 0xa679438e 17 working).C ∧
    ((((((s (.reg 1)) + (s (.input 14))) + (((s (.reg 2)) &&& (~~~(s (.reg 0)))) ||| ((s (.reg 0))
      &&& (s (.reg 12))))) + 0xa679438e)).rotateLeft 17 + (s (.reg 0))) = (operation F X[14]
      0xa679438e 17 working).B ∧
    (s (.reg 2)) = (operation F X[14] 0xa679438e 17 working).A ∧
    (s (.reg 3)) = X[1] ∧
    (~~~(s (.reg 0))) = (~~~(operation F X[14] 0xa679438e 17 working).C) ∧
    (s (.input 14)) = X[14] ∧
    (s (.reg 9)) = X[6] ∧
    (s (.reg 11)) = X[10] ∧
    (s (.reg 12)) = (operation F X[14] 0xa679438e 17 working).D ∧
    (s (.reg 14)) = X[11] ∧
    (s (.input 15)) = X[15]
  simp only [operation, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, true_and, and_true]
  md5_word_arithmetic

def Invariant16 (initial : Buffer) (X : Vector (BitVec 32) 16)
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
  s (.reg 5) = ((((~~~working.D) &&& working.C) + X[1]) + working.A) ∧
  s (.reg 7) = X[15] ∧
  s (.reg 8) = X[14] ∧
  s (.reg 9) = X[6] ∧
  s (.reg 11) = X[10] ∧
  s (.reg 13) = (~~~working.C) ∧
  s (.reg 14) = X[11]

def segment16 : List WordInstruction := [
  .mov (.reg 10) (.location (.reg 1)),
  .and (.reg 10) (.location (.reg 0)),
  .mov (.reg 13) (.location (.reg 1)),
  .not (.reg 13),
  .lea (.reg 15) (.reg 3) (.reg 12),
  .and (.reg 12) (.location (.reg 13)),
  .or (.reg 12) (.location (.reg 10)),
  .mov (.reg 7) (.location (.input 15)),
  .add (.reg 2) (.location (.reg 7)),
  .mov (.stack 48) (.location (.reg 7)),
  .add (.reg 2) (.location (.reg 12)),
  .add (.reg 2) (.immediate 0x49b40821),
  .and (.reg 5) (.location (.reg 1)),
  .add (.reg 5) (.location (.reg 15)),
  .rol (.reg 2) 22,
  .add (.reg 2) (.location (.reg 1))]

theorem segment16_correct (initial : Buffer) (X : Vector (BitVec 32) 16)
    (working : Buffer) (s : WordState) (h : Invariant15 initial X working s) :
    Invariant16 initial X (operation F X[15] 0x49b40821 22 working) (executeWords segment16 s) := by
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
    (s (.input 15)) = X[15] ∧
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
    (s (.reg 0)) = (operation F X[15] 0x49b40821 22 working).D ∧
    (s (.reg 1)) = (operation F X[15] 0x49b40821 22 working).C ∧
    ((((((s (.reg 2)) + (s (.input 15))) + (((s (.reg 12)) &&& (~~~(s (.reg 1)))) ||| ((s (.reg 1))
      &&& (s (.reg 0))))) + 0x49b40821)).rotateLeft 22 + (s (.reg 1))) = (operation F X[15]
      0x49b40821 22 working).B ∧
    (((s (.reg 5)) &&& (s (.reg 1))) + ((s (.reg 3)) + (s (.reg 12)))) = ((((~~~(operation F X[15]
      0x49b40821 22 working).D) &&& (operation F X[15] 0x49b40821 22 working).C) + X[1]) +
      (operation F X[15] 0x49b40821 22 working).A) ∧
    (s (.input 15)) = X[15] ∧
    (s (.reg 8)) = X[14] ∧
    (s (.reg 9)) = X[6] ∧
    (s (.reg 11)) = X[10] ∧
    (~~~(s (.reg 1))) = (~~~(operation F X[15] 0x49b40821 22 working).C) ∧
    (s (.reg 14)) = X[11]
  simp only [operation, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, true_and, and_true]
  md5_word_arithmetic

end Md5.Proofs.Block.Rounds
