import Md5.Proofs.Block.Rounds.Algebra

namespace Md5.Proofs.Block.Rounds

open Standards.RFC.MD5

def schedule (X : Vector (BitVec 32) 16) : List (Buffer → Buffer) := [
  operation F X[0] 0xd76aa478 7,
  operation F X[1] 0xe8c7b756 12,
  operation F X[2] 0x242070db 17,
  operation F X[3] 0xc1bdceee 22,
  operation F X[4] 0xf57c0faf 7,
  operation F X[5] 0x4787c62a 12,
  operation F X[6] 0xa8304613 17,
  operation F X[7] 0xfd469501 22,
  operation F X[8] 0x698098d8 7,
  operation F X[9] 0x8b44f7af 12,
  operation F X[10] 0xffff5bb1 17,
  operation F X[11] 0x895cd7be 22,
  operation F X[12] 0x6b901122 7,
  operation F X[13] 0xfd987193 12,
  operation F X[14] 0xa679438e 17,
  operation F X[15] 0x49b40821 22,
  operation G X[1] 0xf61e2562 5,
  operation G X[6] 0xc040b340 9,
  operation G X[11] 0x265e5a51 14,
  operation G X[0] 0xe9b6c7aa 20,
  operation G X[5] 0xd62f105d 5,
  operation G X[10] 0x2441453 9,
  operation G X[15] 0xd8a1e681 14,
  operation G X[4] 0xe7d3fbc8 20,
  operation G X[9] 0x21e1cde6 5,
  operation G X[14] 0xc33707d6 9,
  operation G X[3] 0xf4d50d87 14,
  operation G X[8] 0x455a14ed 20,
  operation G X[13] 0xa9e3e905 5,
  operation G X[2] 0xfcefa3f8 9,
  operation G X[7] 0x676f02d9 14,
  operation G X[12] 0x8d2a4c8a 20,
  operation H X[5] 0xfffa3942 4,
  operation H X[8] 0x8771f681 11,
  operation H X[11] 0x6d9d6122 16,
  operation H X[14] 0xfde5380c 23,
  operation H X[1] 0xa4beea44 4,
  operation H X[4] 0x4bdecfa9 11,
  operation H X[7] 0xf6bb4b60 16,
  operation H X[10] 0xbebfbc70 23,
  operation H X[13] 0x289b7ec6 4,
  operation H X[0] 0xeaa127fa 11,
  operation H X[3] 0xd4ef3085 16,
  operation H X[6] 0x4881d05 23,
  operation H X[9] 0xd9d4d039 4,
  operation H X[12] 0xe6db99e5 11,
  operation H X[15] 0x1fa27cf8 16,
  operation H X[2] 0xc4ac5665 23,
  operation I X[0] 0xf4292244 6,
  operation I X[7] 0x432aff97 10,
  operation I X[14] 0xab9423a7 15,
  operation I X[5] 0xfc93a039 21,
  operation I X[12] 0x655b59c3 6,
  operation I X[3] 0x8f0ccc92 10,
  operation I X[10] 0xffeff47d 15,
  operation I X[1] 0x85845dd1 21,
  operation I X[8] 0x6fa87e4f 6,
  operation I X[15] 0xfe2ce6e0 10,
  operation I X[6] 0xa3014314 15,
  operation I X[13] 0x4e0811a1 21,
  operation I X[4] 0xf7537e82 6,
  operation I X[11] 0xbd3af235 10,
  operation I X[2] 0x2ad7d2bb 15,
  operation I X[9] 0xeb86d391 21]

def runSchedule (initial : Buffer) (X : Vector (BitVec 32) 16) : Buffer :=
  (schedule X).foldl (fun s f ↦ f s) initial

def specSchedule :=
  (rounds.flatMap fun (f, entries) ↦ entries.map fun (k, amount) ↦ (f, k, amount)).zip T.toList

set_option maxRecDepth 4096 in
theorem schedule_eq_spec (X : Vector (BitVec 32) 16) :
    schedule X = specSchedule.map
      (fun ((f, k, amount), t) ↦ operation f X[k] t amount) := by
  rfl

abbrev OperationEntry :=
  (BitVec 32 → BitVec 32 → BitVec 32 → BitVec 32) × Fin 16 × Nat

abbrev OperationConstant := OperationEntry × BitVec 32

def runOperationList (ops : List OperationConstant) (initial : Buffer)
    (X : Vector (BitVec 32) 16) : Buffer := Id.run do
  let mut a := initial.A
  let mut b := initial.B
  let mut c := initial.C
  let mut d := initial.D
  for ((f, k, amount), t) in ops do
    let updated := b + (a + f b c d + X[k] + t).rotateLeft amount
    (a, b, c, d) := (d, updated, b, c)
  return ⟨initial.A + a, initial.B + b, initial.C + c, initial.D + d⟩

theorem runOperationList_eq_fold (ops : List OperationConstant) (initial : Buffer)
    (X : Vector (BitVec 32) 16) :
    runOperationList ops initial X = feedForward initial
      (ops.foldl (fun b a ↦ operation a.1.1 X[a.1.2.1] a.2 a.1.2.2 b) initial) := by
  unfold runOperationList
  simp only [List.forIn_pure_yield_eq_foldl]
  let pack : BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 → Buffer :=
    fun (a, b, c, d) ↦ ⟨a, b, c, d⟩
  have hom := List.foldl_hom (l := ops)
    (init := (initial.A, initial.B, initial.C, initial.D)) pack
    (g₁ := fun b a ↦ (b.2.2.2,
      b.2.1 + (b.1 + a.1.1 b.2.1 b.2.2.1 b.2.2.2 + X[a.1.2.1] + a.2).rotateLeft a.1.2.2,
      b.2.1, b.2.2.1))
    (g₂ := fun b a ↦ operation a.1.1 X[a.1.2.1] a.2 a.1.2.2 b)
    (by intro x y; rfl)
  rw [hom]
  rfl

set_option maxRecDepth 4096 in
theorem processBlock_eq_runSchedule (initial : Buffer) (X : Vector (BitVec 32) 16) :
    processBlock initial X = feedForward initial (runSchedule initial X) := by
  have hs : runSchedule initial X =
      specSchedule.foldl (fun b a ↦ operation a.1.1 X[a.1.2.1] a.2 a.1.2.2 b) initial := by
    rw [runSchedule, schedule_eq_spec, List.foldl_map]
  calc
    processBlock initial X = runOperationList specSchedule initial X := by
      simp only [processBlock, runOperationList, specSchedule]
    _ = feedForward initial (specSchedule.foldl
        (fun b a ↦ operation a.1.1 X[a.1.2.1] a.2 a.1.2.2 b) initial) :=
      runOperationList_eq_fold _ _ _
    _ = feedForward initial (runSchedule initial X) := congrArg (feedForward initial) hs.symm

end Md5.Proofs.Block.Rounds
