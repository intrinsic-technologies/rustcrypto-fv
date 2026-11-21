import K256.Proofs.Generate.Generator.Affine.Invert.Core.Batch.State

namespace K256.Proofs.Generate.Generator.Affine.Invert.Core.Batch

open SafeGcd.Batch (Words)

def positiveByte (s : Words) : BitVec 8 :=
  if (!(s.delta == 0) && !s.delta.msb) then 1 else 0

def oddByte (s : Words) : BitVec 8 := s.g.setWidth 8 &&& 1

def swapByte (s : Words) : BitVec 8 := positiveByte s &&& s.g.setWidth 8

def selectWord (bit : BitVec 8) (x y : BitVec 64) :=
  (((y ^^^ x) &&& -bit.setWidth 64) ^^^ x)

def maskedF (s : Words) := (-((oddByte s).setWidth 64)) &&& s.f

def iterationWords (s : Words) : Words where
  delta := s.delta + 2 ^^^ (((2 - s.delta) ^^^ (s.delta + 2)) &&& -(swapByte s).setWidth 64)
  f := selectWord (swapByte s) s.f s.g
  g := (selectWord (swapByte s) (maskedF s + s.g) (s.g - maskedF s)).sshiftRight 1
  u := selectWord (swapByte s) s.u s.q + selectWord (swapByte s) s.u s.q
  v := selectWord (swapByte s) s.v s.r + selectWord (swapByte s) s.v s.r
  q := s.q + ((-(oddByte s).setWidth 64) &&& selectWord (positiveByte s) s.u (-s.u))
  r := s.r + ((-(oddByte s).setWidth 64) &&& selectWord (positiveByte s) s.v (-s.v))

private theorem positiveByte_eq (s : Words) :
    positiveByte s = if 0 < s.delta.toInt then 1 else 0 := by
  unfold positiveByte
  congr 1
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq,
    BitVec.msb_eq_toInt]
  simp only [decide_eq_false_iff_not, ← BitVec.toInt_inj]
  apply propext
  have : (0 : BitVec 64).toInt = 0 := rfl
  omega

theorem iterationWords_eq (s : Words) : iterationWords s = SafeGcd.Batch.next s := by
  have andL (x : BitVec 64) : 18446744073709551615#64 &&& x = x := BitVec.allOnes_and
  have andR (x : BitVec 64) : x &&& 18446744073709551615#64 = x := BitVec.and_allOnes
  have cancel (x y : BitVec 64) : x ^^^ (x ^^^ y) = y := by rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  have swapMask : swapByte s = if 0 < s.delta.toInt then oddByte s else 0 := by
    rw [swapByte, positiveByte_eq]
    split <;> simp [BitVec.and_comm, oddByte]
  have oddMask := SafeGcd.parity_byte s.g
  change oddByte s = _ at oddMask
  by_cases odd : s.g.toInt % 2 = 0 <;> by_cases pos : 0 < s.delta.toInt <;>
    simp [iterationWords, SafeGcd.Batch.next, SafeGcd.Batch.swap, SafeGcd.Batch.numerator,
      SafeGcd.Batch.even_eq, SafeGcd.Batch.positive, maskedF, selectWord, swapMask,
      positiveByte_eq, oddMask, odd, pos, BitVec.add_comm, BitVec.xor_comm, andL, andR, cancel, BitVec.sub_eq_add_neg]

end K256.Proofs.Generate.Generator.Affine.Invert.Core.Batch
