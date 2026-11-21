import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Arithmetic.Core
import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Arithmetic.Recurrence

set_option autoImplicit false

open P256.Proofs.Field.Montgomery (p reduceFour reduceStep)

namespace P256.Proofs.Sec1.SquareRoot.Montgomery

theorem wordsValue_split (a : Nat) (b : Vector (BitVec 64) 4) :
    a*wordsValue b = a*lowerWordsValue b + wordBase*(wordBase^2*(a*b[3].toNat)) := by
  unfold wordsValue lowerWordsValue P256.Proofs.Sec1.SquareRoot.Montgomery.limbsToNat
  change a*(b[0].toNat+wordBase*(b[1].toNat+wordBase*(b[2].toNat+wordBase*b[3].toNat))) = _
  grind only

theorem firstRow_value (a next : BitVec 64) (b : Vector (BitVec 64) 4) :
    (firstRow a next b).value = reduceStep (a.toNat*wordsValue b) +
      wordBase^3*(next.toNat*b[3].toNat) := by
  rw [wordsValue_split, P256.Proofs.Field.Montgomery.reduceStep_add_wordMultiple]
  let c := coreWords 0 0 0 a b
  have hc := coreWords_value 0 0 0 a b
  change c.value = reduceStep (0+wordBase*0+wordBase^2*0+a.toNat*lowerWordsValue b) at hc
  simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add] at hc
  change c.value = reduceStep (a.toNat*lowerWordsValue b) at hc
  change c.first.toNat + wordBase*c.second.toNat + wordBase^2*(firstTop c.low c.high a b[3] next).value = _
  rw [firstTop_value, ← hc]
  clear_value c
  clear hc
  unfold CoreWords.value
  grind only

theorem nextRow_value (t : InterleavedWords) (a next : BitVec 64) (b : Vector (BitVec 64) 4) :
    (nextRow t a next b).value = reduceStep (t.value + a.toNat*lowerWordsValue b) +
      wordBase^3*(next.toNat*b[3].toNat) := by
  have split : t.value + a.toNat*lowerWordsValue b =
      (t.first.toNat+wordBase*t.second.toNat+wordBase^2*t.top.low.toNat+a.toNat*lowerWordsValue b) +
        wordBase*(wordBase^2*(t.top.mid.toNat+wordBase*t.top.high.toNat+wordBase^2*t.top.carry.toNat)) := by
    unfold InterleavedWords.value TopWords.value
    grind only
  rw [split, P256.Proofs.Field.Montgomery.reduceStep_add_wordMultiple]
  let c := coreWords t.first t.second t.top.low a b
  have hc := coreWords_value t.first t.second t.top.low a b
  change c.value = _ at hc
  change c.first.toNat + wordBase*c.second.toNat +
    wordBase^2*(mergeTop c.low c.high t.top.mid t.top.high t.top.carry next b[3]).value = _
  rw [mergeTop_value, ← hc]
  clear_value c
  clear hc split
  unfold CoreWords.value
  grind only

theorem lastRow_value (t : InterleavedWords) (a : BitVec 64) (b : Vector (BitVec 64) 4) :
    (lastRow t a b).value = reduceStep (t.value + a.toNat*lowerWordsValue b) := by
  have split : t.value + a.toNat*lowerWordsValue b =
      (t.first.toNat+wordBase*t.second.toNat+wordBase^2*t.top.low.toNat+a.toNat*lowerWordsValue b) +
        wordBase*(wordBase^2*(t.top.mid.toNat+wordBase*t.top.high.toNat+wordBase^2*t.top.carry.toNat)) := by
    unfold InterleavedWords.value TopWords.value
    grind only
  rw [split, P256.Proofs.Field.Montgomery.reduceStep_add_wordMultiple]
  let c := coreWords t.first t.second t.top.low a b
  let f := finishTop c.low c.high t.top.mid t.top.high t.top.carry
  have hc := coreWords_value t.first t.second t.top.low a b
  have hf := finishTop_value c.low c.high t.top.mid t.top.high t.top.carry
  change c.value = _ at hc
  change f.low.toNat + wordBase*f.mid.toNat + wordBase^2*f.high.toNat = _ at hf
  change c.first.toNat+wordBase*c.second.toNat+wordBase^2*f.low.toNat+
    wordBase^3*f.mid.toNat+wordBase^4*f.high.toNat = _
  rw [← hc]
  clear_value c f
  clear hc split
  unfold CoreWords.value
  grind only

theorem reduceStep_prepared (t a : Nat) (b : Vector (BitVec 64) 4) :
    reduceStep (t + wordBase^3*(a*b[3].toNat) + a*lowerWordsValue b) =
      reduceStep (t + a*wordsValue b) := by
  congr 1
  rw [wordsValue_split]
  grind only

theorem multiplyWords_value (a b : Vector (BitVec 64) 4) :
    (multiplyWords a b).value = reduceFour (wordsValue a * wordsValue b) := by
  let t0 := firstRow a[0] a[1] b
  let t1 := nextRow t0 a[1] a[2] b
  let t2 := nextRow t1 a[2] a[3] b
  have h0 := firstRow_value a[0] a[1] b
  have h1 := nextRow_value t0 a[1] a[2] b
  have h2 := nextRow_value t1 a[2] a[3] b
  have h3 := lastRow_value t2 a[3] b
  change t0.value = _ at h0
  change t1.value = _ at h1
  change t2.value = _ at h2
  rw [h0, reduceStep_prepared] at h1
  rw [h1, reduceStep_prepared] at h2
  rw [h2, reduceStep_prepared] at h3
  change (lastRow t2 a[3] b).value = _
  rw [h3]
  simpa only [ciosFour, ciosRound, Nat.zero_add, wordsValue] using
    ciosFour_eq_reduceFour a[0].toNat a[1].toNat a[2].toNat a[3].toNat (wordsValue b)

end P256.Proofs.Sec1.SquareRoot.Montgomery
