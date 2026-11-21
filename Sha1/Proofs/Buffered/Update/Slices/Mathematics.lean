import Sha1.Proofs.Buffered.Invariant

namespace Sha1.Proofs.Buffered.Update.Slices

open Sha1.Proofs.Wrapper.Absorb

private theorem fullBytes_append_aligned (a b : ByteArray) (ha : a.size % 64 = 0) :
    fullBytes (a ++ b) = a ++ fullBytes b := by
  have hcut : 64 * ((a.size + b.size) / 64) = a.size + 64 * (b.size / 64) := by omega
  simp only [fullBytes, fullBlocks, ByteArray.size_append, hcut, ByteArray.extract_append,
    Nat.zero_sub, Nat.add_sub_cancel_left]
  rw [show a.size + 64 * (b.size / 64) = max (a.size + 64 * (b.size / 64)) a.size by omega,
    ByteArray.extract_zero_max_size]

private theorem absorbedHash_append (a b : ByteArray) :
    absorbedHash (a ++ b) = compressBlocks (absorbedHash a) (fullBytes (tailBytes a ++ b)) := by
  have he : fullBytes (a ++ b) = fullBytes a ++ fullBytes (tailBytes a ++ b) := by
    conv => lhs; rw [← fullBytes_append_tailBytes a, ByteArray.append_assoc]
    exact fullBytes_append_aligned _ _ (fullBytes_aligned a)
  rw [absorbedHash, he, compressBlocks_append _ _ _ (fullBytes_aligned a)]
  rfl

theorem absorbedHash_append_short (a b : ByteArray) (h : b.size < 64 - a.size % 64) :
    absorbedHash (a ++ b) = absorbedHash a := by
  have hs : (tailBytes a ++ b).size < 64 := by rw [ByteArray.size_append, size_tailBytes]; omega
  rw [absorbedHash_append]
  simp only [fullBytes, fullBlocks, Nat.div_eq_of_lt hs, Nat.mul_zero, ByteArray.extract_same]
  unfold compressBlocks
  rw [Sha1.Proofs.Compress.Parser.parse_empty]
  rfl

theorem absorbedHash_append_blocks (a b : ByteArray) (h : a.size % 64 = 0) :
    absorbedHash (a ++ b) = compressBlocks (absorbedHash a) (fullBytes b) := by
  rw [absorbedHash, fullBytes_append_aligned _ _ h, compressBlocks_append _ _ _ h]
  have he : fullBytes a = a := by
    simp only [fullBytes, fullBlocks, show 64 * (a.size / 64) = a.size by omega,
      ByteArray.extract_zero_size]
  rw [absorbedHash, he]

theorem absorbedHash_append_fill_prefix (a b : ByteArray) (h : 64 - a.size % 64 ≤ b.size) :
    absorbedHash (a ++ b.extract 0 (64 - a.size % 64)) =
      compressBlocks (absorbedHash a) (filledBlock a b) := by
  rw [absorbedHash_append]
  change compressBlocks _ (fullBytes (filledBlock a b)) = _
  rw [fullBytes, fullBlocks, filledBlock_size _ _ h]
  change compressBlocks _ ((filledBlock a b).extract 0 64) = _
  rw [← filledBlock_size a b h, ByteArray.extract_zero_size]

end Sha1.Proofs.Buffered.Update.Slices
