import K256.Proofs.Sec1.Affine.DecodeCall
import K256.Proofs.Sec1.Affine.Routes.Compressed
import K256.Proofs.Sec1.Affine.Routes.Uncompressed

namespace K256.Proofs.Sec1.Affine

open K256.Spec.Program X86.Machine

private theorem tagSize {t : UInt8} {n : Nat}
    (valid : Parser.validTag t.toBitVec)
    (size : n = (Parser.lengthTable.get ⟨t.toNat,Parser.validTag_lt valid⟩).toNat) :
    t = 0 ∨ ((t = 2 ∨ t = 3 ∨ t = 5) ∧ n = 33) ∨ (t = 4 ∧ n = 65) := by
  have h : t = 0 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 := by
    simp only [← UInt8.toBitVec_inj]
    exact valid
  rcases h with rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl ⟨Or.inl rfl,size⟩)
  · exact Or.inr (Or.inl ⟨Or.inr (Or.inl rfl),size⟩)
  · exact Or.inr (Or.inr ⟨rfl,size⟩)
  · exact Or.inr (Or.inl ⟨Or.inr (Or.inr rfl),size⟩)

theorem decodeCall_of_decoders {s : RamState} {bytes : ByteArray}
    (call : ValidCall publicKeyFromSec1Bytes s [bytes])
    (compressed : Compressed.DecoderCall Extracted.programImage)
    (uncompressed : Uncompressed.DecoderCall Extracted.programImage) : DecodeCall s bytes := by
  intro args m pos valid len entry
  let tag := bytes[0]'pos
  have header : bytes.data[0]? = some tag := by rw [Array.getElem?_eq_getElem pos]; rfl
  have get : bytes.data[0]?.getD 0 = tag := by rw [header]; rfl
  have size : (s.regValue .rdx).toNat = bytes.size := call.lengthArgumentsMatchInputs.1
  obtain zero | ⟨comp,length⟩ | ⟨full,length⟩ := tagSize valid (size.symm.trans (congrArg BitVec.toNat len))
  · exact decodeIdentityCall call entry (get.trans zero)
  · have good : tag.toBitVec = 2 ∨ tag.toBitVec = 3 ∨ tag.toBitVec = 4 ∨ tag.toBitVec = 5 := by
      dsimp only [tag]
      rcases comp with h | h | h <;> rw [h] <;> decide
    exact decodeCoordinateCall call entry (congrArg UInt8.toBitVec get) good (by omega)
      (compressedRoutine call compressed comp header length)
  · have bits := congrArg UInt8.toBitVec (get.trans full)
    exact decodeCoordinateCall call entry bits (Or.inr (Or.inr (Or.inl rfl))) (by omega)
      (uncompressedRoutine uncompressed (full ▸ header) length)

end K256.Proofs.Sec1.Affine
