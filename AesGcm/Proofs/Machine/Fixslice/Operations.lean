import AesGcm.Proofs.Machine.Fixslice.Representation
import Standards.NIST.AES.Transformations
import Init.Data.UInt.Bitwise

namespace AesGcm.Proofs.Machine.Fixslice

abbrev StandardBlocks := Fin 4 → Standards.NIST.AES.Block

def fromStandard (x : StandardBlocks) : Blocks := fun b j ↦ (x b)[j.val].toBitVec

def toStandard (x : Blocks) : StandardBlocks := fun b ↦
  Vector.ofFn fun j ↦ UInt8.ofBitVec (x b j)

def encodeStandard (x : StandardBlocks) : Planes := encode (fromStandard x)

def decodeStandard (x : Planes) : StandardBlocks := toStandard (decode x)

theorem toStandard_fromStandard (x : StandardBlocks) : toStandard (fromStandard x) = x := by
  funext b
  apply Vector.ext
  intro j hj
  simp only [toStandard, fromStandard, Vector.getElem_ofFn, UInt8.ofBitVec_toBitVec]

theorem fromStandard_toStandard (x : Blocks) : fromStandard (toStandard x) = x := by
  funext b j
  simp only [fromStandard, toStandard, Vector.getElem_ofFn]

theorem decodeStandard_encodeStandard (x : StandardBlocks) :
    decodeStandard (encodeStandard x) = x := by
  simp only [decodeStandard, encodeStandard, decode_encode, toStandard_fromStandard]

theorem encodeStandard_decodeStandard (x : Planes) :
    encodeStandard (decodeStandard x) = x := by
  simp only [decodeStandard, encodeStandard, fromStandard_toStandard, encode_decode]

def xorBlocks (x y : Blocks) : Blocks := fun b j ↦ x b j ^^^ y b j

def xorPlanes (x y : Planes) : Planes := fun p ↦ x p ^^^ y p

theorem encode_xorBlocks (x y : Blocks) :
    encode (xorBlocks x y) = xorPlanes (encode x) (encode y) := by
  funext p
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  change (encode (xorBlocks x y) p).getLsbD i =
    (encode x p ^^^ encode y p).getLsbD i
  rw [BitVec.getLsbD_xor, getLsbD_encode _ p ⟨i, hi⟩,
    getLsbD_encode x p ⟨i, hi⟩, getLsbD_encode y p ⟨i, hi⟩]
  exact BitVec.getLsbD_xor

theorem decode_xorPlanes (x y : Planes) :
    decode (xorPlanes x y) = xorBlocks (decode x) (decode y) := by
  rw [← encode_decode x, ← encode_decode y, ← encode_xorBlocks, decode_encode]
  simp only [decode_encode]

def broadcast (x : Fin 16 → BitVec 8) : Blocks := fun _ ↦ x

def roundKeyBlocks (key : Vector (Vector UInt8 4) 4) : Blocks :=
  fun _ j ↦ key[j.val / 4][j.val % 4].toBitVec

theorem fromStandard_addRoundKey (x : StandardBlocks) (key : Vector (Vector UInt8 4) 4) :
    fromStandard (fun b ↦ Standards.NIST.AES.addRoundKey (x b) key) =
      xorBlocks (fromStandard x) (roundKeyBlocks key) := by
  funext b j
  simp only [fromStandard, Standards.NIST.AES.addRoundKey, Vector.getElem_ofFn, Fin.getElem_fin, UInt8.toBitVec_xor, xorBlocks, roundKeyBlocks]

theorem encodeStandard_addRoundKey (x : StandardBlocks) (key : Vector (Vector UInt8 4) 4) :
    encodeStandard (fun b ↦ Standards.NIST.AES.addRoundKey (x b) key) =
      xorPlanes (encodeStandard x) (encode (roundKeyBlocks key)) := by
  simp only [encodeStandard, fromStandard_addRoundKey, encode_xorBlocks]

theorem encode_injective {x y : Blocks} (h : encode x = encode y) : x = y := by
  simpa only [decode_encode] using congrArg decode h

theorem decode_injective {x y : Planes} (h : decode x = decode y) : x = y := by
  simpa only [encode_decode] using congrArg encode h

end AesGcm.Proofs.Machine.Fixslice
