import AesGcm.Proofs.Machine.Fixslice16.Representation
import Standards.NIST.AES.Transformations
import Init.Data.UInt.Bitwise

namespace AesGcm.Proofs.Machine.Fixslice16

def fromStandard (x : Standards.NIST.AES.Block) : Block := fun j ↦ x[j.val].toBitVec

def toStandard (x : Block) : Standards.NIST.AES.Block :=
  Vector.ofFn fun j ↦ UInt8.ofBitVec (x j)

def encodeStandard (x : Standards.NIST.AES.Block) : Planes16 := encode (fromStandard x)

def decodeStandard (x : Planes16) : Standards.NIST.AES.Block := toStandard (decode x)

theorem toStandard_fromStandard (x : Standards.NIST.AES.Block) :
    toStandard (fromStandard x) = x := by
  apply Vector.ext
  intro j hj
  simp only [toStandard, fromStandard, Vector.getElem_ofFn, UInt8.ofBitVec_toBitVec]

theorem fromStandard_toStandard (x : Block) : fromStandard (toStandard x) = x := by
  funext j
  simp only [fromStandard, toStandard, Vector.getElem_ofFn]

theorem decodeStandard_encodeStandard (x : Standards.NIST.AES.Block) :
    decodeStandard (encodeStandard x) = x := by
  simp only [decodeStandard, encodeStandard, decode_encode, toStandard_fromStandard]

theorem encodeStandard_decodeStandard (x : Planes16) :
    encodeStandard (decodeStandard x) = x := by
  simp only [decodeStandard, encodeStandard, fromStandard_toStandard, encode_decode]

def xorBlock (x y : Block) : Block := fun j ↦ x j ^^^ y j

def xorPlanes (x y : Planes16) : Planes16 := fun p ↦ x p ^^^ y p

theorem encode_xorBlock (x y : Block) :
    encode (xorBlock x y) = xorPlanes (encode x) (encode y) := by
  funext p
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  change (encode (xorBlock x y) p).getLsbD i =
    (encode x p ^^^ encode y p).getLsbD i
  rw [BitVec.getLsbD_xor, getLsbD_encode _ p ⟨i, hi⟩,
    getLsbD_encode x p ⟨i, hi⟩, getLsbD_encode y p ⟨i, hi⟩]
  exact BitVec.getLsbD_xor

theorem decode_xorPlanes (x y : Planes16) :
    decode (xorPlanes x y) = xorBlock (decode x) (decode y) := by
  rw [← encode_decode x, ← encode_decode y, ← encode_xorBlock, decode_encode]
  simp only [decode_encode]

def roundKeyBlock (key : Vector (Vector UInt8 4) 4) : Block :=
  fun j ↦ key[j.val / 4][j.val % 4].toBitVec

theorem fromStandard_addRoundKey (x : Standards.NIST.AES.Block)
    (key : Vector (Vector UInt8 4) 4) :
    fromStandard (Standards.NIST.AES.addRoundKey x key) =
      xorBlock (fromStandard x) (roundKeyBlock key) := by
  funext j
  simp only [fromStandard, Standards.NIST.AES.addRoundKey, Vector.getElem_ofFn, Fin.getElem_fin,
    UInt8.toBitVec_xor, xorBlock, roundKeyBlock]

theorem encodeStandard_addRoundKey (x : Standards.NIST.AES.Block)
    (key : Vector (Vector UInt8 4) 4) :
    encodeStandard (Standards.NIST.AES.addRoundKey x key) =
      xorPlanes (encodeStandard x) (encode (roundKeyBlock key)) := by
  simp only [encodeStandard, fromStandard_addRoundKey, encode_xorBlock]

end AesGcm.Proofs.Machine.Fixslice16
