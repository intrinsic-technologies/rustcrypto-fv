import AesGcm.Proofs.Machine.Fixslice.MixColumns

namespace AesGcm.Proofs.Machine.AES64

open AesGcm.Proofs.Machine.Fixslice

theorem rotateRowsAndColumns11_machine (x : BitVec 64) :
    ((x.rotateLeft 44 &&& 0x0fff0fff0fff0fff) |||
      (x.rotateLeft 60 &&& 0xf000f000f000f000)) = rotateRowsAndColumns11 x := by
  change (((x <<< 44 ||| x >>> 20) &&& 0x0fff0fff0fff0fff) |||
    ((x <<< 60 ||| x >>> 4) &&& 0xf000f000f000f000)) =
    (((x >>> 20 ||| x <<< 44) &&& 0x0fff0fff0fff0fff) |||
      ((x >>> 4 ||| x <<< 60) &&& 0xf000f000f000f000))
  rw [BitVec.or_comm (x <<< 44), BitVec.or_comm (x <<< 60)]
  rfl

theorem rotateRowsAndColumns12_machine (x : BitVec 64) :
    ((x.rotateLeft 40 &&& 0x00ff00ff00ff00ff) |||
      (x.rotateLeft 56 &&& 0xff00ff00ff00ff00)) = rotateRowsAndColumns12 x := by
  change (((x <<< 40 ||| x >>> 24) &&& 0x00ff00ff00ff00ff) |||
    ((x <<< 56 ||| x >>> 8) &&& 0xff00ff00ff00ff00)) =
    (((x >>> 24 ||| x <<< 40) &&& 0x00ff00ff00ff00ff) |||
      ((x >>> 8 ||| x <<< 56) &&& 0xff00ff00ff00ff00))
  rw [BitVec.or_comm (x <<< 40), BitVec.or_comm (x <<< 56)]
  rfl

theorem rotateRowsAndColumns13_machine (x : BitVec 64) :
    ((x.rotateLeft 36 &&& 0x000f000f000f000f) |||
      (x.rotateLeft 52 &&& 0xfff0fff0fff0fff0)) = rotateRowsAndColumns13 x := by
  change (((x <<< 36 ||| x >>> 28) &&& 0x000f000f000f000f) |||
    ((x <<< 52 ||| x >>> 12) &&& 0xfff0fff0fff0fff0)) =
    (((x >>> 28 ||| x <<< 36) &&& 0x000f000f000f000f) |||
      ((x >>> 12 ||| x <<< 52) &&& 0xfff0fff0fff0fff0))
  rw [BitVec.or_comm (x <<< 36), BitVec.or_comm (x <<< 52)]
  rfl

theorem rotateRowsAndColumns22_machine (x : BitVec 64) :
    ((x.rotateLeft 24 &&& 0x00ff00ff00ff00ff) |||
      (x.rotateLeft 40 &&& 0xff00ff00ff00ff00)) = rotateRowsAndColumns22 x := by
  change (((x <<< 24 ||| x >>> 40) &&& 0x00ff00ff00ff00ff) |||
    ((x <<< 40 ||| x >>> 24) &&& 0xff00ff00ff00ff00)) =
    (((x >>> 40 ||| x <<< 24) &&& 0x00ff00ff00ff00ff) |||
      ((x >>> 24 ||| x <<< 40) &&& 0xff00ff00ff00ff00))
  rw [BitVec.or_comm (x <<< 24), BitVec.or_comm (x <<< 40)]
  rfl

theorem rotateRows1_machine (x : BitVec 64) : x.rotateLeft 48 = rotateRows1 x := by
  change (x <<< 48 ||| x >>> 16) = (x >>> 16 ||| x <<< 48)
  exact BitVec.or_comm _ _

theorem rotateRows2_machine (x : BitVec 64) : x.rotateLeft 32 = rotateRows2 x := by
  change (x <<< 32 ||| x >>> 32) = (x >>> 32 ||| x <<< 32)
  exact BitVec.or_comm _ _

end AesGcm.Proofs.Machine.AES64
