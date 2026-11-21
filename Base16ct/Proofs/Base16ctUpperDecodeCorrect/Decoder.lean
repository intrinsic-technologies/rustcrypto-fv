import Base16ct.Proofs.Base16ctUpperDecodeCorrect.Decoding

namespace Base16ct.Proofs.Base16ctUpperDecodeCorrect

open Base16ct.Spec Base16ct.Spec.Program Base16ct.Spec.Program.Extracted

def decodeAddress : RFC4648.Alphabet → BitVec 64
  | .lower => lower_decodeAddress
  | .upper => upper_decodeAddress

def decodeRoutine (alphabet : RFC4648.Alphabet) : Routine where
  entryAddress := decodeAddress alphabet
  minStackBytes := 144

end Base16ct.Proofs.Base16ctUpperDecodeCorrect
