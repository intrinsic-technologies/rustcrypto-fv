import Base16ct.Spec

namespace Base16ct.Proofs.Base16ctUpperDecodeCorrect.RFC4648

inductive Alphabet where

  | upper

  | lower
  deriving DecidableEq, Repr

def Alphabet.table : Alphabet → List UInt8
  | .upper =>
    [0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39,
     0x41, 0x42, 0x43, 0x44, 0x45, 0x46]
  | .lower =>
    [0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39,
     0x61, 0x62, 0x63, 0x64, 0x65, 0x66]

def valueOfCharacter (alphabets : List Alphabet) (character : UInt8) : Option Nat :=
  alphabets.findSome? fun alphabet => alphabet.table.idxOf? character

def caseInsensitive : List Alphabet :=
  [.upper, .lower]

def decode (alphabets : List Alphabet) : List UInt8 → Option (List UInt8)
  | [] => some []
  | high :: low :: rest => do
    let high ← valueOfCharacter alphabets high
    let low ← valueOfCharacter alphabets low
    let rest ← decode alphabets rest
    pure (UInt8.ofNat (16 * high + low) :: rest)
  | [_] => none

end Base16ct.Proofs.Base16ctUpperDecodeCorrect.RFC4648
