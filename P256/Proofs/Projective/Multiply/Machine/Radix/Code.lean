import P256.Proofs.Projective.Multiply.Machine.Radix.Initialize
import P256.Proofs.Projective.Multiply.Machine.Radix.Nibbles.Pair
import P256.Proofs.Projective.Multiply.Machine.Radix.Nibbles.Special
import P256.Proofs.Projective.Multiply.Machine.Radix.Nibbles.Finish
import P256.Proofs.Projective.Multiply.Machine.Radix.Recenter.Tail

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Radix

open P256.Spec.Program

theorem nibble_code_0 :
    Extracted.textBytes.toListFrom 0xb77f 20 =
      firstPairBytes 111 8 9 := by decide +kernel

theorem nibble_code_1 :
    Extracted.textBytes.toListFrom 0xb793 21 =
      pairBytes 110 10 11 := by decide +kernel

theorem nibble_code_2 :
    Extracted.textBytes.toListFrom 0xb7a8 21 =
      pairBytes 109 12 13 := by decide +kernel

theorem nibble_code_3 :
    Extracted.textBytes.toListFrom 0xb7bd 21 =
      pairBytes 108 14 15 := by decide +kernel

theorem nibble_code_4 :
    Extracted.textBytes.toListFrom 0xb7d2 21 =
      pairBytes 107 16 17 := by decide +kernel

theorem nibble_code_5 :
    Extracted.textBytes.toListFrom 0xb7e7 44 =
      doublePairBytes 106 105 18 19 20 21 := by decide +kernel

theorem nibble_code_7 :
    Extracted.textBytes.toListFrom 0xb813 21 =
      pairBytes 104 22 23 := by decide +kernel

theorem nibble_code_8 :
    Extracted.textBytes.toListFrom 0xb828 21 =
      pairBytes 103 24 25 := by decide +kernel

theorem nibble_code_9 :
    Extracted.textBytes.toListFrom 0xb83d 21 =
      pairBytes 102 26 27 := by decide +kernel

theorem nibble_code_10 :
    Extracted.textBytes.toListFrom 0xb852 21 =
      pairBytes 101 28 29 := by decide +kernel

theorem nibble_code_11 :
    Extracted.textBytes.toListFrom 0xb867 44 =
      doublePairBytes 100 99 30 31 32 33 := by decide +kernel

theorem nibble_code_13 :
    Extracted.textBytes.toListFrom 0xb893 21 =
      pairBytes 98 34 35 := by decide +kernel

theorem nibble_code_14 :
    Extracted.textBytes.toListFrom 0xb8a8 21 =
      pairBytes 97 36 37 := by decide +kernel

theorem nibble_code_15 :
    Extracted.textBytes.toListFrom 0xb8bd 21 =
      pairBytes 96 38 39 := by decide +kernel

theorem nibble_code_16 :
    Extracted.textBytes.toListFrom 0xb8d2 21 =
      pairBytes 95 40 41 := by decide +kernel

theorem nibble_code_17 :
    Extracted.textBytes.toListFrom 0xb8e7 21 =
      pairBytes 94 42 43 := by decide +kernel

theorem nibble_code_18 :
    Extracted.textBytes.toListFrom 0xb8fc 21 =
      pairBytes 93 44 45 := by decide +kernel

theorem nibble_code_19 :
    Extracted.textBytes.toListFrom 0xb911 21 =
      pairBytes 92 46 47 := by decide +kernel

theorem nibble_code_20 :
    Extracted.textBytes.toListFrom 0xb926 21 =
      pairBytes 91 48 49 := by decide +kernel

theorem nibble_code_21 :
    Extracted.textBytes.toListFrom 0xb93b 21 =
      pairBytes 90 50 51 := by decide +kernel

theorem nibble_code_22 :
    Extracted.textBytes.toListFrom 0xb950 21 =
      pairBytes 89 52 53 := by decide +kernel

theorem nibble_code_23 :
    Extracted.textBytes.toListFrom 0xb965 21 =
      pairBytes 88 54 55 := by decide +kernel

theorem nibble_code_24 :
    Extracted.textBytes.toListFrom 0xb97a 21 =
      pairBytes 87 56 57 := by decide +kernel

theorem nibble_code_25 :
    Extracted.textBytes.toListFrom 0xb98f 21 =
      pairBytes 86 58 59 := by decide +kernel

theorem nibble_code_26 :
    Extracted.textBytes.toListFrom 0xb9a4 21 =
      pairBytes 85 60 61 := by decide +kernel

theorem nibble_code_27 :
    Extracted.textBytes.toListFrom 0xb9b9 21 =
      pairBytes 84 62 63 := by decide +kernel

theorem nibble_code_28 :
    Extracted.textBytes.toListFrom 0xb9ce 21 =
      pairBytes 83 64 65 := by decide +kernel

theorem nibble_code_29 :
    Extracted.textBytes.toListFrom 0xb9e3 21 =
      pairBytes 82 66 67 := by decide +kernel

theorem nibble_code_30 :
    Extracted.textBytes.toListFrom 0xb9f8 21 =
      pairBytes 81 68 69 := by decide +kernel

theorem nibble_code_31 :
    Extracted.textBytes.toListFrom 0xba0d 21 =
      pairBytes 80 70 71 := by decide +kernel

theorem extractionFinishBytes_code :
    Extracted.textBytes.toListFrom 0xba22 14 = extractionFinishBytes := by decide +kernel

theorem Recenter_firstHalfBytes_code :
    Extracted.textBytes.toListFrom 0xba30 23 = Recenter.firstHalfBytes := by decide +kernel

theorem Recenter_secondHalfBytes_code :
    Extracted.textBytes.toListFrom 0xba47 23 = Recenter.secondHalfBytes := by decide +kernel

theorem Recenter_tailBytes_code :
    Extracted.textBytes.toListFrom 0xba5e 12 = Recenter.tailBytes := by decide +kernel

theorem initializeBytes_code :
    Extracted.textBytes.toListFrom 0xb728 82 = initializeBytes := by decide +kernel

end P256.Proofs.Projective.Multiply.Machine.Radix
