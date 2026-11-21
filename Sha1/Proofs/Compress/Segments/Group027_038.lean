import Sha1.Proofs.Compress.Machine.Run
import Sha1.Proofs.Compress.Rounds.Scalar
import Sha1.Proofs.Common.Instructions.MovStore.Triple
import X86Proofs.Instructions.Mov.Generated.RM.Triple
import X86Proofs.Instructions.Lea.Generated.RM.Triple
import X86Proofs.Instructions.Add.Generated.AccImm32.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.Imm32.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Or.Generated.RR.Triple
import X86Proofs.Instructions.Xor.Generated.RM.Triple
import X86Proofs.Instructions.Rol.Generated.R.Triple

namespace Sha1.Proofs.Compress.Machine

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Sha1.Spec.Program
open Standards.NIST.SHA1 Sha1.Proofs.Compress.Rounds

attribute [local irreducible] workingAfter scheduleWord messageSchedule

private def genericCut027 (stack input : BitVec 64) (H : Vector (BitVec 32) 5)
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) : List Write :=
  [⟨(.reg 0 : Operand 32), ((A 21)).rotateLeft 30⟩,
    ⟨(.reg 1 : Operand 32), (A 25)⟩,
    ⟨(.reg 2 : Operand 32), ((W 11) ^^^ (W 17) ^^^ (W 22) ^^^ (W 9))⟩,
    ⟨(.reg 3 : Operand 32), (W 13)⟩,
    ⟨(.reg 5 : Operand 32), (((A 22)).rotateLeft 30 ^^^ ((A 23)).rotateLeft 30)⟩,
    ⟨(.reg 6 : Operand 32), (A 24)⟩,
    ⟨(.reg 7 : Operand 32), ((A 23)).rotateLeft 30⟩,
    ⟨(.reg 8 : Operand 32), (W 11)⟩,
    ⟨(.reg 9 : Operand 32), ((W 26) + ((A 22)).rotateLeft 30)⟩,
    ⟨(.reg 11 : Operand 32), (W 22)⟩,
    ⟨(.reg 12 : Operand 32), (W 16)⟩,
    ⟨(.reg 14 : Operand 32), (W 24)⟩,
    ⟨(.reg 15 : Operand 32), (W 17)⟩,
    ⟨(.mem (stack + 4) : Operand 32), (W 21)⟩,
    ⟨(.mem (stack + 8) : Operand 32), (W 20)⟩,
    ⟨(.mem (stack + 16) : Operand 32), (W 13)⟩,
    ⟨(.mem (stack + 24) : Operand 32), (W 26)⟩,
    ⟨(.mem (stack + 32) : Operand 32), (W 22)⟩,
    ⟨(.mem (stack + 40) : Operand 32), (W 23)⟩,
    ⟨(.mem (stack + 48) : Operand 32), (W 15)⟩,
    ⟨(.mem (stack + 56) : Operand 32), (W 19)⟩,
    ⟨(.mem (stack + 64) : Operand 64), input⟩,
    ⟨(.mem (stack + 72) : Operand 32), (W 14)⟩,
    ⟨(.mem (stack + 88) : Operand 32), (W 18)⟩,
    ⟨(.mem (stack + 96) : Operand 32), (W 12)⟩,
    ⟨(.mem (stack + 104) : Operand 32), (W 24)⟩,
    ⟨(.mem (stack + 116) : Operand 32), H[0]⟩,
    ⟨(.mem (stack + 120) : Operand 32), H[3]⟩,
    ⟨(.mem (stack + 124) : Operand 32), H[4]⟩,
    ⟨(.mem (stack + 144) : Operand 32), H[2]⟩,
    ⟨(.mem (stack + 152) : Operand 32), H[1]⟩]

private def genericCut028 (stack input : BitVec 64) (H : Vector (BitVec 32) 5)
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) : List Write :=
  [⟨(.reg 1 : Operand 32), (A 25)⟩,
    ⟨(.reg 2 : Operand 32), (A 26)⟩,
    ⟨(.reg 6 : Operand 32), ((A 24)).rotateLeft 30⟩,
    ⟨(.reg 7 : Operand 32), ((A 23)).rotateLeft 30⟩,
    ⟨(.reg 9 : Operand 32), ((W 26) + ((A 22)).rotateLeft 30)⟩,
    ⟨(.reg 10 : Operand 32), (W 27)⟩,
    ⟨(.reg 11 : Operand 32), (W 22)⟩,
    ⟨(.reg 12 : Operand 32), (W 16)⟩,
    ⟨(.reg 15 : Operand 32), (W 17)⟩,
    ⟨(.mem (stack + 0) : Operand 32), (W 25)⟩,
    ⟨(.mem (stack + 4) : Operand 32), (W 21)⟩,
    ⟨(.mem (stack + 8) : Operand 32), (W 20)⟩,
    ⟨(.mem (stack + 16) : Operand 32), (W 13)⟩,
    ⟨(.mem (stack + 24) : Operand 32), (W 26)⟩,
    ⟨(.mem (stack + 32) : Operand 32), (W 22)⟩,
    ⟨(.mem (stack + 40) : Operand 32), (W 23)⟩,
    ⟨(.mem (stack + 48) : Operand 32), (W 15)⟩,
    ⟨(.mem (stack + 56) : Operand 32), (W 19)⟩,
    ⟨(.mem (stack + 64) : Operand 64), input⟩,
    ⟨(.mem (stack + 72) : Operand 32), (W 14)⟩,
    ⟨(.mem (stack + 88) : Operand 32), (W 18)⟩,
    ⟨(.mem (stack + 96) : Operand 32), (W 12)⟩,
    ⟨(.mem (stack + 104) : Operand 32), (W 24)⟩,
    ⟨(.mem (stack + 116) : Operand 32), H[0]⟩,
    ⟨(.mem (stack + 120) : Operand 32), H[3]⟩,
    ⟨(.mem (stack + 124) : Operand 32), H[4]⟩,
    ⟨(.mem (stack + 144) : Operand 32), H[2]⟩,
    ⟨(.mem (stack + 152) : Operand 32), H[1]⟩]

private def genericCut029 (stack input : BitVec 64) (H : Vector (BitVec 32) 5)
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) : List Write :=
  [⟨(.reg 0 : Operand 32), (A 27)⟩,
    ⟨(.reg 1 : Operand 32), ((A 25)).rotateLeft 30⟩,
    ⟨(.reg 2 : Operand 32), ((A 26)).rotateLeft 30⟩,
    ⟨(.reg 6 : Operand 32), ((A 24)).rotateLeft 30⟩,
    ⟨(.reg 7 : Operand 32), ((W 27) + ((A 23)).rotateLeft 30 + ((A 26) ^^^ ((A 24)).rotateLeft 30 ^^^ ((A 25)).rotateLeft 30))⟩,
    ⟨(.reg 8 : Operand 32), (W 14)⟩,
    ⟨(.reg 10 : Operand 32), (W 27)⟩,
    ⟨(.reg 11 : Operand 32), (W 22)⟩,
    ⟨(.reg 12 : Operand 32), (W 16)⟩,
    ⟨(.reg 15 : Operand 32), (W 17)⟩,
    ⟨(.mem (stack + 0) : Operand 32), (W 25)⟩,
    ⟨(.mem (stack + 4) : Operand 32), (W 21)⟩,
    ⟨(.mem (stack + 8) : Operand 32), (W 20)⟩,
    ⟨(.mem (stack + 16) : Operand 32), (W 13)⟩,
    ⟨(.mem (stack + 24) : Operand 32), (W 26)⟩,
    ⟨(.mem (stack + 32) : Operand 32), (W 22)⟩,
    ⟨(.mem (stack + 40) : Operand 32), (W 23)⟩,
    ⟨(.mem (stack + 48) : Operand 32), (W 15)⟩,
    ⟨(.mem (stack + 56) : Operand 32), (W 19)⟩,
    ⟨(.mem (stack + 64) : Operand 64), input⟩,
    ⟨(.mem (stack + 80) : Operand 32), (W 27)⟩,
    ⟨(.mem (stack + 88) : Operand 32), (W 18)⟩,
    ⟨(.mem (stack + 96) : Operand 32), (W 12)⟩,
    ⟨(.mem (stack + 104) : Operand 32), (W 24)⟩,
    ⟨(.mem (stack + 116) : Operand 32), H[0]⟩,
    ⟨(.mem (stack + 120) : Operand 32), H[3]⟩,
    ⟨(.mem (stack + 124) : Operand 32), H[4]⟩,
    ⟨(.mem (stack + 144) : Operand 32), H[2]⟩,
    ⟨(.mem (stack + 152) : Operand 32), H[1]⟩]

private def genericCut030 (stack input : BitVec 64) (H : Vector (BitVec 32) 5)
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) : List Write :=
  [⟨(.reg 0 : Operand 32), (A 28)⟩,
    ⟨(.reg 1 : Operand 32), ((A 25)).rotateLeft 30⟩,
    ⟨(.reg 2 : Operand 32), ((A 27) ^^^ ((A 25)).rotateLeft 30 ^^^ ((A 26)).rotateLeft 30)⟩,
    ⟨(.reg 3 : Operand 32), ((W 12) ^^^ (W 14))⟩,
    ⟨(.reg 5 : Operand 32), (((A 26)).rotateLeft 30 ^^^ ((A 27)).rotateLeft 30)⟩,
    ⟨(.reg 6 : Operand 32), ((A 24)).rotateLeft 30⟩,
    ⟨(.reg 8 : Operand 32), ((A 27)).rotateLeft 30⟩,
    ⟨(.reg 12 : Operand 32), (W 16)⟩,
    ⟨(.reg 13 : Operand 32), ((W 30) + ((A 26)).rotateLeft 30)⟩,
    ⟨(.reg 15 : Operand 32), (W 17)⟩,
    ⟨(.mem (stack + 0) : Operand 32), (W 25)⟩,
    ⟨(.mem (stack + 4) : Operand 32), (W 21)⟩,
    ⟨(.mem (stack + 8) : Operand 32), (W 20)⟩,
    ⟨(.mem (stack + 16) : Operand 32), (W 13)⟩,
    ⟨(.mem (stack + 24) : Operand 32), (W 26)⟩,
    ⟨(.mem (stack + 32) : Operand 32), (W 22)⟩,
    ⟨(.mem (stack + 40) : Operand 32), (W 23)⟩,
    ⟨(.mem (stack + 48) : Operand 32), (W 15)⟩,
    ⟨(.mem (stack + 56) : Operand 32), (W 19)⟩,
    ⟨(.mem (stack + 64) : Operand 64), input⟩,
    ⟨(.mem (stack + 72) : Operand 32), (W 30)⟩,
    ⟨(.mem (stack + 80) : Operand 32), (W 27)⟩,
    ⟨(.mem (stack + 88) : Operand 32), (W 18)⟩,
    ⟨(.mem (stack + 104) : Operand 32), (W 24)⟩,
    ⟨(.mem (stack + 116) : Operand 32), H[0]⟩,
    ⟨(.mem (stack + 120) : Operand 32), H[3]⟩,
    ⟨(.mem (stack + 124) : Operand 32), H[4]⟩,
    ⟨(.mem (stack + 144) : Operand 32), H[2]⟩,
    ⟨(.mem (stack + 152) : Operand 32), H[1]⟩]

private def genericCut031 (stack input : BitVec 64) (H : Vector (BitVec 32) 5)
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) : List Write :=
  [⟨(.reg 0 : Operand 32), (A 28)⟩,
    ⟨(.reg 1 : Operand 32), ((W 29) + ((A 25)).rotateLeft 30)⟩,
    ⟨(.reg 2 : Operand 32), (W 15)⟩,
    ⟨(.reg 3 : Operand 32), (W 28)⟩,
    ⟨(.reg 5 : Operand 32), ((A 28) ^^^ ((A 26)).rotateLeft 30 ^^^ ((A 27)).rotateLeft 30)⟩,
    ⟨(.reg 8 : Operand 32), ((A 27)).rotateLeft 30⟩,
    ⟨(.reg 9 : Operand 32), (A 29)⟩,
    ⟨(.reg 10 : Operand 32), (W 26)⟩,
    ⟨(.reg 11 : Operand 32), (W 29)⟩,
    ⟨(.reg 12 : Operand 32), (W 16)⟩,
    ⟨(.reg 13 : Operand 32), ((W 30) + ((A 26)).rotateLeft 30)⟩,
    ⟨(.reg 14 : Operand 32), (W 20)⟩,
    ⟨(.reg 15 : Operand 32), (W 17)⟩,
    ⟨(.mem (stack + 0) : Operand 32), (W 25)⟩,
    ⟨(.mem (stack + 4) : Operand 32), (W 21)⟩,
    ⟨(.mem (stack + 8) : Operand 32), (W 20)⟩,
    ⟨(.mem (stack + 24) : Operand 32), (W 26)⟩,
    ⟨(.mem (stack + 32) : Operand 32), (W 22)⟩,
    ⟨(.mem (stack + 40) : Operand 32), (W 23)⟩,
    ⟨(.mem (stack + 56) : Operand 32), (W 19)⟩,
    ⟨(.mem (stack + 64) : Operand 64), input⟩,
    ⟨(.mem (stack + 72) : Operand 32), (W 30)⟩,
    ⟨(.mem (stack + 80) : Operand 32), (W 27)⟩,
    ⟨(.mem (stack + 88) : Operand 32), (W 18)⟩,
    ⟨(.mem (stack + 96) : Operand 32), (W 28)⟩,
    ⟨(.mem (stack + 104) : Operand 32), (W 24)⟩,
    ⟨(.mem (stack + 116) : Operand 32), H[0]⟩,
    ⟨(.mem (stack + 120) : Operand 32), H[3]⟩,
    ⟨(.mem (stack + 124) : Operand 32), H[4]⟩,
    ⟨(.mem (stack + 144) : Operand 32), H[2]⟩,
    ⟨(.mem (stack + 152) : Operand 32), H[1]⟩]

private def genericCut032 (stack input : BitVec 64) (H : Vector (BitVec 32) 5)
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) : List Write :=
  [⟨(.reg 0 : Operand 32), ((A 28)).rotateLeft 30⟩,
    ⟨(.reg 1 : Operand 32), (A 31)⟩,
    ⟨(.reg 2 : Operand 32), (W 31)⟩,
    ⟨(.reg 6 : Operand 32), ((W 31) + ((A 27)).rotateLeft 30)⟩,
    ⟨(.reg 7 : Operand 32), (A 30)⟩,
    ⟨(.reg 9 : Operand 32), (A 29)⟩,
    ⟨(.reg 10 : Operand 32), (W 26)⟩,
    ⟨(.reg 11 : Operand 32), (W 29)⟩,
    ⟨(.reg 12 : Operand 32), (W 16)⟩,
    ⟨(.reg 14 : Operand 32), (W 20)⟩,
    ⟨(.reg 15 : Operand 32), (W 17)⟩,
    ⟨(.mem (stack + 0) : Operand 32), (W 25)⟩,
    ⟨(.mem (stack + 4) : Operand 32), (W 21)⟩,
    ⟨(.mem (stack + 8) : Operand 32), (W 20)⟩,
    ⟨(.mem (stack + 16) : Operand 32), (W 29)⟩,
    ⟨(.mem (stack + 24) : Operand 32), (W 26)⟩,
    ⟨(.mem (stack + 32) : Operand 32), (W 22)⟩,
    ⟨(.mem (stack + 40) : Operand 32), (W 23)⟩,
    ⟨(.mem (stack + 48) : Operand 32), (W 31)⟩,
    ⟨(.mem (stack + 56) : Operand 32), (W 19)⟩,
    ⟨(.mem (stack + 64) : Operand 64), input⟩,
    ⟨(.mem (stack + 72) : Operand 32), (W 30)⟩,
    ⟨(.mem (stack + 80) : Operand 32), (W 27)⟩,
    ⟨(.mem (stack + 88) : Operand 32), (W 18)⟩,
    ⟨(.mem (stack + 96) : Operand 32), (W 28)⟩,
    ⟨(.mem (stack + 104) : Operand 32), (W 24)⟩,
    ⟨(.mem (stack + 116) : Operand 32), H[0]⟩,
    ⟨(.mem (stack + 120) : Operand 32), H[3]⟩,
    ⟨(.mem (stack + 124) : Operand 32), H[4]⟩,
    ⟨(.mem (stack + 144) : Operand 32), H[2]⟩,
    ⟨(.mem (stack + 152) : Operand 32), H[1]⟩]

private def genericCut033 (stack input : BitVec 64) (H : Vector (BitVec 32) 5)
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) : List Write :=
  [⟨(.reg 0 : Operand 32), ((A 28)).rotateLeft 30⟩,
    ⟨(.reg 1 : Operand 32), (A 31)⟩,
    ⟨(.reg 5 : Operand 32), ((A 31)).rotateLeft 30⟩,
    ⟨(.reg 6 : Operand 32), ((A 31)).rotateLeft 30⟩,
    ⟨(.reg 7 : Operand 32), ((A 30)).rotateLeft 30⟩,
    ⟨(.reg 8 : Operand 32), ((W 31) + ((A 27)).rotateLeft 30 + ((A 30) ^^^ ((A 28)).rotateLeft 30 ^^^ ((A 29)).rotateLeft 30))⟩,
    ⟨(.reg 9 : Operand 32), ((A 29)).rotateLeft 30⟩,
    ⟨(.reg 11 : Operand 32), (W 29)⟩,
    ⟨(.reg 12 : Operand 32), ((W 16) ^^^ (W 18))⟩,
    ⟨(.reg 13 : Operand 32), (W 34)⟩,
    ⟨(.reg 15 : Operand 32), (W 17)⟩,
    ⟨(.mem (stack + 0) : Operand 32), (W 25)⟩,
    ⟨(.mem (stack + 4) : Operand 32), (W 21)⟩,
    ⟨(.mem (stack + 8) : Operand 32), (W 20)⟩,
    ⟨(.mem (stack + 16) : Operand 32), (W 29)⟩,
    ⟨(.mem (stack + 24) : Operand 32), (W 26)⟩,
    ⟨(.mem (stack + 32) : Operand 32), (W 22)⟩,
    ⟨(.mem (stack + 40) : Operand 32), (W 23)⟩,
    ⟨(.mem (stack + 48) : Operand 32), (W 31)⟩,
    ⟨(.mem (stack + 56) : Operand 32), (W 19)⟩,
    ⟨(.mem (stack + 64) : Operand 64), input⟩,
    ⟨(.mem (stack + 72) : Operand 32), (W 30)⟩,
    ⟨(.mem (stack + 80) : Operand 32), (W 27)⟩,
    ⟨(.mem (stack + 88) : Operand 32), (W 34)⟩,
    ⟨(.mem (stack + 96) : Operand 32), (W 28)⟩,
    ⟨(.mem (stack + 104) : Operand 32), (W 24)⟩,
    ⟨(.mem (stack + 116) : Operand 32), H[0]⟩,
    ⟨(.mem (stack + 120) : Operand 32), H[3]⟩,
    ⟨(.mem (stack + 124) : Operand 32), H[4]⟩,
    ⟨(.mem (stack + 144) : Operand 32), H[2]⟩,
    ⟨(.mem (stack + 152) : Operand 32), H[1]⟩]

private def genericCut034 (stack input : BitVec 64) (H : Vector (BitVec 32) 5)
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) : List Write :=
  [⟨(.reg 2 : Operand 32), (A 32)⟩,
    ⟨(.reg 5 : Operand 32), (((A 30)).rotateLeft 30 ^^^ ((A 31)).rotateLeft 30)⟩,
    ⟨(.reg 6 : Operand 32), ((A 31)).rotateLeft 30⟩,
    ⟨(.reg 9 : Operand 32), ((A 29)).rotateLeft 30⟩,
    ⟨(.reg 10 : Operand 32), ((W 34) + ((A 30)).rotateLeft 30)⟩,
    ⟨(.reg 11 : Operand 32), (A 33)⟩,
    ⟨(.reg 12 : Operand 32), (W 32)⟩,
    ⟨(.reg 14 : Operand 32), (W 24)⟩,
    ⟨(.reg 15 : Operand 32), (W 17)⟩,
    ⟨(.mem (stack + 0) : Operand 32), (W 25)⟩,
    ⟨(.mem (stack + 4) : Operand 32), (W 21)⟩,
    ⟨(.mem (stack + 8) : Operand 32), (W 20)⟩,
    ⟨(.mem (stack + 12) : Operand 32), (W 32)⟩,
    ⟨(.mem (stack + 16) : Operand 32), (W 29)⟩,
    ⟨(.mem (stack + 24) : Operand 32), (W 26)⟩,
    ⟨(.mem (stack + 32) : Operand 32), (W 22)⟩,
    ⟨(.mem (stack + 40) : Operand 32), (W 23)⟩,
    ⟨(.mem (stack + 48) : Operand 32), (W 31)⟩,
    ⟨(.mem (stack + 56) : Operand 32), (W 19)⟩,
    ⟨(.mem (stack + 64) : Operand 64), input⟩,
    ⟨(.mem (stack + 72) : Operand 32), (W 30)⟩,
    ⟨(.mem (stack + 80) : Operand 32), (W 27)⟩,
    ⟨(.mem (stack + 88) : Operand 32), (W 34)⟩,
    ⟨(.mem (stack + 96) : Operand 32), (W 28)⟩,
    ⟨(.mem (stack + 116) : Operand 32), H[0]⟩,
    ⟨(.mem (stack + 120) : Operand 32), H[3]⟩,
    ⟨(.mem (stack + 124) : Operand 32), H[4]⟩,
    ⟨(.mem (stack + 144) : Operand 32), H[2]⟩,
    ⟨(.mem (stack + 152) : Operand 32), H[1]⟩]

private def genericCut035 (stack input : BitVec 64) (H : Vector (BitVec 32) 5)
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) : List Write :=
  [⟨(.reg 1 : Operand 32), (W 19)⟩,
    ⟨(.reg 2 : Operand 32), (A 32)⟩,
    ⟨(.reg 3 : Operand 32), (W 30)⟩,
    ⟨(.reg 6 : Operand 32), ((A 31)).rotateLeft 30⟩,
    ⟨(.reg 7 : Operand 32), (A 34)⟩,
    ⟨(.reg 10 : Operand 32), ((W 34) + ((A 30)).rotateLeft 30)⟩,
    ⟨(.reg 11 : Operand 32), (A 33)⟩,
    ⟨(.reg 12 : Operand 32), (W 32)⟩,
    ⟨(.reg 13 : Operand 32), (W 25)⟩,
    ⟨(.reg 14 : Operand 32), (W 24)⟩,
    ⟨(.reg 15 : Operand 32), (W 33)⟩,
    ⟨(.mem (stack + 0) : Operand 32), (W 25)⟩,
    ⟨(.mem (stack + 4) : Operand 32), (W 21)⟩,
    ⟨(.mem (stack + 8) : Operand 32), (W 20)⟩,
    ⟨(.mem (stack + 12) : Operand 32), (W 32)⟩,
    ⟨(.mem (stack + 16) : Operand 32), (W 29)⟩,
    ⟨(.mem (stack + 24) : Operand 32), (W 26)⟩,
    ⟨(.mem (stack + 32) : Operand 32), (W 22)⟩,
    ⟨(.mem (stack + 40) : Operand 32), (W 23)⟩,
    ⟨(.mem (stack + 48) : Operand 32), (W 31)⟩,
    ⟨(.mem (stack + 64) : Operand 64), input⟩,
    ⟨(.mem (stack + 72) : Operand 32), (W 30)⟩,
    ⟨(.mem (stack + 80) : Operand 32), (W 27)⟩,
    ⟨(.mem (stack + 88) : Operand 32), (W 34)⟩,
    ⟨(.mem (stack + 96) : Operand 32), (W 28)⟩,
    ⟨(.mem (stack + 116) : Operand 32), H[0]⟩,
    ⟨(.mem (stack + 120) : Operand 32), H[3]⟩,
    ⟨(.mem (stack + 124) : Operand 32), H[4]⟩,
    ⟨(.mem (stack + 144) : Operand 32), H[2]⟩,
    ⟨(.mem (stack + 152) : Operand 32), H[1]⟩]

private def genericCut036 (stack input : BitVec 64) (H : Vector (BitVec 32) 5)
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) : List Write :=
  [⟨(.reg 0 : Operand 32), ((A 33)).rotateLeft 30⟩,
    ⟨(.reg 2 : Operand 32), ((A 32)).rotateLeft 30⟩,
    ⟨(.reg 3 : Operand 32), (W 30)⟩,
    ⟨(.reg 6 : Operand 32), ((W 34) + ((A 30)).rotateLeft 30 + ((A 33) ^^^ ((A 31)).rotateLeft 30 ^^^ ((A 32)).rotateLeft 30))⟩,
    ⟨(.reg 7 : Operand 32), (A 34)⟩,
    ⟨(.reg 8 : Operand 32), ((A 34)).rotateLeft 5⟩,
    ⟨(.reg 9 : Operand 32), (W 35)⟩,
    ⟨(.reg 11 : Operand 32), ((A 33)).rotateLeft 30⟩,
    ⟨(.reg 12 : Operand 32), ((W 35) + ((A 31)).rotateLeft 30)⟩,
    ⟨(.reg 13 : Operand 32), (W 25)⟩,
    ⟨(.reg 14 : Operand 32), (W 24)⟩,
    ⟨(.reg 15 : Operand 32), (W 33)⟩,
    ⟨(.mem (stack + 0) : Operand 32), (W 25)⟩,
    ⟨(.mem (stack + 4) : Operand 32), (W 21)⟩,
    ⟨(.mem (stack + 8) : Operand 32), (W 20)⟩,
    ⟨(.mem (stack + 12) : Operand 32), (W 32)⟩,
    ⟨(.mem (stack + 16) : Operand 32), (W 29)⟩,
    ⟨(.mem (stack + 24) : Operand 32), (W 26)⟩,
    ⟨(.mem (stack + 32) : Operand 32), (W 22)⟩,
    ⟨(.mem (stack + 40) : Operand 32), (W 23)⟩,
    ⟨(.mem (stack + 48) : Operand 32), (W 31)⟩,
    ⟨(.mem (stack + 56) : Operand 32), (W 35)⟩,
    ⟨(.mem (stack + 64) : Operand 64), input⟩,
    ⟨(.mem (stack + 72) : Operand 32), (W 30)⟩,
    ⟨(.mem (stack + 80) : Operand 32), (W 27)⟩,
    ⟨(.mem (stack + 88) : Operand 32), (W 34)⟩,
    ⟨(.mem (stack + 96) : Operand 32), (W 28)⟩,
    ⟨(.mem (stack + 116) : Operand 32), H[0]⟩,
    ⟨(.mem (stack + 120) : Operand 32), H[3]⟩,
    ⟨(.mem (stack + 124) : Operand 32), H[4]⟩,
    ⟨(.mem (stack + 144) : Operand 32), H[2]⟩,
    ⟨(.mem (stack + 152) : Operand 32), H[1]⟩]

private def genericCut037 (stack input : BitVec 64) (H : Vector (BitVec 32) 5)
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) : List Write :=
  [⟨(.reg 0 : Operand 32), ((A 34) ^^^ ((A 32)).rotateLeft 30 ^^^ ((A 33)).rotateLeft 30)⟩,
    ⟨(.reg 1 : Operand 32), (A 35)⟩,
    ⟨(.reg 2 : Operand 32), ((A 32)).rotateLeft 30⟩,
    ⟨(.reg 6 : Operand 32), (((A 34)).rotateLeft 30 ^^^ ((A 35)).rotateLeft 30)⟩,
    ⟨(.reg 7 : Operand 32), ((A 34)).rotateLeft 30⟩,
    ⟨(.reg 8 : Operand 32), ((A 35)).rotateLeft 30⟩,
    ⟨(.reg 9 : Operand 32), (W 38)⟩,
    ⟨(.reg 10 : Operand 32), ((W 20) ^^^ (W 22))⟩,
    ⟨(.reg 11 : Operand 32), ((A 33)).rotateLeft 30⟩,
    ⟨(.reg 12 : Operand 32), ((W 35) + ((A 31)).rotateLeft 30)⟩,
    ⟨(.reg 13 : Operand 32), (W 25)⟩,
    ⟨(.reg 14 : Operand 32), (W 24)⟩,
    ⟨(.reg 15 : Operand 32), (W 33)⟩,
    ⟨(.mem (stack + 0) : Operand 32), (W 25)⟩,
    ⟨(.mem (stack + 4) : Operand 32), (W 21)⟩,
    ⟨(.mem (stack + 12) : Operand 32), (W 32)⟩,
    ⟨(.mem (stack + 16) : Operand 32), (W 29)⟩,
    ⟨(.mem (stack + 24) : Operand 32), (W 26)⟩,
    ⟨(.mem (stack + 32) : Operand 32), (W 38)⟩,
    ⟨(.mem (stack + 40) : Operand 32), (W 23)⟩,
    ⟨(.mem (stack + 48) : Operand 32), (W 31)⟩,
    ⟨(.mem (stack + 56) : Operand 32), (W 35)⟩,
    ⟨(.mem (stack + 64) : Operand 64), input⟩,
    ⟨(.mem (stack + 72) : Operand 32), (W 30)⟩,
    ⟨(.mem (stack + 80) : Operand 32), (W 27)⟩,
    ⟨(.mem (stack + 88) : Operand 32), (W 34)⟩,
    ⟨(.mem (stack + 96) : Operand 32), (W 28)⟩,
    ⟨(.mem (stack + 116) : Operand 32), H[0]⟩,
    ⟨(.mem (stack + 120) : Operand 32), H[3]⟩,
    ⟨(.mem (stack + 124) : Operand 32), H[4]⟩,
    ⟨(.mem (stack + 144) : Operand 32), H[2]⟩,
    ⟨(.mem (stack + 152) : Operand 32), H[1]⟩]

private def genericCut038 (stack input : BitVec 64) (H : Vector (BitVec 32) 5)
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) : List Write :=
  [⟨(.reg 0 : Operand 32), (W 23)⟩,
    ⟨(.reg 1 : Operand 32), (W 36)⟩,
    ⟨(.reg 5 : Operand 32), ((W 38) + ((A 34)).rotateLeft 30)⟩,
    ⟨(.reg 6 : Operand 32), (((A 34)).rotateLeft 30 ^^^ ((A 35)).rotateLeft 30)⟩,
    ⟨(.reg 8 : Operand 32), ((A 35)).rotateLeft 30⟩,
    ⟨(.reg 9 : Operand 32), (A 36)⟩,
    ⟨(.reg 10 : Operand 32), (A 37)⟩,
    ⟨(.reg 11 : Operand 32), ((A 33)).rotateLeft 30⟩,
    ⟨(.reg 12 : Operand 32), (W 28)⟩,
    ⟨(.reg 13 : Operand 32), (W 25)⟩,
    ⟨(.reg 14 : Operand 32), (W 24)⟩,
    ⟨(.reg 15 : Operand 32), (W 33)⟩,
    ⟨(.mem (stack + 0) : Operand 32), (W 25)⟩,
    ⟨(.mem (stack + 4) : Operand 32), (W 21)⟩,
    ⟨(.mem (stack + 8) : Operand 32), (W 36)⟩,
    ⟨(.mem (stack + 12) : Operand 32), (W 32)⟩,
    ⟨(.mem (stack + 16) : Operand 32), (W 29)⟩,
    ⟨(.mem (stack + 24) : Operand 32), (W 26)⟩,
    ⟨(.mem (stack + 32) : Operand 32), (W 38)⟩,
    ⟨(.mem (stack + 48) : Operand 32), (W 31)⟩,
    ⟨(.mem (stack + 56) : Operand 32), (W 35)⟩,
    ⟨(.mem (stack + 64) : Operand 64), input⟩,
    ⟨(.mem (stack + 72) : Operand 32), (W 30)⟩,
    ⟨(.mem (stack + 80) : Operand 32), (W 27)⟩,
    ⟨(.mem (stack + 88) : Operand 32), (W 34)⟩,
    ⟨(.mem (stack + 96) : Operand 32), (W 28)⟩,
    ⟨(.mem (stack + 116) : Operand 32), H[0]⟩,
    ⟨(.mem (stack + 120) : Operand 32), H[3]⟩,
    ⟨(.mem (stack + 124) : Operand 32), H[4]⟩,
    ⟨(.mem (stack + 144) : Operand 32), H[2]⟩,
    ⟨(.mem (stack + 152) : Operand 32), H[1]⟩]

private def genericCut039 (stack input : BitVec 64) (H : Vector (BitVec 32) 5)
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) : List Write :=
  [⟨(.reg 3 : Operand 32), (W 34)⟩,
    ⟨(.reg 5 : Operand 32), ((W 38) + ((A 34)).rotateLeft 30)⟩,
    ⟨(.reg 6 : Operand 32), (A 38)⟩,
    ⟨(.reg 7 : Operand 32), (W 39)⟩,
    ⟨(.reg 8 : Operand 32), ((A 35)).rotateLeft 30⟩,
    ⟨(.reg 9 : Operand 32), (A 36)⟩,
    ⟨(.reg 10 : Operand 32), (A 37)⟩,
    ⟨(.reg 12 : Operand 32), (W 28)⟩,
    ⟨(.reg 13 : Operand 32), (W 29)⟩,
    ⟨(.reg 14 : Operand 32), (W 24)⟩,
    ⟨(.reg 15 : Operand 32), (W 33)⟩,
    ⟨(.mem (stack + 0) : Operand 32), (W 25)⟩,
    ⟨(.mem (stack + 4) : Operand 32), (W 37)⟩,
    ⟨(.mem (stack + 8) : Operand 32), (W 36)⟩,
    ⟨(.mem (stack + 12) : Operand 32), (W 32)⟩,
    ⟨(.mem (stack + 24) : Operand 32), (W 26)⟩,
    ⟨(.mem (stack + 32) : Operand 32), (W 38)⟩,
    ⟨(.mem (stack + 48) : Operand 32), (W 31)⟩,
    ⟨(.mem (stack + 56) : Operand 32), (W 35)⟩,
    ⟨(.mem (stack + 64) : Operand 64), input⟩,
    ⟨(.mem (stack + 72) : Operand 32), (W 30)⟩,
    ⟨(.mem (stack + 80) : Operand 32), (W 27)⟩,
    ⟨(.mem (stack + 88) : Operand 32), (W 34)⟩,
    ⟨(.mem (stack + 96) : Operand 32), (W 28)⟩,
    ⟨(.mem (stack + 116) : Operand 32), H[0]⟩,
    ⟨(.mem (stack + 120) : Operand 32), H[3]⟩,
    ⟨(.mem (stack + 124) : Operand 32), H[4]⟩,
    ⟨(.mem (stack + 144) : Operand 32), H[2]⟩,
    ⟨(.mem (stack + 152) : Operand 32), H[1]⟩]

def bytes027 : List UInt8 :=
  [0xd1, 0xc2, 0x89, 0x14, 0x24, 0x31, 0xf5, 0x01, 0xd0, 0x01, 0xe8, 0x4c, 0x89, 0xc2, 0x31, 0xda, 0x33, 0x54, 0x24, 0x38, 0x44, 0x31, 0xf2, 0xd1, 0xc2, 0x49, 0x89, 0xd2, 0x89, 0xca, 0xc1, 0xc2, 0x05, 0xc1, 0xc6, 0x1e, 0x01, 0xc2, 0x81, 0xc2, 0xa1, 0xeb, 0xd9, 0x6e]

set_option maxHeartbeats 800000 in
def effect027 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (rolR32Effect 0x102a8f 2 2 1) (movM32R32LowEffect 0x102a91 2 (.sib 4 none 0 .none))) (xorR32R32Effect 0x102a94 2 5 6)) (addR32R32Effect 0x102a96 2 0 2)) (addR32R32Effect 0x102a98 2 0 5)) (movR64R64Effect 0x102a9a 2 8)) (xorR32R32Effect 0x102a9d 2 2 3)) (xorR32M32LowEffect 0x102a9f 2 (.sib 4 none 0 (.d8 0x38)))) (xorR32R32Effect 0x102aa3 3 2 14)) (rolR32Effect 0x102aa6 2 2 1)) (movR64R64Effect 0x102aa8 10 2)) (movR32R32Effect 0x102aab 2 2 1)) (rolR32Effect 0x102aad 3 2 5)) (rolR32Effect 0x102ab0 3 6 30)) (addR32R32Effect 0x102ab3 2 2 0)) (addR32Imm32Effect 0x102ab5 6 2 0x6ed9eba1)

set_option maxHeartbeats 800000 in
theorem block027 [Bindings] (boundary : ReturnBoundary) (stack input : BitVec 64)
    (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes027.length →
      0x102a8f + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x102a8f ∧ FrameData stack input M s ∧
        Write.AllHold s (cut027 stack input H M))
      (codeRange 0x102a8f bytes027) effect027 := by
  unfold bytes027 at hout ⊢
  sha1_run_begin (rol_r32_one_effect_step 0x102a8f 0xc2 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m32_r32_low_effect_step 0x102a91 2 (.sib 4 none 0 .none) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (xor_r32_r32_effect_step 0x102a94 0xf5 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (add_r32_r32_effect_step 0x102a96 0xd0 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (add_r32_r32_effect_step 0x102a98 0xe8 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (mov_r64_r64_effect_step 0x102a9a 0x4c 0xc2 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (xor_r32_r32_effect_step 0x102a9d 0xda (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (xor_r32_m32_low_effect_step 0x102a9f 2 (.sib 4 none 0 (.d8 0x38)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102aa3 0x44 0xf2 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (rol_r32_one_effect_step 0x102aa6 0xc2 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (mov_r64_r64_effect_step 0x102aa8 0x49 0xd2 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (mov_r32_r32_effect_step 0x102aab 0xca (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (rol_r32_imm8_effect_step 0x102aad 0xc2 0x5 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (rol_r32_imm8_effect_step 0x102ab0 0xc6 0x1e (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (add_r32_r32_effect_step 0x102ab3 0xc2 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (add_r32_imm32_effect_step 0x102ab5 0xc2 0x6ed9eba1 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_finish [effect027]

theorem effect027_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s)
    (he : (effect027 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have hfoot : ∀ c ∈ (effect027 s).components, c ∈ [.mem ((Operand.reg 4 : Operand 64).read s + BitVec.ofNat 64 0) 4, .reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] := by
    unfold effect027
    iterate 15 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [addR32Imm32Effect_components, addR32R32Effect_components, movM32R32LowEffect, storeEffect_components, movR32R32Effect_components, movR64R64Effect_components, rolR32Effect_components, xorR32M32LowEffect, xorR32R32Effect_components, List.mem_cons, List.not_mem_nil, or_false, or_imp, forall_and, forall_eq, or_true]
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only [x86_compose]
  have ha := he.agrees.mono hfoot
  rw [hs] at ha
  apply ha.widen
  · intro c hc hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all (config := {decide := true, implicitDefEqProofs := false}) only [Component.isMem, scratchComponents, x86_compose]
  · intro address c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hCov.elim
      | exact scratchComponents_stack (Or.inl (by decide +kernel)) hCov

theorem effect027_rip {s t : RamState}
    (he : (effect027 s).Holds s t) :
    t.RIP = 0x102abb := by
  exact he.rip.trans (by rfl)

section Words027
set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem genericWords027 {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) {s t : RamState}
    (hWork : A 26 = (A 25).rotateLeft 5 +
      (A 24 ^^^ (A 23).rotateLeft 30 ^^^ (A 22).rotateLeft 30) +
      (A 21).rotateLeft 30 + 0x6ed9eba1 + W 25)
    (hSchedule25 : W 25 = (W 11 ^^^ W 17 ^^^ W 22 ^^^ W 9).rotateLeft 1)
    (hSchedule27 : W 27 = (W 11 ^^^ W 13 ^^^ W 19 ^^^ W 24).rotateLeft 1)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (hw : Write.AllHold s (genericCut027 stack input H A W))
    (he : (effect027 s).Holds s t) :
    Write.AllHold t (genericCut028 stack input H A W) := by
  have hfull : ∀ w ∈ (effect027 s).writes, w.Full := by
    apply Effect.Local.full
    unfold effect027
    repeat' first | (solve | x86_local) | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  sha1_norm at hs
  simp only [genericCut027, Write.AllHold] at hw
  obtain ⟨h0, h1, h2, h3, h5, h6, h7, h8, h9, h11, h12, h14, h15,
    hM4, hM8, hM16, hM24, hM32, hM40, hM48, hM56, hM64, hM72, hM88,
    hM96, hM104, hM116, hM120, hM124, hM144, hM152⟩ := hw
  sha1_norm at h0 h1 h2 h3 h5 h6 h7 h8 h9 h11 h12 h14 h15
  sha1_norm at hM4 hM8 hM16 hM24 hM32 hM40 hM48 hM56 hM64 hM72 hM88 hM96 hM104 hM116 hM120 hM124 hM144 hM152
  simp only [genericCut028, Write.AllHold, ← ho.read_reg, ← ho.read_mem]
  sha1_norm [effect027, hs, h0, h1, h2, h3, h5, h6, h7, h8, h9, h11, h12,
    h14, h15, hM4, hM8, hM16, hM24, hM32, hM40, hM48, hM56, hM64,
    hM72, hM88, hM96, hM104, hM116, hM120, hM124, hM144, hM152, read32_memStore64_low, BitVec.setWidth_add, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
  rw [hWork, hSchedule25, hSchedule27]
  simp_all (config := {implicitDefEqProofs := false, decide := true})
  all_goals ac_rfl

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
theorem effect027_words {stack input : BitVec 64}
    {H : Vector (BitVec 32) 5} {M : Vector (BitVec 32) 16}
    {s t : RamState}
    (hf : FrameData stack input M s)
    (hw : Write.AllHold s (cut027 stack input H M))
    (he : (effect027 s).Holds s t) :
    Write.AllHold t (cut028 stack input H M) := by
  let A : Nat → BitVec 32 := fun n ↦ (workingAfter M H n).a
  let W : Fin 80 → BitVec 32 := scheduleWord M
  have hWork : A 26 = (A 25).rotateLeft 5 +
      (A 24 ^^^ (A 23).rotateLeft 30 ^^^ (A 22).rotateLeft 30) +
      (A 21).rotateLeft 30 + 0x6ed9eba1 + W 25 := by
    dsimp [A, W]
    rw [workingAfter_step_a_values M H 21 (by decide +kernel),
      sha1_f_parity_first (by decide +kernel) (by decide +kernel)]
    simp [K, Parity]
    all_goals ac_rfl
  have hSchedule25 : W 25 = (W 11 ^^^ W 17 ^^^ W 22 ^^^ W 9).rotateLeft 1 := by
    dsimp [W]
    change scheduleWord M (⟨25, by decide⟩ : Fin 80) = _
    rw [scheduleWord_recurrence M ⟨25, by decide⟩ (by decide)]
    simp only [Nat.reduceSub]
    rw [sha1Rotl_eq_rotateLeft 1 _ (by decide)]
    ac_rfl
  have hSchedule27 : W 27 = (W 11 ^^^ W 13 ^^^ W 19 ^^^ W 24).rotateLeft 1 := by
    dsimp [W]
    change scheduleWord M (⟨27, by decide⟩ : Fin 80) = _
    rw [scheduleWord_recurrence M ⟨27, by decide⟩ (by decide)]
    simp only [Nat.reduceSub]
    rw [sha1Rotl_eq_rotateLeft 1 _ (by decide)]
    ac_rfl
  have hpre : Write.AllHold s (genericCut027 stack input H A W) := by
    change Write.AllHold s (cut027 stack input H M)
    exact hw
  have hraw := genericWords027 A W hWork hSchedule25 hSchedule27 hf.stackPointer hpre he
  change Write.AllHold t (cut028 stack input H M)
  exact hraw
end Words027

theorem segment027 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x102a8f 0x102abb
      cut027 cut028 := by
  have hout : ∀ d : Nat, d ≤ bytes027.length →
      0x102a8f + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    simp only [bytes027, List.length_cons, List.length_nil] at hd
    apply outsideCompression_ne hOutside
    · change 0x1024e0 ≤ (0x102a8f + d % 2^64) % 2^64
      omega
    · change (0x102a8f + d % 2^64) % 2^64 < 0x1036df
      omega
  apply Segment.of_block (fun _ _ _ _ => effect027)
    (fun stack input H M => block027 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64
      0x2a8f) bytes027,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact effect027_rip he
  · intro stack input H M s t _ hf _ he
    exact effect027_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect027_words hf hw he


def bytes028 : List UInt8 :=
  [0x89, 0xd0, 0xc1, 0xc0, 0x5, 0x45, 0x8d, 0x4, 0x3a, 0x4c, 0x89, 0x54, 0x24, 0x50, 0x31, 0xf7, 0x31, 0xcf, 0x44, 0x1, 0xcf, 0x1, 0xf8, 0x5, 0xa1, 0xeb, 0xd9, 0x6e, 0xc1, 0xc1, 0x1e, 0x89, 0xcf, 0x31, 0xf7, 0x31, 0xd7, 0x44, 0x1, 0xc7, 0xc1, 0xc2, 0x1e, 0x4c, 0x8b, 0x44, 0x24, 0x48]

set_option maxHeartbeats 800000 in
def effect028 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq ((movR32R32Effect 0x102abb 2 0 2)) (rolR32Effect 0x102abd 3 0 5)) (leaR32Effect 0x102ac0 4 8 (.sib 10 (some 7) 0 .none))) (movM64R64Effect 0x102ac4 10 (.sib 4 none 0 (.d8 0x50)))) (xorR32R32Effect 0x102ac9 2 7 6)) (xorR32R32Effect 0x102acb 2 7 1)) (addR32R32Effect 0x102acd 3 7 9)) (addR32R32Effect 0x102ad0 2 0 7)) (addEaxImm32Effect 0x102ad2 0x6ed9eba1)) (rolR32Effect 0x102ad7 3 1 30)) (movR32R32Effect 0x102ada 2 7 1)) (xorR32R32Effect 0x102adc 2 7 6)) (xorR32R32Effect 0x102ade 2 7 2)) (addR32R32Effect 0x102ae0 3 7 8)) (rolR32Effect 0x102ae3 3 2 30)) (movR64M64Effect 0x102ae6 8 (.sib 4 none 0 (.d8 0x48)))

set_option maxHeartbeats 1600000 in
theorem block028 [Bindings] (boundary : ReturnBoundary)
    (stack input : BitVec 64) (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes028.length → 0x102abb + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x102abb ∧ FrameData stack input M s ∧
        Write.AllHold s (cut028 stack input H M))
      (codeRange 0x102abb bytes028) effect028 := by
  unfold bytes028 at hout ⊢
  sha1_run_begin (mov_r32_r32_effect_step 0x102abb 0xd0 (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x102abd 0xc0 0x5 (by decide +kernel) (by decide +kernel))
  sha1_run_then (lea_r32_rex_effect_step 0x102ac0 0x45 (by unfold RexNoWPrefix; decide +kernel) 0 (.sib 10 (some 7) 0 .none) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m64_r64_effect_step 0x102ac4 0x4c (by unfold RexWPrefix; decide +kernel) 2 (.sib 4 none 0 (.d8 0x50)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x102ac9 0xf7 (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x102acb 0xcf (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x102acd 0x44 0xcf (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_effect_step 0x102ad0 0xf8 (by decide +kernel))
  sha1_run_then (add_eax_imm32_effect_step 0x102ad2 0x6ed9eba1)
  sha1_run_then (rol_r32_imm8_effect_step 0x102ad7 0xc1 0x1e (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_effect_step 0x102ada 0xcf (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x102adc 0xf7 (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x102ade 0xd7 (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x102ae0 0x44 0xc7 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x102ae3 0xc2 0x1e (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r64_m64_effect_step 0x102ae6 0x4c (by unfold RexWPrefix; decide +kernel) 0 (.sib 4 none 0 (.d8 0x48)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_finish [effect028]



set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
theorem effect028_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s) (he : (effect028 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have hfoot : ∀ c ∈ (effect028 s).components, c ∈ [.mem ((Operand.reg 4 : Operand 64).read s + BitVec.ofNat 64 80) 8, .reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] := by
    unfold effect028
    iterate 15 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [movR32R32Effect_components, rolR32Effect_components, leaR32Effect_components, movM64R64Effect_components, xorR32R32Effect_components, addR32R32Effect_components, addEaxImm32Effect_components, movR64M64Effect_components, List.mem_cons, List.not_mem_nil, or_false,
        or_imp, forall_and, forall_eq, or_true]
    all_goals sha1_norm
  have ha := he.agrees.mono hfoot
  rw [hs] at ha
  apply ha.widen
  · intro c hc hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all (config := {decide := true, implicitDefEqProofs := false}) only
      [Component.isMem, scratchComponents, x86_compose]
  · intro address c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hCov.elim
      | exact scratchComponents_stack (Or.inl (by decide +kernel)) hCov

theorem effect028_rip {s t : RamState} (he : (effect028 s).Holds s t) :
    t.RIP = 0x102aeb := by
  exact he.rip.trans (by rfl)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem genericWords028 {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) {s t : RamState}
    (hA27 : A 27 = (A 26).rotateLeft 5 + (A 25 ^^^ (A 24).rotateLeft 30 ^^^ (A 23).rotateLeft 30) + (A 22).rotateLeft 30 + 0x6ed9eba1 + W 26)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (hw : Write.AllHold s (genericCut028 stack input H A W))
    (he : (effect028 s).Holds s t) :
    Write.AllHold t (genericCut029 stack input H A W) := by
  have hfull : ∀ w ∈ (effect028 s).writes, w.Full := by
    apply Effect.Local.full
    unfold effect028
    repeat' first | (solve | x86_local) | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  sha1_norm at hs
  simp only [genericCut028, Write.AllHold] at hw
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27⟩ := hw
  have h9low := (read32_of_read64_low (s := s) (a := (stack + 0))
    (v := (Operand.mem ((stack + 0)) : Operand 64).read s) rfl).symm.trans h9
  have h10low := (read32_of_read64_low (s := s) (a := (stack + 4))
    (v := (Operand.mem ((stack + 4)) : Operand 64).read s) rfl).symm.trans h10
  have h11low := (read32_of_read64_low (s := s) (a := (stack + 8))
    (v := (Operand.mem ((stack + 8)) : Operand 64).read s) rfl).symm.trans h11
  have h12low := (read32_of_read64_low (s := s) (a := (stack + 16))
    (v := (Operand.mem ((stack + 16)) : Operand 64).read s) rfl).symm.trans h12
  have h13low := (read32_of_read64_low (s := s) (a := (stack + 24))
    (v := (Operand.mem ((stack + 24)) : Operand 64).read s) rfl).symm.trans h13
  have h14low := (read32_of_read64_low (s := s) (a := (stack + 32))
    (v := (Operand.mem ((stack + 32)) : Operand 64).read s) rfl).symm.trans h14
  have h15low := (read32_of_read64_low (s := s) (a := (stack + 40))
    (v := (Operand.mem ((stack + 40)) : Operand 64).read s) rfl).symm.trans h15
  have h16low := (read32_of_read64_low (s := s) (a := (stack + 48))
    (v := (Operand.mem ((stack + 48)) : Operand 64).read s) rfl).symm.trans h16
  have h17low := (read32_of_read64_low (s := s) (a := (stack + 56))
    (v := (Operand.mem ((stack + 56)) : Operand 64).read s) rfl).symm.trans h17
  have h19low := (read32_of_read64_low (s := s) (a := (stack + 72))
    (v := (Operand.mem ((stack + 72)) : Operand 64).read s) rfl).symm.trans h19
  have h20low := (read32_of_read64_low (s := s) (a := (stack + 88))
    (v := (Operand.mem ((stack + 88)) : Operand 64).read s) rfl).symm.trans h20
  have h21low := (read32_of_read64_low (s := s) (a := (stack + 96))
    (v := (Operand.mem ((stack + 96)) : Operand 64).read s) rfl).symm.trans h21
  have h22low := (read32_of_read64_low (s := s) (a := (stack + 104))
    (v := (Operand.mem ((stack + 104)) : Operand 64).read s) rfl).symm.trans h22
  have h23low := (read32_of_read64_low (s := s) (a := (stack + 116))
    (v := (Operand.mem ((stack + 116)) : Operand 64).read s) rfl).symm.trans h23
  have h24low := (read32_of_read64_low (s := s) (a := (stack + 120))
    (v := (Operand.mem ((stack + 120)) : Operand 64).read s) rfl).symm.trans h24
  have h25low := (read32_of_read64_low (s := s) (a := (stack + 124))
    (v := (Operand.mem ((stack + 124)) : Operand 64).read s) rfl).symm.trans h25
  have h26low := (read32_of_read64_low (s := s) (a := (stack + 144))
    (v := (Operand.mem ((stack + 144)) : Operand 64).read s) rfl).symm.trans h26
  have h27low := (read32_of_read64_low (s := s) (a := (stack + 152))
    (v := (Operand.mem ((stack + 152)) : Operand 64).read s) rfl).symm.trans h27
  sha1_norm at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27
  simp only [genericCut029, Write.AllHold, ← ho.read_reg, ← ho.read_mem]
  sha1_norm [effect028, hs, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h9low, h10low, h11low, h12low, h13low, h14low, h15low, h16low, h17low, h19low, h20low, h21low, h22low, h23low, h24low, h25low, h26low, h27low,
    read32_memStore64_low, BitVec.setWidth_add, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, leaSpec]
  rw [hA27]
  all_goals sha1_norm [← BitVec.setWidth_eq_extractLsb' (by decide : 32 ≤ 64),
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
  simp_all (config := {implicitDefEqProofs := false, decide := true})
  all_goals repeat' first | (solve | ac_rfl) | apply And.intro

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
theorem effect028_words {stack input : BitVec 64}
    {H : Vector (BitVec 32) 5} {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s) (hw : Write.AllHold s (cut028 stack input H M))
    (he : (effect028 s).Holds s t) : Write.AllHold t (cut029 stack input H M) := by
  let A : Nat → BitVec 32 := fun n ↦ (workingAfter M H n).a
  let W : Fin 80 → BitVec 32 := scheduleWord M
  have hA27 : A 27 = (A 26).rotateLeft 5 + (A 25 ^^^ (A 24).rotateLeft 30 ^^^ (A 23).rotateLeft 30) + (A 22).rotateLeft 30 + 0x6ed9eba1 + W 26 := by
    dsimp [A, W]
    rw [workingAfter_step_a_values M H 22 (by decide +kernel),
      sha1_f_parity_first (by decide +kernel) (by decide +kernel)]
    simp [K, Parity]
  have hpre : Write.AllHold s (genericCut028 stack input H A W) := by
    change Write.AllHold s (cut028 stack input H M)
    exact hw
  have hraw := genericWords028 A W hA27 hf.stackPointer hpre he
  change Write.AllHold t (cut029 stack input H M)
  exact hraw

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
theorem segment028 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x102abb 0x102aeb cut028 cut029 := by
  have hout : ∀ d : Nat, d ≤ bytes028.length →
      0x102abb + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    simp only [bytes028, List.length_cons, List.length_nil] at hd
    apply outsideCompression_ne hOutside
    · change 0x1024e0 ≤ (0x102abb + d % 2^64) % 2^64
      omega
    · change (0x102abb + d % 2^64) % 2^64 < 0x1036df
      omega
  apply Segment.of_block (fun _ _ _ _ => effect028)
    (fun stack input H M => block028 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64 0x2abb) bytes028,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact effect028_rip he
  · intro stack input H M s t _ hf _ he
    exact effect028_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect028_words hf hw he

def bytes029 : List UInt8 :=
  [0x48, 0x8b, 0x5c, 0x24, 0x60, 0x44, 0x31, 0xc3, 0x45, 0x31, 0xe0, 0x45, 0x31, 0xd8, 0x45, 0x31, 0xd0, 0x41, 0xd1, 0xc0, 0x4d, 0x89, 0xc1, 0x4c, 0x89, 0x44, 0x24, 0x48, 0x41, 0x89, 0xc0, 0x41, 0xc1, 0xc0, 0x1e, 0x44, 0x89, 0xc5, 0x31, 0xd5, 0x45, 0x8d, 0x2c, 0x11, 0x31, 0xca, 0x31, 0xc2, 0xc1, 0xc0, 0x5, 0x1, 0xf8, 0x5, 0xa1, 0xeb, 0xd9, 0x6e]

set_option maxHeartbeats 800000 in
def effect029 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq ((movR64M64Effect 0x102aeb 3 (.sib 4 none 0 (.d8 0x60)))) (xorR32R32Effect 0x102af0 3 3 8)) (xorR32R32Effect 0x102af3 3 8 12)) (xorR32R32Effect 0x102af6 3 8 11)) (xorR32R32Effect 0x102af9 3 8 10)) (rolR32Effect 0x102afc 3 8 1)) (movR64R64Effect 0x102aff 9 8)) (movM64R64Effect 0x102b02 8 (.sib 4 none 0 (.d8 0x48)))) (movR32R32Effect 0x102b07 3 8 0)) (rolR32Effect 0x102b0a 4 8 30)) (movR32R32Effect 0x102b0e 3 5 8)) (xorR32R32Effect 0x102b11 2 5 2)) (leaR32Effect 0x102b13 4 13 (.sib 9 (some 2) 0 .none))) (xorR32R32Effect 0x102b17 2 2 1)) (xorR32R32Effect 0x102b19 2 2 0)) (rolR32Effect 0x102b1b 3 0 5)) (addR32R32Effect 0x102b1e 2 0 7)) (addEaxImm32Effect 0x102b20 0x6ed9eba1)

set_option maxHeartbeats 1600000 in
theorem block029 [Bindings] (boundary : ReturnBoundary)
    (stack input : BitVec 64) (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes029.length → 0x102aeb + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x102aeb ∧ FrameData stack input M s ∧
        Write.AllHold s (cut029 stack input H M))
      (codeRange 0x102aeb bytes029) effect029 := by
  unfold bytes029 at hout ⊢
  sha1_run_begin (mov_r64_m64_effect_step 0x102aeb 0x48 (by unfold RexWPrefix; decide +kernel) 3 (.sib 4 none 0 (.d8 0x60)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102af0 0x44 0xc3 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102af3 0x45 0xe0 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102af6 0x45 0xd8 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102af9 0x45 0xd0 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_one_rex_effect_step 0x102afc 0x41 0xc0 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r64_r64_effect_step 0x102aff 0x4d 0xc1 (by unfold RexWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m64_r64_effect_step 0x102b02 0x4c (by unfold RexWPrefix; decide +kernel) 0 (.sib 4 none 0 (.d8 0x48)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x102b07 0x41 0xc0 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_imm8_rex_effect_step 0x102b0a 0x41 0xc0 0x1e (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x102b0e 0x44 0xc5 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x102b11 0xd5 (by decide +kernel))
  sha1_run_then (lea_r32_rex_effect_step 0x102b13 0x45 (by unfold RexNoWPrefix; decide +kernel) 5 (.sib 9 (some 2) 0 .none) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x102b17 0xca (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x102b19 0xc2 (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x102b1b 0xc0 0x5 (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_effect_step 0x102b1e 0xf8 (by decide +kernel))
  sha1_run_then (add_eax_imm32_effect_step 0x102b20 0x6ed9eba1)
  sha1_run_finish [effect029]



set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
theorem effect029_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s) (he : (effect029 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have hfoot : ∀ c ∈ (effect029 s).components, c ∈ [.mem ((Operand.reg 4 : Operand 64).read s + BitVec.ofNat 64 72) 8, .reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] := by
    unfold effect029
    iterate 17 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [movR64M64Effect_components, xorR32R32Effect_components, rolR32Effect_components, movR64R64Effect_components, movM64R64Effect_components, movR32R32Effect_components, leaR32Effect_components, addR32R32Effect_components, addEaxImm32Effect_components, List.mem_cons, List.not_mem_nil, or_false,
        or_imp, forall_and, forall_eq, or_true]
    all_goals sha1_norm
  have ha := he.agrees.mono hfoot
  rw [hs] at ha
  apply ha.widen
  · intro c hc hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all (config := {decide := true, implicitDefEqProofs := false}) only
      [Component.isMem, scratchComponents, x86_compose]
  · intro address c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hCov.elim
      | exact scratchComponents_stack (Or.inl (by decide +kernel)) hCov

theorem effect029_rip {s t : RamState} (he : (effect029 s).Holds s t) :
    t.RIP = 0x102b25 := by
  exact he.rip.trans (by rfl)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem genericWords029 {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) {s t : RamState}
    (hA28 : A 28 = (A 27).rotateLeft 5 + (A 26 ^^^ (A 25).rotateLeft 30 ^^^ (A 24).rotateLeft 30) + (A 23).rotateLeft 30 + 0x6ed9eba1 + W 27)
    (hW30 : W 30 = (W 27 ^^^ W 22 ^^^ W 16 ^^^ W 14).rotateLeft 1)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (hw : Write.AllHold s (genericCut029 stack input H A W))
    (he : (effect029 s).Holds s t) :
    Write.AllHold t (genericCut030 stack input H A W) := by
  have hfull : ∀ w ∈ (effect029 s).writes, w.Full := by
    apply Effect.Local.full
    unfold effect029
    repeat' first | (solve | x86_local) | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  sha1_norm at hs
  simp only [genericCut029, Write.AllHold] at hw
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28⟩ := hw
  have h10low := (read32_of_read64_low (s := s) (a := (stack + 0))
    (v := (Operand.mem ((stack + 0)) : Operand 64).read s) rfl).symm.trans h10
  have h11low := (read32_of_read64_low (s := s) (a := (stack + 4))
    (v := (Operand.mem ((stack + 4)) : Operand 64).read s) rfl).symm.trans h11
  have h12low := (read32_of_read64_low (s := s) (a := (stack + 8))
    (v := (Operand.mem ((stack + 8)) : Operand 64).read s) rfl).symm.trans h12
  have h13low := (read32_of_read64_low (s := s) (a := (stack + 16))
    (v := (Operand.mem ((stack + 16)) : Operand 64).read s) rfl).symm.trans h13
  have h14low := (read32_of_read64_low (s := s) (a := (stack + 24))
    (v := (Operand.mem ((stack + 24)) : Operand 64).read s) rfl).symm.trans h14
  have h15low := (read32_of_read64_low (s := s) (a := (stack + 32))
    (v := (Operand.mem ((stack + 32)) : Operand 64).read s) rfl).symm.trans h15
  have h16low := (read32_of_read64_low (s := s) (a := (stack + 40))
    (v := (Operand.mem ((stack + 40)) : Operand 64).read s) rfl).symm.trans h16
  have h17low := (read32_of_read64_low (s := s) (a := (stack + 48))
    (v := (Operand.mem ((stack + 48)) : Operand 64).read s) rfl).symm.trans h17
  have h18low := (read32_of_read64_low (s := s) (a := (stack + 56))
    (v := (Operand.mem ((stack + 56)) : Operand 64).read s) rfl).symm.trans h18
  have h20low := (read32_of_read64_low (s := s) (a := (stack + 80))
    (v := (Operand.mem ((stack + 80)) : Operand 64).read s) rfl).symm.trans h20
  have h21low := (read32_of_read64_low (s := s) (a := (stack + 88))
    (v := (Operand.mem ((stack + 88)) : Operand 64).read s) rfl).symm.trans h21
  have h22low := (read32_of_read64_low (s := s) (a := (stack + 96))
    (v := (Operand.mem ((stack + 96)) : Operand 64).read s) rfl).symm.trans h22
  have h23low := (read32_of_read64_low (s := s) (a := (stack + 104))
    (v := (Operand.mem ((stack + 104)) : Operand 64).read s) rfl).symm.trans h23
  have h24low := (read32_of_read64_low (s := s) (a := (stack + 116))
    (v := (Operand.mem ((stack + 116)) : Operand 64).read s) rfl).symm.trans h24
  have h25low := (read32_of_read64_low (s := s) (a := (stack + 120))
    (v := (Operand.mem ((stack + 120)) : Operand 64).read s) rfl).symm.trans h25
  have h26low := (read32_of_read64_low (s := s) (a := (stack + 124))
    (v := (Operand.mem ((stack + 124)) : Operand 64).read s) rfl).symm.trans h26
  have h27low := (read32_of_read64_low (s := s) (a := (stack + 144))
    (v := (Operand.mem ((stack + 144)) : Operand 64).read s) rfl).symm.trans h27
  have h28low := (read32_of_read64_low (s := s) (a := (stack + 152))
    (v := (Operand.mem ((stack + 152)) : Operand 64).read s) rfl).symm.trans h28
  sha1_norm at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28
  simp only [genericCut030, Write.AllHold, ← ho.read_reg, ← ho.read_mem]
  sha1_norm [effect029, hs, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h10low, h11low, h12low, h13low, h14low, h15low, h16low, h17low, h18low, h20low, h21low, h22low, h23low, h24low, h25low, h26low, h27low, h28low,
    read32_memStore64_low, BitVec.setWidth_add, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, leaSpec]
  rw [hA28, hW30]
  all_goals sha1_norm [← BitVec.setWidth_eq_extractLsb' (by decide : 32 ≤ 64),
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
  simp_all (config := {implicitDefEqProofs := false, decide := true})
  all_goals repeat' first | (solve | ac_rfl) | apply And.intro

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
theorem effect029_words {stack input : BitVec 64}
    {H : Vector (BitVec 32) 5} {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s) (hw : Write.AllHold s (cut029 stack input H M))
    (he : (effect029 s).Holds s t) : Write.AllHold t (cut030 stack input H M) := by
  let A : Nat → BitVec 32 := fun n ↦ (workingAfter M H n).a
  let W : Fin 80 → BitVec 32 := scheduleWord M
  have hA28 : A 28 = (A 27).rotateLeft 5 + (A 26 ^^^ (A 25).rotateLeft 30 ^^^ (A 24).rotateLeft 30) + (A 23).rotateLeft 30 + 0x6ed9eba1 + W 27 := by
    dsimp [A, W]
    rw [workingAfter_step_a_values M H 23 (by decide +kernel),
      sha1_f_parity_first (by decide +kernel) (by decide +kernel)]
    simp [K, Parity]
  have hW30 : W 30 = (W 27 ^^^ W 22 ^^^ W 16 ^^^ W 14).rotateLeft 1 := by
    dsimp [W]
    change scheduleWord M (⟨30, by decide⟩ : Fin 80) = _
    rw [scheduleWord_recurrence M ⟨30, by decide⟩ (by decide)]
    simp only [Nat.reduceSub]
    rw [sha1Rotl_eq_rotateLeft 1 _ (by decide)]
    rfl
  have hpre : Write.AllHold s (genericCut029 stack input H A W) := by
    change Write.AllHold s (cut029 stack input H M)
    exact hw
  have hraw := genericWords029 A W hA28 hW30 hf.stackPointer hpre he
  change Write.AllHold t (cut030 stack input H M)
  exact hraw

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
theorem segment029 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x102aeb 0x102b25 cut029 cut030 := by
  have hout : ∀ d : Nat, d ≤ bytes029.length →
      0x102aeb + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    simp only [bytes029, List.length_cons, List.length_nil] at hd
    apply outsideCompression_ne hOutside
    · change 0x1024e0 ≤ (0x102aeb + d % 2^64) % 2^64
      omega
    · change (0x102aeb + d % 2^64) % 2^64 < 0x1036df
      omega
  apply Segment.of_block (fun _ _ _ _ => effect029)
    (fun stack input H M => block029 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64 0x2aeb) bytes029,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact effect029_rip he
  · intro stack input H M s t _ hf _ he
    exact effect029_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect029_words hf hw he

def bytes030 : List UInt8 :=
  [0x44, 0x8b, 0x74, 0x24, 0x8, 0x44, 0x31, 0xf3, 0x33, 0x1c, 0x24, 0xd1, 0xc3, 0x89, 0xc7, 0xc1, 0xc7, 0x5, 0x1, 0xde, 0x48, 0x89, 0x5c, 0x24, 0x60, 0x1, 0xd6, 0x44, 0x8d, 0xc, 0x37, 0x41, 0x81, 0xc1, 0xa1, 0xeb, 0xd9, 0x6e, 0x4c, 0x8b, 0x5c, 0x24, 0x10, 0x48, 0x8b, 0x54, 0x24, 0x30, 0x41, 0x31, 0xd3, 0x44, 0x33, 0x5c, 0x24, 0x4, 0x4c, 0x8b, 0x54, 0x24, 0x18, 0x45, 0x31, 0xd3, 0x41, 0xd1, 0xc3, 0x31, 0xc5, 0x44, 0x1, 0xd9]

set_option maxHeartbeats 800000 in
def effect030 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq ((movR32M32Effect 0x102b25 14 (.sib 4 none 0 (.d8 0x8)))) (xorR32R32Effect 0x102b2a 3 3 14)) (xorR32M32LowEffect 0x102b2d 3 (.sib 4 none 0 .none))) (rolR32Effect 0x102b30 2 3 1)) (movR32R32Effect 0x102b32 2 7 0)) (rolR32Effect 0x102b34 3 7 5)) (addR32R32Effect 0x102b37 2 6 3)) (movM64R64Effect 0x102b39 3 (.sib 4 none 0 (.d8 0x60)))) (addR32R32Effect 0x102b3e 2 6 2)) (leaR32Effect 0x102b40 4 9 (.sib 7 (some 6) 0 .none))) (addR32Imm32Effect 0x102b44 7 9 0x6ed9eba1)) (movR64M64Effect 0x102b4b 11 (.sib 4 none 0 (.d8 0x10)))) (movR64M64Effect 0x102b50 2 (.sib 4 none 0 (.d8 0x30)))) (xorR32R32Effect 0x102b55 3 11 2)) (xorR32M32Effect 0x102b58 11 (.sib 4 none 0 (.d8 0x4)))) (movR64M64Effect 0x102b5d 10 (.sib 4 none 0 (.d8 0x18)))) (xorR32R32Effect 0x102b62 3 11 10)) (rolR32Effect 0x102b65 3 11 1)) (xorR32R32Effect 0x102b68 2 5 0)) (addR32R32Effect 0x102b6a 3 1 11)

set_option maxHeartbeats 1600000 in
theorem block030 [Bindings] (boundary : ReturnBoundary)
    (stack input : BitVec 64) (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes030.length → 0x102b25 + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x102b25 ∧ FrameData stack input M s ∧
        Write.AllHold s (cut030 stack input H M))
      (codeRange 0x102b25 bytes030) effect030 := by
  unfold bytes030 at hout ⊢
  sha1_run_begin (mov_r32_m32_effect_step 0x102b25 0x44 (by unfold RexNoWPrefix; decide +kernel) 6 (.sib 4 none 0 (.d8 0x8)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102b2a 0x44 0xf3 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_m32_low_effect_step 0x102b2d 3 (.sib 4 none 0 .none) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_one_effect_step 0x102b30 0xc3 (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_effect_step 0x102b32 0xc7 (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x102b34 0xc7 0x5 (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_effect_step 0x102b37 0xde (by decide +kernel))
  sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m64_r64_effect_step 0x102b39 0x48 (by unfold RexWPrefix; decide +kernel) 3 (.sib 4 none 0 (.d8 0x60)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_effect_step 0x102b3e 0xd6 (by decide +kernel))
  sha1_run_then (lea_r32_rex_effect_step 0x102b40 0x44 (by unfold RexNoWPrefix; decide +kernel) 1 (.sib 7 (some 6) 0 .none) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_imm32_rex_effect_step 0x102b44 0x41 0xc1 0x6ed9eba1 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r64_m64_effect_step 0x102b4b 0x4c (by unfold RexWPrefix; decide +kernel) 3 (.sib 4 none 0 (.d8 0x10)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r64_m64_effect_step 0x102b50 0x48 (by unfold RexWPrefix; decide +kernel) 2 (.sib 4 none 0 (.d8 0x30)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102b55 0x41 0xd3 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_m32_effect_step 0x102b58 0x44 (by unfold RexNoWPrefix; decide +kernel) 3 (.sib 4 none 0 (.d8 0x4)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r64_m64_effect_step 0x102b5d 0x4c (by unfold RexWPrefix; decide +kernel) 2 (.sib 4 none 0 (.d8 0x18)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102b62 0x45 0xd3 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_one_rex_effect_step 0x102b65 0x41 0xc3 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x102b68 0xc5 (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x102b6a 0x44 0xd9 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_finish [effect030]



set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
theorem effect030_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s) (he : (effect030 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have hfoot : ∀ c ∈ (effect030 s).components, c ∈ [.mem ((Operand.reg 4 : Operand 64).read s + BitVec.ofNat 64 96) 8, .reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] := by
    unfold effect030
    iterate 19 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [movR32M32Effect_components, xorR32R32Effect_components, xorR32M32LowEffect_components, rolR32Effect_components, movR32R32Effect_components, addR32R32Effect_components, movM64R64Effect_components, leaR32Effect_components, addR32Imm32Effect_components, movR64M64Effect_components, xorR32M32Effect_components, List.mem_cons, List.not_mem_nil, or_false,
        or_imp, forall_and, forall_eq, or_true]
    all_goals sha1_norm
  have ha := he.agrees.mono hfoot
  rw [hs] at ha
  apply ha.widen
  · intro c hc hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all (config := {decide := true, implicitDefEqProofs := false}) only
      [Component.isMem, scratchComponents, x86_compose]
  · intro address c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hCov.elim
      | exact scratchComponents_stack (Or.inl (by decide +kernel)) hCov

theorem effect030_rip {s t : RamState} (he : (effect030 s).Holds s t) :
    t.RIP = 0x102b6d := by
  exact he.rip.trans (by rfl)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem genericWords030 {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) {s t : RamState}
    (hA29 : A 29 = (A 28).rotateLeft 5 + (A 27 ^^^ (A 26).rotateLeft 30 ^^^ (A 25).rotateLeft 30) + (A 24).rotateLeft 30 + 0x6ed9eba1 + W 28)
    (hW28 : W 28 = (W 25 ^^^ W 20 ^^^ W 14 ^^^ W 12).rotateLeft 1)
    (hW29 : W 29 = (W 26 ^^^ W 21 ^^^ W 15 ^^^ W 13).rotateLeft 1)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (hw : Write.AllHold s (genericCut030 stack input H A W))
    (he : (effect030 s).Holds s t) :
    Write.AllHold t (genericCut031 stack input H A W) := by
  have hfull : ∀ w ∈ (effect030 s).writes, w.Full := by
    apply Effect.Local.full
    unfold effect030
    repeat' first | (solve | x86_local) | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  sha1_norm at hs
  simp only [genericCut030, Write.AllHold] at hw
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28⟩ := hw
  have h10low := (read32_of_read64_low (s := s) (a := (stack + 0))
    (v := (Operand.mem ((stack + 0)) : Operand 64).read s) rfl).symm.trans h10
  have h11low := (read32_of_read64_low (s := s) (a := (stack + 4))
    (v := (Operand.mem ((stack + 4)) : Operand 64).read s) rfl).symm.trans h11
  have h12low := (read32_of_read64_low (s := s) (a := (stack + 8))
    (v := (Operand.mem ((stack + 8)) : Operand 64).read s) rfl).symm.trans h12
  have h13low := (read32_of_read64_low (s := s) (a := (stack + 16))
    (v := (Operand.mem ((stack + 16)) : Operand 64).read s) rfl).symm.trans h13
  have h14low := (read32_of_read64_low (s := s) (a := (stack + 24))
    (v := (Operand.mem ((stack + 24)) : Operand 64).read s) rfl).symm.trans h14
  have h15low := (read32_of_read64_low (s := s) (a := (stack + 32))
    (v := (Operand.mem ((stack + 32)) : Operand 64).read s) rfl).symm.trans h15
  have h16low := (read32_of_read64_low (s := s) (a := (stack + 40))
    (v := (Operand.mem ((stack + 40)) : Operand 64).read s) rfl).symm.trans h16
  have h17low := (read32_of_read64_low (s := s) (a := (stack + 48))
    (v := (Operand.mem ((stack + 48)) : Operand 64).read s) rfl).symm.trans h17
  have h18low := (read32_of_read64_low (s := s) (a := (stack + 56))
    (v := (Operand.mem ((stack + 56)) : Operand 64).read s) rfl).symm.trans h18
  have h20low := (read32_of_read64_low (s := s) (a := (stack + 72))
    (v := (Operand.mem ((stack + 72)) : Operand 64).read s) rfl).symm.trans h20
  have h21low := (read32_of_read64_low (s := s) (a := (stack + 80))
    (v := (Operand.mem ((stack + 80)) : Operand 64).read s) rfl).symm.trans h21
  have h22low := (read32_of_read64_low (s := s) (a := (stack + 88))
    (v := (Operand.mem ((stack + 88)) : Operand 64).read s) rfl).symm.trans h22
  have h23low := (read32_of_read64_low (s := s) (a := (stack + 104))
    (v := (Operand.mem ((stack + 104)) : Operand 64).read s) rfl).symm.trans h23
  have h24low := (read32_of_read64_low (s := s) (a := (stack + 116))
    (v := (Operand.mem ((stack + 116)) : Operand 64).read s) rfl).symm.trans h24
  have h25low := (read32_of_read64_low (s := s) (a := (stack + 120))
    (v := (Operand.mem ((stack + 120)) : Operand 64).read s) rfl).symm.trans h25
  have h26low := (read32_of_read64_low (s := s) (a := (stack + 124))
    (v := (Operand.mem ((stack + 124)) : Operand 64).read s) rfl).symm.trans h26
  have h27low := (read32_of_read64_low (s := s) (a := (stack + 144))
    (v := (Operand.mem ((stack + 144)) : Operand 64).read s) rfl).symm.trans h27
  have h28low := (read32_of_read64_low (s := s) (a := (stack + 152))
    (v := (Operand.mem ((stack + 152)) : Operand 64).read s) rfl).symm.trans h28
  sha1_norm at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28
  simp only [genericCut031, Write.AllHold, ← ho.read_reg, ← ho.read_mem]
  sha1_norm [effect030, hs, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h10low, h11low, h12low, h13low, h14low, h15low, h16low, h17low, h18low, h20low, h21low, h22low, h23low, h24low, h25low, h26low, h27low, h28low,
    read32_memStore64_low, BitVec.setWidth_add, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, leaSpec]
  rw [hA29, hW28, hW29]
  all_goals sha1_norm [← BitVec.setWidth_eq_extractLsb' (by decide : 32 ≤ 64),
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
  simp_all (config := {implicitDefEqProofs := false, decide := true})
  all_goals repeat' first | (solve | ac_rfl) | apply And.intro

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
theorem effect030_words {stack input : BitVec 64}
    {H : Vector (BitVec 32) 5} {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s) (hw : Write.AllHold s (cut030 stack input H M))
    (he : (effect030 s).Holds s t) : Write.AllHold t (cut031 stack input H M) := by
  let A : Nat → BitVec 32 := fun n ↦ (workingAfter M H n).a
  let W : Fin 80 → BitVec 32 := scheduleWord M
  have hA29 : A 29 = (A 28).rotateLeft 5 + (A 27 ^^^ (A 26).rotateLeft 30 ^^^ (A 25).rotateLeft 30) + (A 24).rotateLeft 30 + 0x6ed9eba1 + W 28 := by
    dsimp [A, W]
    rw [workingAfter_step_a_values M H 24 (by decide +kernel),
      sha1_f_parity_first (by decide +kernel) (by decide +kernel)]
    simp [K, Parity]
  have hW28 : W 28 = (W 25 ^^^ W 20 ^^^ W 14 ^^^ W 12).rotateLeft 1 := by
    dsimp [W]
    change scheduleWord M (⟨28, by decide⟩ : Fin 80) = _
    rw [scheduleWord_recurrence M ⟨28, by decide⟩ (by decide)]
    simp only [Nat.reduceSub]
    rw [sha1Rotl_eq_rotateLeft 1 _ (by decide)]
    rfl
  have hW29 : W 29 = (W 26 ^^^ W 21 ^^^ W 15 ^^^ W 13).rotateLeft 1 := by
    dsimp [W]
    change scheduleWord M (⟨29, by decide⟩ : Fin 80) = _
    rw [scheduleWord_recurrence M ⟨29, by decide⟩ (by decide)]
    simp only [Nat.reduceSub]
    rw [sha1Rotl_eq_rotateLeft 1 _ (by decide)]
    rfl
  have hpre : Write.AllHold s (genericCut030 stack input H A W) := by
    change Write.AllHold s (cut030 stack input H M)
    exact hw
  have hraw := genericWords030 A W hA29 hW28 hW29 hf.stackPointer hpre he
  change Write.AllHold t (cut031 stack input H M)
  exact hraw

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
theorem segment030 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x102b25 0x102b6d cut030 cut031 := by
  have hout : ∀ d : Nat, d ≤ bytes030.length →
      0x102b25 + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    simp only [bytes030, List.length_cons, List.length_nil] at hd
    apply outsideCompression_ne hOutside
    · change 0x1024e0 ≤ (0x102b25 + d % 2^64) % 2^64
      omega
    · change (0x102b25 + d % 2^64) % 2^64 < 0x1036df
      omega
  apply Segment.of_block (fun _ _ _ _ => effect030)
    (fun stack input H M => block030 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64 0x2b25) bytes030,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact effect030_rip he
  · intro stack input H M s t _ hf _ he
    exact effect030_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect030_words hf hw he

def bytes031 : List UInt8 :=
  [0x4c, 0x89, 0x5c, 0x24, 0x10, 0x1, 0xe9, 0x44, 0x31, 0xfa, 0x33, 0x54, 0x24, 0x28, 0x31, 0xda, 0xd1, 0xc2, 0x44, 0x89, 0xce, 0xc1, 0xc6, 0x5, 0xc1, 0xc0, 0x1e, 0x8d, 0x3c, 0xe, 0x81, 0xc7, 0xa1, 0xeb, 0xd9, 0x6e, 0x42, 0x8d, 0x34, 0x2, 0x48, 0x89, 0x54, 0x24, 0x30, 0x41, 0x31, 0xc0, 0x45, 0x31, 0xc8, 0x45, 0x1, 0xe8, 0x89, 0xf9, 0xc1, 0xc1, 0x5, 0x44, 0x1, 0xc1, 0x81, 0xc1, 0xa1, 0xeb, 0xd9, 0x6e]

set_option maxHeartbeats 800000 in
def effect031 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq ((movM64R64Effect 0x102b6d 11 (.sib 4 none 0 (.d8 0x10)))) (addR32R32Effect 0x102b72 2 1 5)) (xorR32R32Effect 0x102b74 3 2 15)) (xorR32M32LowEffect 0x102b77 2 (.sib 4 none 0 (.d8 0x28)))) (xorR32R32Effect 0x102b7b 2 2 3)) (rolR32Effect 0x102b7d 2 2 1)) (movR32R32Effect 0x102b7f 3 6 9)) (rolR32Effect 0x102b82 3 6 5)) (rolR32Effect 0x102b85 3 0 30)) (leaR32Effect 0x102b88 3 7 (.sib 6 (some 1) 0 .none))) (addR32Imm32Effect 0x102b8b 6 7 0x6ed9eba1)) (leaR32Effect 0x102b91 4 6 (.sib 2 (some 8) 0 .none))) (movM64R64Effect 0x102b95 2 (.sib 4 none 0 (.d8 0x30)))) (xorR32R32Effect 0x102b9a 3 8 0)) (xorR32R32Effect 0x102b9d 3 8 9)) (addR32R32Effect 0x102ba0 3 8 13)) (movR32R32Effect 0x102ba3 2 1 7)) (rolR32Effect 0x102ba5 3 1 5)) (addR32R32Effect 0x102ba8 3 1 8)) (addR32Imm32Effect 0x102bab 6 1 0x6ed9eba1)

set_option maxHeartbeats 1600000 in
theorem block031 [Bindings] (boundary : ReturnBoundary)
    (stack input : BitVec 64) (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes031.length → 0x102b6d + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x102b6d ∧ FrameData stack input M s ∧
        Write.AllHold s (cut031 stack input H M))
      (codeRange 0x102b6d bytes031) effect031 := by
  unfold bytes031 at hout ⊢
  sha1_run_begin (Sha1.Proofs.Common.Instructions.MovStore.mov_m64_r64_effect_step 0x102b6d 0x4c (by unfold RexWPrefix; decide +kernel) 3 (.sib 4 none 0 (.d8 0x10)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_effect_step 0x102b72 0xe9 (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102b74 0x44 0xfa (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_m32_low_effect_step 0x102b77 2 (.sib 4 none 0 (.d8 0x28)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x102b7b 0xda (by decide +kernel))
  sha1_run_then (rol_r32_one_effect_step 0x102b7d 0xc2 (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x102b7f 0x44 0xce (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x102b82 0xc6 0x5 (by decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x102b85 0xc0 0x1e (by decide +kernel) (by decide +kernel))
  sha1_run_then (lea_r32_effect_step 0x102b88 7 (.sib 6 (some 1) 0 .none) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_imm32_effect_step 0x102b8b 0xc7 0x6ed9eba1 (by decide +kernel) (by decide +kernel))
  sha1_run_then (lea_r32_rex_effect_step 0x102b91 0x42 (by unfold RexNoWPrefix; decide +kernel) 6 (.sib 2 (some 8) 0 .none) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m64_r64_effect_step 0x102b95 0x48 (by unfold RexWPrefix; decide +kernel) 2 (.sib 4 none 0 (.d8 0x30)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102b9a 0x41 0xc0 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102b9d 0x45 0xc8 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x102ba0 0x45 0xe8 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_effect_step 0x102ba3 0xf9 (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x102ba5 0xc1 0x5 (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x102ba8 0x44 0xc1 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_imm32_effect_step 0x102bab 0xc1 0x6ed9eba1 (by decide +kernel) (by decide +kernel))
  sha1_run_finish [effect031]



set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
theorem effect031_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s) (he : (effect031 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have hfoot : ∀ c ∈ (effect031 s).components, c ∈ [.mem ((Operand.reg 4 : Operand 64).read s + BitVec.ofNat 64 16) 8, .mem ((Operand.reg 4 : Operand 64).read s + BitVec.ofNat 64 48) 8, .reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] := by
    unfold effect031
    iterate 19 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [movM64R64Effect_components, addR32R32Effect_components, xorR32R32Effect_components, xorR32M32LowEffect_components, rolR32Effect_components, movR32R32Effect_components, leaR32Effect_components, addR32Imm32Effect_components, List.mem_cons, List.not_mem_nil, or_false,
        or_imp, forall_and, forall_eq, or_true]
    all_goals sha1_norm
  have ha := he.agrees.mono hfoot
  rw [hs] at ha
  apply ha.widen
  · intro c hc hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all (config := {decide := true, implicitDefEqProofs := false}) only
      [Component.isMem, scratchComponents, x86_compose]
  · intro address c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hCov.elim
      | exact scratchComponents_stack (Or.inl (by decide +kernel)) hCov

theorem effect031_rip {s t : RamState} (he : (effect031 s).Holds s t) :
    t.RIP = 0x102bb1 := by
  exact he.rip.trans (by rfl)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem genericWords031 {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) {s t : RamState}
    (hA30 : A 30 = (A 29).rotateLeft 5 + (A 28 ^^^ (A 27).rotateLeft 30 ^^^ (A 26).rotateLeft 30) + (A 25).rotateLeft 30 + 0x6ed9eba1 + W 29)
    (hA31 : A 31 = (A 30).rotateLeft 5 + (A 29 ^^^ (A 28).rotateLeft 30 ^^^ (A 27).rotateLeft 30) + (A 26).rotateLeft 30 + 0x6ed9eba1 + W 30)
    (hW31 : W 31 = (W 28 ^^^ W 23 ^^^ W 17 ^^^ W 15).rotateLeft 1)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (hw : Write.AllHold s (genericCut031 stack input H A W))
    (he : (effect031 s).Holds s t) :
    Write.AllHold t (genericCut032 stack input H A W) := by
  have hfull : ∀ w ∈ (effect031 s).writes, w.Full := by
    apply Effect.Local.full
    unfold effect031
    repeat' first | (solve | x86_local) | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  sha1_norm at hs
  simp only [genericCut031, Write.AllHold] at hw
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30⟩ := hw
  have h13low := (read32_of_read64_low (s := s) (a := (stack + 0))
    (v := (Operand.mem ((stack + 0)) : Operand 64).read s) rfl).symm.trans h13
  have h14low := (read32_of_read64_low (s := s) (a := (stack + 4))
    (v := (Operand.mem ((stack + 4)) : Operand 64).read s) rfl).symm.trans h14
  have h15low := (read32_of_read64_low (s := s) (a := (stack + 8))
    (v := (Operand.mem ((stack + 8)) : Operand 64).read s) rfl).symm.trans h15
  have h16low := (read32_of_read64_low (s := s) (a := (stack + 24))
    (v := (Operand.mem ((stack + 24)) : Operand 64).read s) rfl).symm.trans h16
  have h17low := (read32_of_read64_low (s := s) (a := (stack + 32))
    (v := (Operand.mem ((stack + 32)) : Operand 64).read s) rfl).symm.trans h17
  have h18low := (read32_of_read64_low (s := s) (a := (stack + 40))
    (v := (Operand.mem ((stack + 40)) : Operand 64).read s) rfl).symm.trans h18
  have h19low := (read32_of_read64_low (s := s) (a := (stack + 56))
    (v := (Operand.mem ((stack + 56)) : Operand 64).read s) rfl).symm.trans h19
  have h21low := (read32_of_read64_low (s := s) (a := (stack + 72))
    (v := (Operand.mem ((stack + 72)) : Operand 64).read s) rfl).symm.trans h21
  have h22low := (read32_of_read64_low (s := s) (a := (stack + 80))
    (v := (Operand.mem ((stack + 80)) : Operand 64).read s) rfl).symm.trans h22
  have h23low := (read32_of_read64_low (s := s) (a := (stack + 88))
    (v := (Operand.mem ((stack + 88)) : Operand 64).read s) rfl).symm.trans h23
  have h24low := (read32_of_read64_low (s := s) (a := (stack + 96))
    (v := (Operand.mem ((stack + 96)) : Operand 64).read s) rfl).symm.trans h24
  have h25low := (read32_of_read64_low (s := s) (a := (stack + 104))
    (v := (Operand.mem ((stack + 104)) : Operand 64).read s) rfl).symm.trans h25
  have h26low := (read32_of_read64_low (s := s) (a := (stack + 116))
    (v := (Operand.mem ((stack + 116)) : Operand 64).read s) rfl).symm.trans h26
  have h27low := (read32_of_read64_low (s := s) (a := (stack + 120))
    (v := (Operand.mem ((stack + 120)) : Operand 64).read s) rfl).symm.trans h27
  have h28low := (read32_of_read64_low (s := s) (a := (stack + 124))
    (v := (Operand.mem ((stack + 124)) : Operand 64).read s) rfl).symm.trans h28
  have h29low := (read32_of_read64_low (s := s) (a := (stack + 144))
    (v := (Operand.mem ((stack + 144)) : Operand 64).read s) rfl).symm.trans h29
  have h30low := (read32_of_read64_low (s := s) (a := (stack + 152))
    (v := (Operand.mem ((stack + 152)) : Operand 64).read s) rfl).symm.trans h30
  sha1_norm at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30
  simp only [genericCut032, Write.AllHold, ← ho.read_reg, ← ho.read_mem]
  sha1_norm [effect031, hs, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h13low, h14low, h15low, h16low, h17low, h18low, h19low, h21low, h22low, h23low, h24low, h25low, h26low, h27low, h28low, h29low, h30low,
    read32_memStore64_low, BitVec.setWidth_add, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, leaSpec]
  rw [hA30, hA31, hW31]
  all_goals sha1_norm [← BitVec.setWidth_eq_extractLsb' (by decide : 32 ≤ 64),
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
  simp_all (config := {implicitDefEqProofs := false, decide := true})
  all_goals repeat' first | (solve | ac_rfl) | apply And.intro

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
theorem effect031_words {stack input : BitVec 64}
    {H : Vector (BitVec 32) 5} {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s) (hw : Write.AllHold s (cut031 stack input H M))
    (he : (effect031 s).Holds s t) : Write.AllHold t (cut032 stack input H M) := by
  let A : Nat → BitVec 32 := fun n ↦ (workingAfter M H n).a
  let W : Fin 80 → BitVec 32 := scheduleWord M
  have hA30 : A 30 = (A 29).rotateLeft 5 + (A 28 ^^^ (A 27).rotateLeft 30 ^^^ (A 26).rotateLeft 30) + (A 25).rotateLeft 30 + 0x6ed9eba1 + W 29 := by
    dsimp [A, W]
    rw [workingAfter_step_a_values M H 25 (by decide +kernel),
      sha1_f_parity_first (by decide +kernel) (by decide +kernel)]
    simp [K, Parity]
  have hA31 : A 31 = (A 30).rotateLeft 5 + (A 29 ^^^ (A 28).rotateLeft 30 ^^^ (A 27).rotateLeft 30) + (A 26).rotateLeft 30 + 0x6ed9eba1 + W 30 := by
    dsimp [A, W]
    rw [workingAfter_step_a_values M H 26 (by decide +kernel),
      sha1_f_parity_first (by decide +kernel) (by decide +kernel)]
    simp [K, Parity]
  have hW31 : W 31 = (W 28 ^^^ W 23 ^^^ W 17 ^^^ W 15).rotateLeft 1 := by
    dsimp [W]
    change scheduleWord M (⟨31, by decide⟩ : Fin 80) = _
    rw [scheduleWord_recurrence M ⟨31, by decide⟩ (by decide)]
    simp only [Nat.reduceSub]
    rw [sha1Rotl_eq_rotateLeft 1 _ (by decide)]
    rfl
  have hpre : Write.AllHold s (genericCut031 stack input H A W) := by
    change Write.AllHold s (cut031 stack input H M)
    exact hw
  have hraw := genericWords031 A W hA30 hA31 hW31 hf.stackPointer hpre he
  change Write.AllHold t (cut032 stack input H M)
  exact hraw

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
theorem segment031 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x102b6d 0x102bb1 cut031 cut032 := by
  have hout : ∀ d : Nat, d ≤ bytes031.length →
      0x102b6d + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    simp only [bytes031, List.length_cons, List.length_nil] at hd
    apply outsideCompression_ne hOutside
    · change 0x1024e0 ≤ (0x102b6d + d % 2^64) % 2^64
      omega
    · change (0x102b6d + d % 2^64) % 2^64 < 0x1036df
      omega
  apply Segment.of_block (fun _ _ _ _ => effect031)
    (fun stack input H M => block031 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64 0x2b6d) bytes031,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact effect031_rip he
  · intro stack input H M s t _ hf _ he
    exact effect031_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect031_words hf hw he

def bytes032 : List UInt8 :=
  [0x41, 0xc1, 0xc1, 0x1e, 0x45, 0x89, 0xc8, 0x41, 0x31, 0xc0, 0x41, 0x31, 0xf8, 0xc1, 0xc7, 0x1e, 0x41, 0x1, 0xf0, 0x4c, 0x8b, 0x6c, 0x24, 0x58, 0x45, 0x31, 0xec, 0x45, 0x31, 0xf5, 0x45, 0x31, 0xd5, 0x41, 0x31, 0xd5, 0x41, 0xd1, 0xc5, 0x4c, 0x89, 0x6c, 0x24, 0x58, 0x89, 0xce, 0xc1, 0xc6, 0x1e, 0x89, 0xf5]

set_option maxHeartbeats 800000 in
def effect032 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq ((rolR32Effect 0x102bb1 4 9 30)) (movR32R32Effect 0x102bb5 3 8 9)) (xorR32R32Effect 0x102bb8 3 8 0)) (xorR32R32Effect 0x102bbb 3 8 7)) (rolR32Effect 0x102bbe 3 7 30)) (addR32R32Effect 0x102bc1 3 8 6)) (movR64M64Effect 0x102bc4 13 (.sib 4 none 0 (.d8 0x58)))) (xorR32R32Effect 0x102bc9 3 12 13)) (xorR32R32Effect 0x102bcc 3 13 14)) (xorR32R32Effect 0x102bcf 3 13 10)) (xorR32R32Effect 0x102bd2 3 13 2)) (rolR32Effect 0x102bd5 3 13 1)) (movM64R64Effect 0x102bd8 13 (.sib 4 none 0 (.d8 0x58)))) (movR32R32Effect 0x102bdd 2 6 1)) (rolR32Effect 0x102bdf 3 6 30)) (movR32R32Effect 0x102be2 2 5 6)

set_option maxHeartbeats 1600000 in
theorem block032 [Bindings] (boundary : ReturnBoundary)
    (stack input : BitVec 64) (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes032.length → 0x102bb1 + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x102bb1 ∧ FrameData stack input M s ∧
        Write.AllHold s (cut032 stack input H M))
      (codeRange 0x102bb1 bytes032) effect032 := by
  unfold bytes032 at hout ⊢
  sha1_run_begin (rol_r32_imm8_rex_effect_step 0x102bb1 0x41 0xc1 0x1e (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x102bb5 0x45 0xc8 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102bb8 0x41 0xc0 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102bbb 0x41 0xf8 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x102bbe 0xc7 0x1e (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x102bc1 0x41 0xf0 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r64_m64_effect_step 0x102bc4 0x4c (by unfold RexWPrefix; decide +kernel) 5 (.sib 4 none 0 (.d8 0x58)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102bc9 0x45 0xec (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102bcc 0x45 0xf5 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102bcf 0x45 0xd5 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102bd2 0x41 0xd5 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_one_rex_effect_step 0x102bd5 0x41 0xc5 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m64_r64_effect_step 0x102bd8 0x4c (by unfold RexWPrefix; decide +kernel) 5 (.sib 4 none 0 (.d8 0x58)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_effect_step 0x102bdd 0xce (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x102bdf 0xc6 0x1e (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_effect_step 0x102be2 0xf5 (by decide +kernel))
  sha1_run_finish [effect032]



set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
theorem effect032_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s) (he : (effect032 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have hfoot : ∀ c ∈ (effect032 s).components, c ∈ [.mem ((Operand.reg 4 : Operand 64).read s + BitVec.ofNat 64 88) 8, .reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] := by
    unfold effect032
    iterate 15 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [rolR32Effect_components, movR32R32Effect_components, xorR32R32Effect_components, addR32R32Effect_components, movR64M64Effect_components, movM64R64Effect_components, List.mem_cons, List.not_mem_nil, or_false,
        or_imp, forall_and, forall_eq, or_true]
    all_goals sha1_norm
  have ha := he.agrees.mono hfoot
  rw [hs] at ha
  apply ha.widen
  · intro c hc hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all (config := {decide := true, implicitDefEqProofs := false}) only
      [Component.isMem, scratchComponents, x86_compose]
  · intro address c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hCov.elim
      | exact scratchComponents_stack (Or.inl (by decide +kernel)) hCov

theorem effect032_rip {s t : RamState} (he : (effect032 s).Holds s t) :
    t.RIP = 0x102be4 := by
  exact he.rip.trans (by rfl)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem genericWords032 {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) {s t : RamState}
    (hW34 : W 34 = (W 31 ^^^ W 26 ^^^ W 20 ^^^ W 18).rotateLeft 1)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (hw : Write.AllHold s (genericCut032 stack input H A W))
    (he : (effect032 s).Holds s t) :
    Write.AllHold t (genericCut033 stack input H A W) := by
  have hfull : ∀ w ∈ (effect032 s).writes, w.Full := by
    apply Effect.Local.full
    unfold effect032
    repeat' first | (solve | x86_local) | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  sha1_norm at hs
  simp only [genericCut032, Write.AllHold] at hw
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30⟩ := hw
  have h11low := (read32_of_read64_low (s := s) (a := (stack + 0))
    (v := (Operand.mem ((stack + 0)) : Operand 64).read s) rfl).symm.trans h11
  have h12low := (read32_of_read64_low (s := s) (a := (stack + 4))
    (v := (Operand.mem ((stack + 4)) : Operand 64).read s) rfl).symm.trans h12
  have h13low := (read32_of_read64_low (s := s) (a := (stack + 8))
    (v := (Operand.mem ((stack + 8)) : Operand 64).read s) rfl).symm.trans h13
  have h14low := (read32_of_read64_low (s := s) (a := (stack + 16))
    (v := (Operand.mem ((stack + 16)) : Operand 64).read s) rfl).symm.trans h14
  have h15low := (read32_of_read64_low (s := s) (a := (stack + 24))
    (v := (Operand.mem ((stack + 24)) : Operand 64).read s) rfl).symm.trans h15
  have h16low := (read32_of_read64_low (s := s) (a := (stack + 32))
    (v := (Operand.mem ((stack + 32)) : Operand 64).read s) rfl).symm.trans h16
  have h17low := (read32_of_read64_low (s := s) (a := (stack + 40))
    (v := (Operand.mem ((stack + 40)) : Operand 64).read s) rfl).symm.trans h17
  have h18low := (read32_of_read64_low (s := s) (a := (stack + 48))
    (v := (Operand.mem ((stack + 48)) : Operand 64).read s) rfl).symm.trans h18
  have h19low := (read32_of_read64_low (s := s) (a := (stack + 56))
    (v := (Operand.mem ((stack + 56)) : Operand 64).read s) rfl).symm.trans h19
  have h21low := (read32_of_read64_low (s := s) (a := (stack + 72))
    (v := (Operand.mem ((stack + 72)) : Operand 64).read s) rfl).symm.trans h21
  have h22low := (read32_of_read64_low (s := s) (a := (stack + 80))
    (v := (Operand.mem ((stack + 80)) : Operand 64).read s) rfl).symm.trans h22
  have h23low := (read32_of_read64_low (s := s) (a := (stack + 88))
    (v := (Operand.mem ((stack + 88)) : Operand 64).read s) rfl).symm.trans h23
  have h24low := (read32_of_read64_low (s := s) (a := (stack + 96))
    (v := (Operand.mem ((stack + 96)) : Operand 64).read s) rfl).symm.trans h24
  have h25low := (read32_of_read64_low (s := s) (a := (stack + 104))
    (v := (Operand.mem ((stack + 104)) : Operand 64).read s) rfl).symm.trans h25
  have h26low := (read32_of_read64_low (s := s) (a := (stack + 116))
    (v := (Operand.mem ((stack + 116)) : Operand 64).read s) rfl).symm.trans h26
  have h27low := (read32_of_read64_low (s := s) (a := (stack + 120))
    (v := (Operand.mem ((stack + 120)) : Operand 64).read s) rfl).symm.trans h27
  have h28low := (read32_of_read64_low (s := s) (a := (stack + 124))
    (v := (Operand.mem ((stack + 124)) : Operand 64).read s) rfl).symm.trans h28
  have h29low := (read32_of_read64_low (s := s) (a := (stack + 144))
    (v := (Operand.mem ((stack + 144)) : Operand 64).read s) rfl).symm.trans h29
  have h30low := (read32_of_read64_low (s := s) (a := (stack + 152))
    (v := (Operand.mem ((stack + 152)) : Operand 64).read s) rfl).symm.trans h30
  sha1_norm at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30
  simp only [genericCut033, Write.AllHold, ← ho.read_reg, ← ho.read_mem]
  sha1_norm [effect032, hs, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h11low, h12low, h13low, h14low, h15low, h16low, h17low, h18low, h19low, h21low, h22low, h23low, h24low, h25low, h26low, h27low, h28low, h29low, h30low,
    read32_memStore64_low, BitVec.setWidth_add, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, leaSpec]
  rw [hW34]
  all_goals sha1_norm [← BitVec.setWidth_eq_extractLsb' (by decide : 32 ≤ 64),
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
  simp_all (config := {implicitDefEqProofs := false, decide := true})
  all_goals repeat' first | (solve | ac_rfl) | apply And.intro

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
theorem effect032_words {stack input : BitVec 64}
    {H : Vector (BitVec 32) 5} {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s) (hw : Write.AllHold s (cut032 stack input H M))
    (he : (effect032 s).Holds s t) : Write.AllHold t (cut033 stack input H M) := by
  let A : Nat → BitVec 32 := fun n ↦ (workingAfter M H n).a
  let W : Fin 80 → BitVec 32 := scheduleWord M
  have hW34 : W 34 = (W 31 ^^^ W 26 ^^^ W 20 ^^^ W 18).rotateLeft 1 := by
    dsimp [W]
    change scheduleWord M (⟨34, by decide⟩ : Fin 80) = _
    rw [scheduleWord_recurrence M ⟨34, by decide⟩ (by decide)]
    simp only [Nat.reduceSub]
    rw [sha1Rotl_eq_rotateLeft 1 _ (by decide)]
    rfl
  have hpre : Write.AllHold s (genericCut032 stack input H A W) := by
    change Write.AllHold s (cut032 stack input H M)
    exact hw
  have hraw := genericWords032 A W hW34 hf.stackPointer hpre he
  change Write.AllHold t (cut033 stack input H M)
  exact hraw

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
theorem segment032 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x102bb1 0x102be4 cut032 cut033 := by
  have hout : ∀ d : Nat, d ≤ bytes032.length →
      0x102bb1 + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    simp only [bytes032, List.length_cons, List.length_nil] at hd
    apply outsideCompression_ne hOutside
    · change 0x1024e0 ≤ (0x102bb1 + d % 2^64) % 2^64
      omega
    · change (0x102bb1 + d % 2^64) % 2^64 < 0x1036df
      omega
  apply Segment.of_block (fun _ _ _ _ => effect032)
    (fun stack input H M => block032 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64 0x2bb1) bytes032,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact effect032_rip he
  · intro stack input H M s t _ hf _ he
    exact effect032_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect032_words hf hw he

def bytes033 : List UInt8 :=
  [0x31, 0xfd, 0x46, 0x8d, 0x14, 0x2f, 0x44, 0x31, 0xcf, 0x31, 0xcf, 0xc1, 0xc1, 0x5, 0x42, 0x8d, 0x14, 0x1, 0x81, 0xc2, 0xa1, 0xeb, 0xd9, 0x6e, 0x4c, 0x8b, 0x74, 0x24, 0x68, 0x45, 0x31, 0xf4, 0x45, 0x31, 0xdc, 0x41, 0xd1, 0xc4, 0x44, 0x1, 0xe0, 0x44, 0x89, 0x64, 0x24, 0xc, 0x1, 0xf8, 0x89, 0xd7, 0xc1, 0xc7, 0x5, 0x44, 0x8d, 0x1c, 0x7, 0x41, 0x81, 0xc3, 0xa1, 0xeb, 0xd9, 0x6e]

set_option maxHeartbeats 800000 in
def effect033 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq ((xorR32R32Effect 0x102be4 2 5 7)) (leaR32Effect 0x102be6 4 10 (.sib 7 (some 13) 0 .none))) (xorR32R32Effect 0x102bea 3 7 9)) (xorR32R32Effect 0x102bed 2 7 1)) (rolR32Effect 0x102bef 3 1 5)) (leaR32Effect 0x102bf2 4 2 (.sib 1 (some 8) 0 .none))) (addR32Imm32Effect 0x102bf6 6 2 0x6ed9eba1)) (movR64M64Effect 0x102bfc 14 (.sib 4 none 0 (.d8 0x68)))) (xorR32R32Effect 0x102c01 3 12 14)) (xorR32R32Effect 0x102c04 3 12 11)) (rolR32Effect 0x102c07 3 12 1)) (addR32R32Effect 0x102c0a 3 0 12)) (movM32R32Effect 0x102c0d 12 (.sib 4 none 0 (.d8 0xc)))) (addR32R32Effect 0x102c12 2 0 7)) (movR32R32Effect 0x102c14 2 7 2)) (rolR32Effect 0x102c16 3 7 5)) (leaR32Effect 0x102c19 4 11 (.sib 7 (some 0) 0 .none))) (addR32Imm32Effect 0x102c1d 7 11 0x6ed9eba1)

set_option maxHeartbeats 1600000 in
theorem block033 [Bindings] (boundary : ReturnBoundary)
    (stack input : BitVec 64) (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes033.length → 0x102be4 + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x102be4 ∧ FrameData stack input M s ∧
        Write.AllHold s (cut033 stack input H M))
      (codeRange 0x102be4 bytes033) effect033 := by
  unfold bytes033 at hout ⊢
  sha1_run_begin (xor_r32_r32_effect_step 0x102be4 0xfd (by decide +kernel))
  sha1_run_then (lea_r32_rex_effect_step 0x102be6 0x46 (by unfold RexNoWPrefix; decide +kernel) 2 (.sib 7 (some 13) 0 .none) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102bea 0x44 0xcf (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x102bed 0xcf (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x102bef 0xc1 0x5 (by decide +kernel) (by decide +kernel))
  sha1_run_then (lea_r32_rex_effect_step 0x102bf2 0x42 (by unfold RexNoWPrefix; decide +kernel) 2 (.sib 1 (some 8) 0 .none) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_imm32_effect_step 0x102bf6 0xc2 0x6ed9eba1 (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r64_m64_effect_step 0x102bfc 0x4c (by unfold RexWPrefix; decide +kernel) 6 (.sib 4 none 0 (.d8 0x68)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102c01 0x45 0xf4 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102c04 0x45 0xdc (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_one_rex_effect_step 0x102c07 0x41 0xc4 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x102c0a 0x44 0xe0 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m32_r32_effect_step 0x102c0d 0x44 (by unfold RexNoWPrefix; decide +kernel) 4 (.sib 4 none 0 (.d8 0xc)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_effect_step 0x102c12 0xf8 (by decide +kernel))
  sha1_run_then (mov_r32_r32_effect_step 0x102c14 0xd7 (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x102c16 0xc7 0x5 (by decide +kernel) (by decide +kernel))
  sha1_run_then (lea_r32_rex_effect_step 0x102c19 0x44 (by unfold RexNoWPrefix; decide +kernel) 3 (.sib 7 (some 0) 0 .none) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_imm32_rex_effect_step 0x102c1d 0x41 0xc3 0x6ed9eba1 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_finish [effect033]



set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
theorem effect033_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s) (he : (effect033 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have hfoot : ∀ c ∈ (effect033 s).components, c ∈ [.mem ((Operand.reg 4 : Operand 64).read s + BitVec.ofNat 64 12) 4, .reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] := by
    unfold effect033
    iterate 17 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [xorR32R32Effect_components, leaR32Effect_components, rolR32Effect_components, addR32Imm32Effect_components, movR64M64Effect_components, addR32R32Effect_components, movM32R32Effect_components, movR32R32Effect_components, List.mem_cons, List.not_mem_nil, or_false,
        or_imp, forall_and, forall_eq, or_true]
    all_goals sha1_norm
  have ha := he.agrees.mono hfoot
  rw [hs] at ha
  apply ha.widen
  · intro c hc hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all (config := {decide := true, implicitDefEqProofs := false}) only
      [Component.isMem, scratchComponents, x86_compose]
  · intro address c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hCov.elim
      | exact scratchComponents_stack (Or.inl (by decide +kernel)) hCov

theorem effect033_rip {s t : RamState} (he : (effect033 s).Holds s t) :
    t.RIP = 0x102c24 := by
  exact he.rip.trans (by rfl)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem genericWords033 {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) {s t : RamState}
    (hA32 : A 32 = (A 31).rotateLeft 5 + (A 30 ^^^ (A 29).rotateLeft 30 ^^^ (A 28).rotateLeft 30) + (A 27).rotateLeft 30 + 0x6ed9eba1 + W 31)
    (hA33 : A 33 = (A 32).rotateLeft 5 + (A 31 ^^^ (A 30).rotateLeft 30 ^^^ (A 29).rotateLeft 30) + (A 28).rotateLeft 30 + 0x6ed9eba1 + W 32)
    (hW32 : W 32 = (W 29 ^^^ W 24 ^^^ W 18 ^^^ W 16).rotateLeft 1)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (hw : Write.AllHold s (genericCut033 stack input H A W))
    (he : (effect033 s).Holds s t) :
    Write.AllHold t (genericCut034 stack input H A W) := by
  have hfull : ∀ w ∈ (effect033 s).writes, w.Full := by
    apply Effect.Local.full
    unfold effect033
    repeat' first | (solve | x86_local) | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  sha1_norm at hs
  simp only [genericCut033, Write.AllHold] at hw
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30⟩ := hw
  have h11low := (read32_of_read64_low (s := s) (a := (stack + 0))
    (v := (Operand.mem ((stack + 0)) : Operand 64).read s) rfl).symm.trans h11
  have h12low := (read32_of_read64_low (s := s) (a := (stack + 4))
    (v := (Operand.mem ((stack + 4)) : Operand 64).read s) rfl).symm.trans h12
  have h13low := (read32_of_read64_low (s := s) (a := (stack + 8))
    (v := (Operand.mem ((stack + 8)) : Operand 64).read s) rfl).symm.trans h13
  have h14low := (read32_of_read64_low (s := s) (a := (stack + 16))
    (v := (Operand.mem ((stack + 16)) : Operand 64).read s) rfl).symm.trans h14
  have h15low := (read32_of_read64_low (s := s) (a := (stack + 24))
    (v := (Operand.mem ((stack + 24)) : Operand 64).read s) rfl).symm.trans h15
  have h16low := (read32_of_read64_low (s := s) (a := (stack + 32))
    (v := (Operand.mem ((stack + 32)) : Operand 64).read s) rfl).symm.trans h16
  have h17low := (read32_of_read64_low (s := s) (a := (stack + 40))
    (v := (Operand.mem ((stack + 40)) : Operand 64).read s) rfl).symm.trans h17
  have h18low := (read32_of_read64_low (s := s) (a := (stack + 48))
    (v := (Operand.mem ((stack + 48)) : Operand 64).read s) rfl).symm.trans h18
  have h19low := (read32_of_read64_low (s := s) (a := (stack + 56))
    (v := (Operand.mem ((stack + 56)) : Operand 64).read s) rfl).symm.trans h19
  have h21low := (read32_of_read64_low (s := s) (a := (stack + 72))
    (v := (Operand.mem ((stack + 72)) : Operand 64).read s) rfl).symm.trans h21
  have h22low := (read32_of_read64_low (s := s) (a := (stack + 80))
    (v := (Operand.mem ((stack + 80)) : Operand 64).read s) rfl).symm.trans h22
  have h23low := (read32_of_read64_low (s := s) (a := (stack + 88))
    (v := (Operand.mem ((stack + 88)) : Operand 64).read s) rfl).symm.trans h23
  have h24low := (read32_of_read64_low (s := s) (a := (stack + 96))
    (v := (Operand.mem ((stack + 96)) : Operand 64).read s) rfl).symm.trans h24
  have h25low := (read32_of_read64_low (s := s) (a := (stack + 104))
    (v := (Operand.mem ((stack + 104)) : Operand 64).read s) rfl).symm.trans h25
  have h26low := (read32_of_read64_low (s := s) (a := (stack + 116))
    (v := (Operand.mem ((stack + 116)) : Operand 64).read s) rfl).symm.trans h26
  have h27low := (read32_of_read64_low (s := s) (a := (stack + 120))
    (v := (Operand.mem ((stack + 120)) : Operand 64).read s) rfl).symm.trans h27
  have h28low := (read32_of_read64_low (s := s) (a := (stack + 124))
    (v := (Operand.mem ((stack + 124)) : Operand 64).read s) rfl).symm.trans h28
  have h29low := (read32_of_read64_low (s := s) (a := (stack + 144))
    (v := (Operand.mem ((stack + 144)) : Operand 64).read s) rfl).symm.trans h29
  have h30low := (read32_of_read64_low (s := s) (a := (stack + 152))
    (v := (Operand.mem ((stack + 152)) : Operand 64).read s) rfl).symm.trans h30
  sha1_norm at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30
  simp only [genericCut034, Write.AllHold, ← ho.read_reg, ← ho.read_mem]
  sha1_norm [effect033, hs, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h11low, h12low, h13low, h14low, h15low, h16low, h17low, h18low, h19low, h21low, h22low, h23low, h24low, h25low, h26low, h27low, h28low, h29low, h30low,
    read32_memStore64_low, BitVec.setWidth_add, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, leaSpec]
  rw [hA32, hA33, hW32]
  all_goals sha1_norm [← BitVec.setWidth_eq_extractLsb' (by decide : 32 ≤ 64),
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
  simp_all (config := {implicitDefEqProofs := false, decide := true})
  all_goals repeat' first | (solve | ac_rfl) | apply And.intro

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
theorem effect033_words {stack input : BitVec 64}
    {H : Vector (BitVec 32) 5} {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s) (hw : Write.AllHold s (cut033 stack input H M))
    (he : (effect033 s).Holds s t) : Write.AllHold t (cut034 stack input H M) := by
  let A : Nat → BitVec 32 := fun n ↦ (workingAfter M H n).a
  let W : Fin 80 → BitVec 32 := scheduleWord M
  have hA32 : A 32 = (A 31).rotateLeft 5 + (A 30 ^^^ (A 29).rotateLeft 30 ^^^ (A 28).rotateLeft 30) + (A 27).rotateLeft 30 + 0x6ed9eba1 + W 31 := by
    dsimp [A, W]
    rw [workingAfter_step_a_values M H 27 (by decide +kernel),
      sha1_f_parity_first (by decide +kernel) (by decide +kernel)]
    simp [K, Parity]
  have hA33 : A 33 = (A 32).rotateLeft 5 + (A 31 ^^^ (A 30).rotateLeft 30 ^^^ (A 29).rotateLeft 30) + (A 28).rotateLeft 30 + 0x6ed9eba1 + W 32 := by
    dsimp [A, W]
    rw [workingAfter_step_a_values M H 28 (by decide +kernel),
      sha1_f_parity_first (by decide +kernel) (by decide +kernel)]
    simp [K, Parity]
  have hW32 : W 32 = (W 29 ^^^ W 24 ^^^ W 18 ^^^ W 16).rotateLeft 1 := by
    dsimp [W]
    change scheduleWord M (⟨32, by decide⟩ : Fin 80) = _
    rw [scheduleWord_recurrence M ⟨32, by decide⟩ (by decide)]
    simp only [Nat.reduceSub]
    rw [sha1Rotl_eq_rotateLeft 1 _ (by decide)]
    rfl
  have hpre : Write.AllHold s (genericCut033 stack input H A W) := by
    change Write.AllHold s (cut033 stack input H M)
    exact hw
  have hraw := genericWords033 A W hA32 hA33 hW32 hf.stackPointer hpre he
  change Write.AllHold t (cut034 stack input H M)
  exact hraw

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
theorem segment033 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x102be4 0x102c24 cut033 cut034 := by
  have hout : ∀ d : Nat, d ≤ bytes033.length →
      0x102be4 + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    simp only [bytes033, List.length_cons, List.length_nil] at hd
    apply outsideCompression_ne hOutside
    · change 0x1024e0 ≤ (0x102be4 + d % 2^64) % 2^64
      omega
    · change (0x102be4 + d % 2^64) % 2^64 < 0x1036df
      omega
  apply Segment.of_block (fun _ _ _ _ => effect033)
    (fun stack input H M => block033 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64 0x2be4) bytes033,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact effect033_rip he
  · intro stack input H M s t _ hf _ he
    exact effect033_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect033_words hf hw he

def bytes034 : List UInt8 :=
  [0x48, 0x8b, 0x4c, 0x24, 0x38, 0x41, 0x31, 0xcf, 0x44, 0x8b, 0x2c, 0x24, 0x45, 0x31, 0xef, 0x48, 0x8b, 0x5c, 0x24, 0x48, 0x41, 0x31, 0xdf, 0x41, 0xd1, 0xc7, 0x31, 0xd5, 0x45, 0x1, 0xf9, 0x41, 0x1, 0xe9, 0x44, 0x89, 0xd8, 0xc1, 0xc0, 0x5, 0x42, 0x8d, 0x3c, 0x8, 0x81, 0xc7, 0xa1, 0xeb, 0xd9, 0x6e]

set_option maxHeartbeats 800000 in
def effect034 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq ((movR64M64Effect 0x102c24 1 (.sib 4 none 0 (.d8 0x38)))) (xorR32R32Effect 0x102c29 3 15 1)) (movR32M32Effect 0x102c2c 13 (.sib 4 none 0 .none))) (xorR32R32Effect 0x102c30 3 15 13)) (movR64M64Effect 0x102c33 3 (.sib 4 none 0 (.d8 0x48)))) (xorR32R32Effect 0x102c38 3 15 3)) (rolR32Effect 0x102c3b 3 15 1)) (xorR32R32Effect 0x102c3e 2 5 2)) (addR32R32Effect 0x102c40 3 9 15)) (addR32R32Effect 0x102c43 3 9 5)) (movR32R32Effect 0x102c46 3 0 11)) (rolR32Effect 0x102c49 3 0 5)) (leaR32Effect 0x102c4c 4 7 (.sib 0 (some 9) 0 .none))) (addR32Imm32Effect 0x102c50 6 7 0x6ed9eba1)

set_option maxHeartbeats 1600000 in
theorem block034 [Bindings] (boundary : ReturnBoundary)
    (stack input : BitVec 64) (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes034.length → 0x102c24 + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x102c24 ∧ FrameData stack input M s ∧
        Write.AllHold s (cut034 stack input H M))
      (codeRange 0x102c24 bytes034) effect034 := by
  unfold bytes034 at hout ⊢
  sha1_run_begin (mov_r64_m64_effect_step 0x102c24 0x48 (by unfold RexWPrefix; decide +kernel) 1 (.sib 4 none 0 (.d8 0x38)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102c29 0x41 0xcf (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_m32_effect_step 0x102c2c 0x44 (by unfold RexNoWPrefix; decide +kernel) 5 (.sib 4 none 0 .none) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102c30 0x45 0xef (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r64_m64_effect_step 0x102c33 0x48 (by unfold RexWPrefix; decide +kernel) 3 (.sib 4 none 0 (.d8 0x48)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102c38 0x41 0xdf (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_one_rex_effect_step 0x102c3b 0x41 0xc7 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x102c3e 0xd5 (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x102c40 0x45 0xf9 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x102c43 0x41 0xe9 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x102c46 0x44 0xd8 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x102c49 0xc0 0x5 (by decide +kernel) (by decide +kernel))
  sha1_run_then (lea_r32_rex_effect_step 0x102c4c 0x42 (by unfold RexNoWPrefix; decide +kernel) 7 (.sib 0 (some 9) 0 .none) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_imm32_effect_step 0x102c50 0xc7 0x6ed9eba1 (by decide +kernel) (by decide +kernel))
  sha1_run_finish [effect034]



set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
theorem effect034_agrees {stack : BitVec 64} {s t : RamState}
    (he : (effect034 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hfoot : ∀ c ∈ (effect034 s).components, c ∈ [.reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] := by
    unfold effect034
    iterate 13 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [movR64M64Effect_components, xorR32R32Effect_components, movR32M32Effect_components, rolR32Effect_components, addR32R32Effect_components, movR32R32Effect_components, leaR32Effect_components, addR32Imm32Effect_components, List.mem_cons, List.not_mem_nil, or_false,
        or_imp, forall_and, forall_eq]
    all_goals sha1_norm
  have ha := he.agrees.mono hfoot
  apply ha.widen
  · intro c hc hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all (config := {decide := true, implicitDefEqProofs := false}) only
      [scratchComponents, x86_compose]
  · intro address c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hCov.elim
      | exact scratchComponents_stack (Or.inl (by decide +kernel)) hCov

theorem effect034_rip {s t : RamState} (he : (effect034 s).Holds s t) :
    t.RIP = 0x102c56 := by
  exact he.rip.trans (by rfl)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem genericWords034 {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) {s t : RamState}
    (hA34 : A 34 = (A 33).rotateLeft 5 + (A 32 ^^^ (A 31).rotateLeft 30 ^^^ (A 30).rotateLeft 30) + (A 29).rotateLeft 30 + 0x6ed9eba1 + W 33)
    (hW33 : W 33 = (W 30 ^^^ W 25 ^^^ W 19 ^^^ W 17).rotateLeft 1)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (hw : Write.AllHold s (genericCut034 stack input H A W))
    (he : (effect034 s).Holds s t) :
    Write.AllHold t (genericCut035 stack input H A W) := by
  have hfull : ∀ w ∈ (effect034 s).writes, w.Full := by
    apply Effect.Local.full
    unfold effect034
    repeat' first | (solve | x86_local) | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  sha1_norm at hs
  simp only [genericCut034, Write.AllHold] at hw
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28⟩ := hw
  have h9low := (read32_of_read64_low (s := s) (a := (stack + 0))
    (v := (Operand.mem ((stack + 0)) : Operand 64).read s) rfl).symm.trans h9
  have h10low := (read32_of_read64_low (s := s) (a := (stack + 4))
    (v := (Operand.mem ((stack + 4)) : Operand 64).read s) rfl).symm.trans h10
  have h11low := (read32_of_read64_low (s := s) (a := (stack + 8))
    (v := (Operand.mem ((stack + 8)) : Operand 64).read s) rfl).symm.trans h11
  have h12low := (read32_of_read64_low (s := s) (a := (stack + 12))
    (v := (Operand.mem ((stack + 12)) : Operand 64).read s) rfl).symm.trans h12
  have h13low := (read32_of_read64_low (s := s) (a := (stack + 16))
    (v := (Operand.mem ((stack + 16)) : Operand 64).read s) rfl).symm.trans h13
  have h14low := (read32_of_read64_low (s := s) (a := (stack + 24))
    (v := (Operand.mem ((stack + 24)) : Operand 64).read s) rfl).symm.trans h14
  have h15low := (read32_of_read64_low (s := s) (a := (stack + 32))
    (v := (Operand.mem ((stack + 32)) : Operand 64).read s) rfl).symm.trans h15
  have h16low := (read32_of_read64_low (s := s) (a := (stack + 40))
    (v := (Operand.mem ((stack + 40)) : Operand 64).read s) rfl).symm.trans h16
  have h17low := (read32_of_read64_low (s := s) (a := (stack + 48))
    (v := (Operand.mem ((stack + 48)) : Operand 64).read s) rfl).symm.trans h17
  have h18low := (read32_of_read64_low (s := s) (a := (stack + 56))
    (v := (Operand.mem ((stack + 56)) : Operand 64).read s) rfl).symm.trans h18
  have h20low := (read32_of_read64_low (s := s) (a := (stack + 72))
    (v := (Operand.mem ((stack + 72)) : Operand 64).read s) rfl).symm.trans h20
  have h21low := (read32_of_read64_low (s := s) (a := (stack + 80))
    (v := (Operand.mem ((stack + 80)) : Operand 64).read s) rfl).symm.trans h21
  have h22low := (read32_of_read64_low (s := s) (a := (stack + 88))
    (v := (Operand.mem ((stack + 88)) : Operand 64).read s) rfl).symm.trans h22
  have h23low := (read32_of_read64_low (s := s) (a := (stack + 96))
    (v := (Operand.mem ((stack + 96)) : Operand 64).read s) rfl).symm.trans h23
  have h24low := (read32_of_read64_low (s := s) (a := (stack + 116))
    (v := (Operand.mem ((stack + 116)) : Operand 64).read s) rfl).symm.trans h24
  have h25low := (read32_of_read64_low (s := s) (a := (stack + 120))
    (v := (Operand.mem ((stack + 120)) : Operand 64).read s) rfl).symm.trans h25
  have h26low := (read32_of_read64_low (s := s) (a := (stack + 124))
    (v := (Operand.mem ((stack + 124)) : Operand 64).read s) rfl).symm.trans h26
  have h27low := (read32_of_read64_low (s := s) (a := (stack + 144))
    (v := (Operand.mem ((stack + 144)) : Operand 64).read s) rfl).symm.trans h27
  have h28low := (read32_of_read64_low (s := s) (a := (stack + 152))
    (v := (Operand.mem ((stack + 152)) : Operand 64).read s) rfl).symm.trans h28
  sha1_norm at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28
  simp only [genericCut035, Write.AllHold, ← ho.read_reg, ← ho.read_mem]
  sha1_norm [effect034, hs, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h9low, h10low, h11low, h12low, h13low, h14low, h15low, h16low, h17low, h18low, h20low, h21low, h22low, h23low, h24low, h25low, h26low, h27low, h28low,
    read32_memStore64_low, BitVec.setWidth_add, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, leaSpec]
  rw [hA34, hW33]
  all_goals sha1_norm [← BitVec.setWidth_eq_extractLsb' (by decide : 32 ≤ 64),
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
  simp_all (config := {implicitDefEqProofs := false, decide := true})
  all_goals repeat' first | (solve | ac_rfl) | apply And.intro

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
theorem effect034_words {stack input : BitVec 64}
    {H : Vector (BitVec 32) 5} {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s) (hw : Write.AllHold s (cut034 stack input H M))
    (he : (effect034 s).Holds s t) : Write.AllHold t (cut035 stack input H M) := by
  let A : Nat → BitVec 32 := fun n ↦ (workingAfter M H n).a
  let W : Fin 80 → BitVec 32 := scheduleWord M
  have hA34 : A 34 = (A 33).rotateLeft 5 + (A 32 ^^^ (A 31).rotateLeft 30 ^^^ (A 30).rotateLeft 30) + (A 29).rotateLeft 30 + 0x6ed9eba1 + W 33 := by
    dsimp [A, W]
    rw [workingAfter_step_a_values M H 29 (by decide +kernel),
      sha1_f_parity_first (by decide +kernel) (by decide +kernel)]
    simp [K, Parity]
  have hW33 : W 33 = (W 30 ^^^ W 25 ^^^ W 19 ^^^ W 17).rotateLeft 1 := by
    dsimp [W]
    change scheduleWord M (⟨33, by decide⟩ : Fin 80) = _
    rw [scheduleWord_recurrence M ⟨33, by decide⟩ (by decide)]
    simp only [Nat.reduceSub]
    rw [sha1Rotl_eq_rotateLeft 1 _ (by decide)]
    rfl
  have hpre : Write.AllHold s (genericCut034 stack input H A W) := by
    change Write.AllHold s (cut034 stack input H M)
    exact hw
  have hraw := genericWords034 A W hA34 hW33 hf.stackPointer hpre he
  change Write.AllHold t (cut035 stack input H M)
  exact hraw

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
theorem segment034 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x102c24 0x102c56 cut034 cut035 := by
  have hout : ∀ d : Nat, d ≤ bytes034.length →
      0x102c24 + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    simp only [bytes034, List.length_cons, List.length_nil] at hd
    apply outsideCompression_ne hOutside
    · change 0x1024e0 ≤ (0x102c24 + d % 2^64) % 2^64
      omega
    · change (0x102c24 + d % 2^64) % 2^64 < 0x1036df
      omega
  apply Segment.of_block (fun _ _ _ _ => effect034)
    (fun stack input H M => block034 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64 0x2c24) bytes034,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact effect034_rip he
  · intro stack input H M s t _ hf _ he
    exact effect034_agrees he
  · intro stack input H M s t _ hf hw he
    exact effect034_words hf hw he

def bytes035 : List UInt8 :=
  [0x48, 0x89, 0xc8, 0x33, 0x44, 0x24, 0x4, 0x33, 0x44, 0x24, 0x50, 0x44, 0x31, 0xe0, 0xd1, 0xc0, 0xc1, 0xc2, 0x1e, 0x41, 0x89, 0xf8, 0x41, 0xc1, 0xc0, 0x5, 0x44, 0x8d, 0x24, 0x30, 0x49, 0x89, 0xc1, 0x48, 0x89, 0x44, 0x24, 0x38, 0x31, 0xd6, 0x44, 0x31, 0xde, 0x41, 0xc1, 0xc3, 0x1e, 0x44, 0x1, 0xd6, 0x44, 0x89, 0xd8]

set_option maxHeartbeats 800000 in
def effect035 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq ((movR64R64Effect 0x102c56 0 1)) (xorR32M32LowEffect 0x102c59 0 (.sib 4 none 0 (.d8 0x4)))) (xorR32M32LowEffect 0x102c5d 0 (.sib 4 none 0 (.d8 0x50)))) (xorR32R32Effect 0x102c61 3 0 12)) (rolR32Effect 0x102c64 2 0 1)) (rolR32Effect 0x102c66 3 2 30)) (movR32R32Effect 0x102c69 3 8 7)) (rolR32Effect 0x102c6c 4 8 5)) (leaR32Effect 0x102c70 4 12 (.sib 0 (some 6) 0 .none))) (movR64R64Effect 0x102c74 9 0)) (movM64R64Effect 0x102c77 0 (.sib 4 none 0 (.d8 0x38)))) (xorR32R32Effect 0x102c7c 2 6 2)) (xorR32R32Effect 0x102c7e 3 6 11)) (rolR32Effect 0x102c81 4 11 30)) (addR32R32Effect 0x102c85 3 6 10)) (movR32R32Effect 0x102c88 3 0 11)

set_option maxHeartbeats 1600000 in
theorem block035 [Bindings] (boundary : ReturnBoundary)
    (stack input : BitVec 64) (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes035.length → 0x102c56 + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x102c56 ∧ FrameData stack input M s ∧
        Write.AllHold s (cut035 stack input H M))
      (codeRange 0x102c56 bytes035) effect035 := by
  unfold bytes035 at hout ⊢
  sha1_run_begin (mov_r64_r64_effect_step 0x102c56 0x48 0xc8 (by unfold RexWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_m32_low_effect_step 0x102c59 0 (.sib 4 none 0 (.d8 0x4)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_m32_low_effect_step 0x102c5d 0 (.sib 4 none 0 (.d8 0x50)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102c61 0x44 0xe0 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_one_effect_step 0x102c64 0xc0 (by decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x102c66 0xc2 0x1e (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x102c69 0x41 0xf8 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_imm8_rex_effect_step 0x102c6c 0x41 0xc0 0x5 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (lea_r32_rex_effect_step 0x102c70 0x44 (by unfold RexNoWPrefix; decide +kernel) 4 (.sib 0 (some 6) 0 .none) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r64_r64_effect_step 0x102c74 0x49 0xc1 (by unfold RexWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m64_r64_effect_step 0x102c77 0x48 (by unfold RexWPrefix; decide +kernel) 0 (.sib 4 none 0 (.d8 0x38)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x102c7c 0xd6 (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102c7e 0x44 0xde (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_imm8_rex_effect_step 0x102c81 0x41 0xc3 0x1e (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x102c85 0x44 0xd6 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x102c88 0x44 0xd8 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_finish [effect035]



set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
theorem effect035_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s) (he : (effect035 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have hfoot : ∀ c ∈ (effect035 s).components, c ∈ [.mem ((Operand.reg 4 : Operand 64).read s + BitVec.ofNat 64 56) 8, .reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] := by
    unfold effect035
    iterate 15 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [movR64R64Effect_components, xorR32M32LowEffect_components, xorR32R32Effect_components, rolR32Effect_components, movR32R32Effect_components, leaR32Effect_components, movM64R64Effect_components, addR32R32Effect_components, List.mem_cons, List.not_mem_nil, or_false,
        or_imp, forall_and, forall_eq, or_true]
    all_goals sha1_norm
  have ha := he.agrees.mono hfoot
  rw [hs] at ha
  apply ha.widen
  · intro c hc hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all (config := {decide := true, implicitDefEqProofs := false}) only
      [Component.isMem, scratchComponents, x86_compose]
  · intro address c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hCov.elim
      | exact scratchComponents_stack (Or.inl (by decide +kernel)) hCov

theorem effect035_rip {s t : RamState} (he : (effect035 s).Holds s t) :
    t.RIP = 0x102c8b := by
  exact he.rip.trans (by rfl)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem genericWords035 {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) {s t : RamState}
    (hW35 : W 35 = (W 32 ^^^ W 27 ^^^ W 21 ^^^ W 19).rotateLeft 1)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (hw : Write.AllHold s (genericCut035 stack input H A W))
    (he : (effect035 s).Holds s t) :
    Write.AllHold t (genericCut036 stack input H A W) := by
  have hfull : ∀ w ∈ (effect035 s).writes, w.Full := by
    apply Effect.Local.full
    unfold effect035
    repeat' first | (solve | x86_local) | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  sha1_norm at hs
  simp only [genericCut035, Write.AllHold] at hw
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29⟩ := hw
  have h11low := (read32_of_read64_low (s := s) (a := (stack + 0))
    (v := (Operand.mem ((stack + 0)) : Operand 64).read s) rfl).symm.trans h11
  have h12low := (read32_of_read64_low (s := s) (a := (stack + 4))
    (v := (Operand.mem ((stack + 4)) : Operand 64).read s) rfl).symm.trans h12
  have h13low := (read32_of_read64_low (s := s) (a := (stack + 8))
    (v := (Operand.mem ((stack + 8)) : Operand 64).read s) rfl).symm.trans h13
  have h14low := (read32_of_read64_low (s := s) (a := (stack + 12))
    (v := (Operand.mem ((stack + 12)) : Operand 64).read s) rfl).symm.trans h14
  have h15low := (read32_of_read64_low (s := s) (a := (stack + 16))
    (v := (Operand.mem ((stack + 16)) : Operand 64).read s) rfl).symm.trans h15
  have h16low := (read32_of_read64_low (s := s) (a := (stack + 24))
    (v := (Operand.mem ((stack + 24)) : Operand 64).read s) rfl).symm.trans h16
  have h17low := (read32_of_read64_low (s := s) (a := (stack + 32))
    (v := (Operand.mem ((stack + 32)) : Operand 64).read s) rfl).symm.trans h17
  have h18low := (read32_of_read64_low (s := s) (a := (stack + 40))
    (v := (Operand.mem ((stack + 40)) : Operand 64).read s) rfl).symm.trans h18
  have h19low := (read32_of_read64_low (s := s) (a := (stack + 48))
    (v := (Operand.mem ((stack + 48)) : Operand 64).read s) rfl).symm.trans h19
  have h21low := (read32_of_read64_low (s := s) (a := (stack + 72))
    (v := (Operand.mem ((stack + 72)) : Operand 64).read s) rfl).symm.trans h21
  have h22low := (read32_of_read64_low (s := s) (a := (stack + 80))
    (v := (Operand.mem ((stack + 80)) : Operand 64).read s) rfl).symm.trans h22
  have h23low := (read32_of_read64_low (s := s) (a := (stack + 88))
    (v := (Operand.mem ((stack + 88)) : Operand 64).read s) rfl).symm.trans h23
  have h24low := (read32_of_read64_low (s := s) (a := (stack + 96))
    (v := (Operand.mem ((stack + 96)) : Operand 64).read s) rfl).symm.trans h24
  have h25low := (read32_of_read64_low (s := s) (a := (stack + 116))
    (v := (Operand.mem ((stack + 116)) : Operand 64).read s) rfl).symm.trans h25
  have h26low := (read32_of_read64_low (s := s) (a := (stack + 120))
    (v := (Operand.mem ((stack + 120)) : Operand 64).read s) rfl).symm.trans h26
  have h27low := (read32_of_read64_low (s := s) (a := (stack + 124))
    (v := (Operand.mem ((stack + 124)) : Operand 64).read s) rfl).symm.trans h27
  have h28low := (read32_of_read64_low (s := s) (a := (stack + 144))
    (v := (Operand.mem ((stack + 144)) : Operand 64).read s) rfl).symm.trans h28
  have h29low := (read32_of_read64_low (s := s) (a := (stack + 152))
    (v := (Operand.mem ((stack + 152)) : Operand 64).read s) rfl).symm.trans h29
  sha1_norm at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29
  simp only [genericCut036, Write.AllHold, ← ho.read_reg, ← ho.read_mem]
  sha1_norm [effect035, hs, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h11low, h12low, h13low, h14low, h15low, h16low, h17low, h18low, h19low, h21low, h22low, h23low, h24low, h25low, h26low, h27low, h28low, h29low,
    read32_memStore64_low, BitVec.setWidth_add, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, leaSpec]
  rw [hW35]
  all_goals sha1_norm [← BitVec.setWidth_eq_extractLsb' (by decide : 32 ≤ 64),
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
  simp_all (config := {implicitDefEqProofs := false, decide := true})
  all_goals repeat' first | (solve | ac_rfl) | apply And.intro

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
theorem effect035_words {stack input : BitVec 64}
    {H : Vector (BitVec 32) 5} {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s) (hw : Write.AllHold s (cut035 stack input H M))
    (he : (effect035 s).Holds s t) : Write.AllHold t (cut036 stack input H M) := by
  let A : Nat → BitVec 32 := fun n ↦ (workingAfter M H n).a
  let W : Fin 80 → BitVec 32 := scheduleWord M
  have hW35 : W 35 = (W 32 ^^^ W 27 ^^^ W 21 ^^^ W 19).rotateLeft 1 := by
    dsimp [W]
    change scheduleWord M (⟨35, by decide⟩ : Fin 80) = _
    rw [scheduleWord_recurrence M ⟨35, by decide⟩ (by decide)]
    simp only [Nat.reduceSub]
    rw [sha1Rotl_eq_rotateLeft 1 _ (by decide)]
    rfl
  have hpre : Write.AllHold s (genericCut035 stack input H A W) := by
    change Write.AllHold s (cut035 stack input H M)
    exact hw
  have hraw := genericWords035 A W hW35 hf.stackPointer hpre he
  change Write.AllHold t (cut036 stack input H M)
  exact hraw

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
theorem segment035 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x102c56 0x102c8b cut035 cut036 := by
  have hout : ∀ d : Nat, d ≤ bytes035.length →
      0x102c56 + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    simp only [bytes035, List.length_cons, List.length_nil] at hd
    apply outsideCompression_ne hOutside
    · change 0x1024e0 ≤ (0x102c56 + d % 2^64) % 2^64
      omega
    · change (0x102c56 + d % 2^64) % 2^64 < 0x1036df
      omega
  apply Segment.of_block (fun _ _ _ _ => effect035)
    (fun stack input H M => block035 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64 0x2c56) bytes035,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact effect035_rip he
  · intro stack input H M s t _ hf _ he
    exact effect035_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect035_words hf hw he

def bytes036 : List UInt8 :=
  [0x31, 0xd0, 0x31, 0xf8, 0xc1, 0xc7, 0x1e, 0x48, 0x8b, 0x4c, 0x24, 0x20, 0x44, 0x8b, 0x54, 0x24, 0x8, 0x41, 0x31, 0xca, 0x44, 0x31, 0xf1, 0x31, 0xd9, 0x44, 0x31, 0xc9, 0xd1, 0xc1, 0x49, 0x89, 0xc9, 0x48, 0x89, 0x4c, 0x24, 0x20, 0x41, 0x8d, 0xc, 0x30, 0x81, 0xc1, 0xa1, 0xeb, 0xd9, 0x6e, 0x41, 0x89, 0xc8, 0x41, 0xc1, 0xc0, 0x1e, 0x44, 0x89, 0xc6, 0x31, 0xfe]

set_option maxHeartbeats 800000 in
def effect036 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq ((xorR32R32Effect 0x102c8b 2 0 2)) (xorR32R32Effect 0x102c8d 2 0 7)) (rolR32Effect 0x102c8f 3 7 30)) (movR64M64Effect 0x102c92 1 (.sib 4 none 0 (.d8 0x20)))) (movR32M32Effect 0x102c97 10 (.sib 4 none 0 (.d8 0x8)))) (xorR32R32Effect 0x102c9c 3 10 1)) (xorR32R32Effect 0x102c9f 3 1 14)) (xorR32R32Effect 0x102ca2 2 1 3)) (xorR32R32Effect 0x102ca4 3 1 9)) (rolR32Effect 0x102ca7 2 1 1)) (movR64R64Effect 0x102ca9 9 1)) (movM64R64Effect 0x102cac 1 (.sib 4 none 0 (.d8 0x20)))) (leaR32Effect 0x102cb1 4 1 (.sib 8 (some 6) 0 .none))) (addR32Imm32Effect 0x102cb5 6 1 0x6ed9eba1)) (movR32R32Effect 0x102cbb 3 8 1)) (rolR32Effect 0x102cbe 4 8 30)) (movR32R32Effect 0x102cc2 3 6 8)) (xorR32R32Effect 0x102cc5 2 6 7)

set_option maxHeartbeats 1600000 in
theorem block036 [Bindings] (boundary : ReturnBoundary)
    (stack input : BitVec 64) (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes036.length → 0x102c8b + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x102c8b ∧ FrameData stack input M s ∧
        Write.AllHold s (cut036 stack input H M))
      (codeRange 0x102c8b bytes036) effect036 := by
  unfold bytes036 at hout ⊢
  sha1_run_begin (xor_r32_r32_effect_step 0x102c8b 0xd0 (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x102c8d 0xf8 (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x102c8f 0xc7 0x1e (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r64_m64_effect_step 0x102c92 0x48 (by unfold RexWPrefix; decide +kernel) 1 (.sib 4 none 0 (.d8 0x20)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_m32_effect_step 0x102c97 0x44 (by unfold RexNoWPrefix; decide +kernel) 2 (.sib 4 none 0 (.d8 0x8)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102c9c 0x41 0xca (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102c9f 0x44 0xf1 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x102ca2 0xd9 (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102ca4 0x44 0xc9 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_one_effect_step 0x102ca7 0xc1 (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r64_r64_effect_step 0x102ca9 0x49 0xc9 (by unfold RexWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m64_r64_effect_step 0x102cac 0x48 (by unfold RexWPrefix; decide +kernel) 1 (.sib 4 none 0 (.d8 0x20)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (lea_r32_rex_effect_step 0x102cb1 0x41 (by unfold RexNoWPrefix; decide +kernel) 1 (.sib 8 (some 6) 0 .none) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_imm32_effect_step 0x102cb5 0xc1 0x6ed9eba1 (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x102cbb 0x41 0xc8 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_imm8_rex_effect_step 0x102cbe 0x41 0xc0 0x1e (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x102cc2 0x44 0xc6 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x102cc5 0xfe (by decide +kernel))
  sha1_run_finish [effect036]



set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
theorem effect036_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s) (he : (effect036 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have hfoot : ∀ c ∈ (effect036 s).components, c ∈ [.mem ((Operand.reg 4 : Operand 64).read s + BitVec.ofNat 64 32) 8, .reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] := by
    unfold effect036
    iterate 17 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [xorR32R32Effect_components, rolR32Effect_components, movR64M64Effect_components, movR32M32Effect_components, movR64R64Effect_components, movM64R64Effect_components, leaR32Effect_components, addR32Imm32Effect_components, movR32R32Effect_components, List.mem_cons, List.not_mem_nil, or_false,
        or_imp, forall_and, forall_eq, or_true]
    all_goals sha1_norm
  have ha := he.agrees.mono hfoot
  rw [hs] at ha
  apply ha.widen
  · intro c hc hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all (config := {decide := true, implicitDefEqProofs := false}) only
      [Component.isMem, scratchComponents, x86_compose]
  · intro address c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hCov.elim
      | exact scratchComponents_stack (Or.inl (by decide +kernel)) hCov

theorem effect036_rip {s t : RamState} (he : (effect036 s).Holds s t) :
    t.RIP = 0x102cc7 := by
  exact he.rip.trans (by rfl)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem genericWords036 {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) {s t : RamState}
    (hA35 : A 35 = (A 34).rotateLeft 5 + (A 33 ^^^ (A 32).rotateLeft 30 ^^^ (A 31).rotateLeft 30) + (A 30).rotateLeft 30 + 0x6ed9eba1 + W 34)
    (hW38 : W 38 = (W 35 ^^^ W 30 ^^^ W 24 ^^^ W 22).rotateLeft 1)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (hw : Write.AllHold s (genericCut036 stack input H A W))
    (he : (effect036 s).Holds s t) :
    Write.AllHold t (genericCut037 stack input H A W) := by
  have hfull : ∀ w ∈ (effect036 s).writes, w.Full := by
    apply Effect.Local.full
    unfold effect036
    repeat' first | (solve | x86_local) | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  sha1_norm at hs
  simp only [genericCut036, Write.AllHold] at hw
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩ := hw
  have h12low := (read32_of_read64_low (s := s) (a := (stack + 0))
    (v := (Operand.mem ((stack + 0)) : Operand 64).read s) rfl).symm.trans h12
  have h13low := (read32_of_read64_low (s := s) (a := (stack + 4))
    (v := (Operand.mem ((stack + 4)) : Operand 64).read s) rfl).symm.trans h13
  have h14low := (read32_of_read64_low (s := s) (a := (stack + 8))
    (v := (Operand.mem ((stack + 8)) : Operand 64).read s) rfl).symm.trans h14
  have h15low := (read32_of_read64_low (s := s) (a := (stack + 12))
    (v := (Operand.mem ((stack + 12)) : Operand 64).read s) rfl).symm.trans h15
  have h16low := (read32_of_read64_low (s := s) (a := (stack + 16))
    (v := (Operand.mem ((stack + 16)) : Operand 64).read s) rfl).symm.trans h16
  have h17low := (read32_of_read64_low (s := s) (a := (stack + 24))
    (v := (Operand.mem ((stack + 24)) : Operand 64).read s) rfl).symm.trans h17
  have h18low := (read32_of_read64_low (s := s) (a := (stack + 32))
    (v := (Operand.mem ((stack + 32)) : Operand 64).read s) rfl).symm.trans h18
  have h19low := (read32_of_read64_low (s := s) (a := (stack + 40))
    (v := (Operand.mem ((stack + 40)) : Operand 64).read s) rfl).symm.trans h19
  have h20low := (read32_of_read64_low (s := s) (a := (stack + 48))
    (v := (Operand.mem ((stack + 48)) : Operand 64).read s) rfl).symm.trans h20
  have h21low := (read32_of_read64_low (s := s) (a := (stack + 56))
    (v := (Operand.mem ((stack + 56)) : Operand 64).read s) rfl).symm.trans h21
  have h23low := (read32_of_read64_low (s := s) (a := (stack + 72))
    (v := (Operand.mem ((stack + 72)) : Operand 64).read s) rfl).symm.trans h23
  have h24low := (read32_of_read64_low (s := s) (a := (stack + 80))
    (v := (Operand.mem ((stack + 80)) : Operand 64).read s) rfl).symm.trans h24
  have h25low := (read32_of_read64_low (s := s) (a := (stack + 88))
    (v := (Operand.mem ((stack + 88)) : Operand 64).read s) rfl).symm.trans h25
  have h26low := (read32_of_read64_low (s := s) (a := (stack + 96))
    (v := (Operand.mem ((stack + 96)) : Operand 64).read s) rfl).symm.trans h26
  have h27low := (read32_of_read64_low (s := s) (a := (stack + 116))
    (v := (Operand.mem ((stack + 116)) : Operand 64).read s) rfl).symm.trans h27
  have h28low := (read32_of_read64_low (s := s) (a := (stack + 120))
    (v := (Operand.mem ((stack + 120)) : Operand 64).read s) rfl).symm.trans h28
  have h29low := (read32_of_read64_low (s := s) (a := (stack + 124))
    (v := (Operand.mem ((stack + 124)) : Operand 64).read s) rfl).symm.trans h29
  have h30low := (read32_of_read64_low (s := s) (a := (stack + 144))
    (v := (Operand.mem ((stack + 144)) : Operand 64).read s) rfl).symm.trans h30
  have h31low := (read32_of_read64_low (s := s) (a := (stack + 152))
    (v := (Operand.mem ((stack + 152)) : Operand 64).read s) rfl).symm.trans h31
  sha1_norm at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31
  simp only [genericCut037, Write.AllHold, ← ho.read_reg, ← ho.read_mem]
  sha1_norm [effect036, hs, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h12low, h13low, h14low, h15low, h16low, h17low, h18low, h19low, h20low, h21low, h23low, h24low, h25low, h26low, h27low, h28low, h29low, h30low, h31low,
    read32_memStore64_low, BitVec.setWidth_add, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, leaSpec]
  rw [hA35, hW38]
  all_goals sha1_norm [← BitVec.setWidth_eq_extractLsb' (by decide : 32 ≤ 64),
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
  simp_all (config := {implicitDefEqProofs := false, decide := true})
  all_goals repeat' first | (solve | ac_rfl) | apply And.intro

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
theorem effect036_words {stack input : BitVec 64}
    {H : Vector (BitVec 32) 5} {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s) (hw : Write.AllHold s (cut036 stack input H M))
    (he : (effect036 s).Holds s t) : Write.AllHold t (cut037 stack input H M) := by
  let A : Nat → BitVec 32 := fun n ↦ (workingAfter M H n).a
  let W : Fin 80 → BitVec 32 := scheduleWord M
  have hA35 : A 35 = (A 34).rotateLeft 5 + (A 33 ^^^ (A 32).rotateLeft 30 ^^^ (A 31).rotateLeft 30) + (A 30).rotateLeft 30 + 0x6ed9eba1 + W 34 := by
    dsimp [A, W]
    rw [workingAfter_step_a_values M H 30 (by decide +kernel),
      sha1_f_parity_first (by decide +kernel) (by decide +kernel)]
    simp [K, Parity]
  have hW38 : W 38 = (W 35 ^^^ W 30 ^^^ W 24 ^^^ W 22).rotateLeft 1 := by
    dsimp [W]
    change scheduleWord M (⟨38, by decide⟩ : Fin 80) = _
    rw [scheduleWord_recurrence M ⟨38, by decide⟩ (by decide)]
    simp only [Nat.reduceSub]
    rw [sha1Rotl_eq_rotateLeft 1 _ (by decide)]
    rfl
  have hpre : Write.AllHold s (genericCut036 stack input H A W) := by
    change Write.AllHold s (cut036 stack input H M)
    exact hw
  have hraw := genericWords036 A W hA35 hW38 hf.stackPointer hpre he
  change Write.AllHold t (cut037 stack input H M)
  exact hraw

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
theorem segment036 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x102c8b 0x102cc7 cut036 cut037 := by
  have hout : ∀ d : Nat, d ≤ bytes036.length →
      0x102c8b + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    simp only [bytes036, List.length_cons, List.length_nil] at hd
    apply outsideCompression_ne hOutside
    · change 0x1024e0 ≤ (0x102c8b + d % 2^64) % 2^64
      omega
    · change (0x102c8b + d % 2^64) % 2^64 < 0x1036df
      omega
  apply Segment.of_block (fun _ _ _ _ => effect036)
    (fun stack input H M => block036 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64 0x2c8b) bytes036,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact effect036_rip he
  · intro stack input H M s t _ hf _ he
    exact effect036_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect036_words hf hw he

def bytes037 : List UInt8 :=
  [0x41, 0x8d, 0x2c, 0x39, 0x44, 0x31, 0xdf, 0x31, 0xcf, 0xc1, 0xc1, 0x5, 0x44, 0x1, 0xe0, 0x44, 0x8d, 0xc, 0x1, 0x41, 0x81, 0xc1, 0xa1, 0xeb, 0xd9, 0x6e, 0x4c, 0x8b, 0x64, 0x24, 0x60, 0x45, 0x31, 0xe2, 0x45, 0x31, 0xfa, 0x41, 0xd1, 0xc2, 0x44, 0x1, 0xd2, 0x44, 0x89, 0xd1, 0x44, 0x89, 0x54, 0x24, 0x8, 0x1, 0xfa, 0x44, 0x89, 0xc8, 0xc1, 0xc0, 0x5, 0x44, 0x8d, 0x14, 0x10, 0x41, 0x81, 0xc2, 0xa1, 0xeb, 0xd9, 0x6e, 0x48, 0x8b, 0x44, 0x24, 0x28]

set_option maxHeartbeats 800000 in
def effect037 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq ((leaR32Effect 0x102cc7 4 5 (.sib 9 (some 7) 0 .none))) (xorR32R32Effect 0x102ccb 3 7 11)) (xorR32R32Effect 0x102cce 2 7 1)) (rolR32Effect 0x102cd0 3 1 5)) (addR32R32Effect 0x102cd3 3 0 12)) (leaR32Effect 0x102cd6 4 9 (.sib 1 (some 0) 0 .none))) (addR32Imm32Effect 0x102cda 7 9 0x6ed9eba1)) (movR64M64Effect 0x102ce1 12 (.sib 4 none 0 (.d8 0x60)))) (xorR32R32Effect 0x102ce6 3 10 12)) (xorR32R32Effect 0x102ce9 3 10 15)) (rolR32Effect 0x102cec 3 10 1)) (addR32R32Effect 0x102cef 3 2 10)) (movR32R32Effect 0x102cf2 3 1 10)) (movM32R32Effect 0x102cf5 10 (.sib 4 none 0 (.d8 0x8)))) (addR32R32Effect 0x102cfa 2 2 7)) (movR32R32Effect 0x102cfc 3 0 9)) (rolR32Effect 0x102cff 3 0 5)) (leaR32Effect 0x102d02 4 10 (.sib 0 (some 2) 0 .none))) (addR32Imm32Effect 0x102d06 7 10 0x6ed9eba1)) (movR64M64Effect 0x102d0d 0 (.sib 4 none 0 (.d8 0x28)))

set_option maxHeartbeats 1600000 in
theorem block037 [Bindings] (boundary : ReturnBoundary)
    (stack input : BitVec 64) (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes037.length → 0x102cc7 + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x102cc7 ∧ FrameData stack input M s ∧
        Write.AllHold s (cut037 stack input H M))
      (codeRange 0x102cc7 bytes037) effect037 := by
  unfold bytes037 at hout ⊢
  sha1_run_begin (lea_r32_rex_effect_step 0x102cc7 0x41 (by unfold RexNoWPrefix; decide +kernel) 5 (.sib 9 (some 7) 0 .none) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102ccb 0x44 0xdf (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x102cce 0xcf (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x102cd0 0xc1 0x5 (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x102cd3 0x44 0xe0 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (lea_r32_rex_effect_step 0x102cd6 0x44 (by unfold RexNoWPrefix; decide +kernel) 1 (.sib 1 (some 0) 0 .none) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_imm32_rex_effect_step 0x102cda 0x41 0xc1 0x6ed9eba1 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r64_m64_effect_step 0x102ce1 0x4c (by unfold RexWPrefix; decide +kernel) 4 (.sib 4 none 0 (.d8 0x60)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102ce6 0x45 0xe2 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102ce9 0x45 0xfa (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_one_rex_effect_step 0x102cec 0x41 0xc2 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x102cef 0x44 0xd2 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x102cf2 0x44 0xd1 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m32_r32_effect_step 0x102cf5 0x44 (by unfold RexNoWPrefix; decide +kernel) 2 (.sib 4 none 0 (.d8 0x8)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_effect_step 0x102cfa 0xfa (by decide +kernel))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x102cfc 0x44 0xc8 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x102cff 0xc0 0x5 (by decide +kernel) (by decide +kernel))
  sha1_run_then (lea_r32_rex_effect_step 0x102d02 0x44 (by unfold RexNoWPrefix; decide +kernel) 2 (.sib 0 (some 2) 0 .none) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_imm32_rex_effect_step 0x102d06 0x41 0xc2 0x6ed9eba1 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r64_m64_effect_step 0x102d0d 0x48 (by unfold RexWPrefix; decide +kernel) 0 (.sib 4 none 0 (.d8 0x28)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_finish [effect037]



set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
theorem effect037_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s) (he : (effect037 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have hfoot : ∀ c ∈ (effect037 s).components, c ∈ [.mem ((Operand.reg 4 : Operand 64).read s + BitVec.ofNat 64 8) 4, .reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] := by
    unfold effect037
    iterate 19 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [leaR32Effect_components, xorR32R32Effect_components, rolR32Effect_components, addR32R32Effect_components, addR32Imm32Effect_components, movR64M64Effect_components, movR32R32Effect_components, movM32R32Effect_components, List.mem_cons, List.not_mem_nil, or_false,
        or_imp, forall_and, forall_eq, or_true]
    all_goals sha1_norm
  have ha := he.agrees.mono hfoot
  rw [hs] at ha
  apply ha.widen
  · intro c hc hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all (config := {decide := true, implicitDefEqProofs := false}) only
      [Component.isMem, scratchComponents, x86_compose]
  · intro address c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hCov.elim
      | exact scratchComponents_stack (Or.inl (by decide +kernel)) hCov

theorem effect037_rip {s t : RamState} (he : (effect037 s).Holds s t) :
    t.RIP = 0x102d12 := by
  exact he.rip.trans (by rfl)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem genericWords037 {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) {s t : RamState}
    (hA36 : A 36 = (A 35).rotateLeft 5 + (A 34 ^^^ (A 33).rotateLeft 30 ^^^ (A 32).rotateLeft 30) + (A 31).rotateLeft 30 + 0x6ed9eba1 + W 35)
    (hA37 : A 37 = (A 36).rotateLeft 5 + (A 35 ^^^ (A 34).rotateLeft 30 ^^^ (A 33).rotateLeft 30) + (A 32).rotateLeft 30 + 0x6ed9eba1 + W 36)
    (hW36 : W 36 = (W 33 ^^^ W 28 ^^^ W 22 ^^^ W 20).rotateLeft 1)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (hw : Write.AllHold s (genericCut037 stack input H A W))
    (he : (effect037 s).Holds s t) :
    Write.AllHold t (genericCut038 stack input H A W) := by
  have hfull : ∀ w ∈ (effect037 s).writes, w.Full := by
    apply Effect.Local.full
    unfold effect037
    repeat' first | (solve | x86_local) | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  sha1_norm at hs
  simp only [genericCut037, Write.AllHold] at hw
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩ := hw
  have h13low := (read32_of_read64_low (s := s) (a := (stack + 0))
    (v := (Operand.mem ((stack + 0)) : Operand 64).read s) rfl).symm.trans h13
  have h14low := (read32_of_read64_low (s := s) (a := (stack + 4))
    (v := (Operand.mem ((stack + 4)) : Operand 64).read s) rfl).symm.trans h14
  have h15low := (read32_of_read64_low (s := s) (a := (stack + 12))
    (v := (Operand.mem ((stack + 12)) : Operand 64).read s) rfl).symm.trans h15
  have h16low := (read32_of_read64_low (s := s) (a := (stack + 16))
    (v := (Operand.mem ((stack + 16)) : Operand 64).read s) rfl).symm.trans h16
  have h17low := (read32_of_read64_low (s := s) (a := (stack + 24))
    (v := (Operand.mem ((stack + 24)) : Operand 64).read s) rfl).symm.trans h17
  have h18low := (read32_of_read64_low (s := s) (a := (stack + 32))
    (v := (Operand.mem ((stack + 32)) : Operand 64).read s) rfl).symm.trans h18
  have h19low := (read32_of_read64_low (s := s) (a := (stack + 40))
    (v := (Operand.mem ((stack + 40)) : Operand 64).read s) rfl).symm.trans h19
  have h20low := (read32_of_read64_low (s := s) (a := (stack + 48))
    (v := (Operand.mem ((stack + 48)) : Operand 64).read s) rfl).symm.trans h20
  have h21low := (read32_of_read64_low (s := s) (a := (stack + 56))
    (v := (Operand.mem ((stack + 56)) : Operand 64).read s) rfl).symm.trans h21
  have h23low := (read32_of_read64_low (s := s) (a := (stack + 72))
    (v := (Operand.mem ((stack + 72)) : Operand 64).read s) rfl).symm.trans h23
  have h24low := (read32_of_read64_low (s := s) (a := (stack + 80))
    (v := (Operand.mem ((stack + 80)) : Operand 64).read s) rfl).symm.trans h24
  have h25low := (read32_of_read64_low (s := s) (a := (stack + 88))
    (v := (Operand.mem ((stack + 88)) : Operand 64).read s) rfl).symm.trans h25
  have h26low := (read32_of_read64_low (s := s) (a := (stack + 96))
    (v := (Operand.mem ((stack + 96)) : Operand 64).read s) rfl).symm.trans h26
  have h27low := (read32_of_read64_low (s := s) (a := (stack + 116))
    (v := (Operand.mem ((stack + 116)) : Operand 64).read s) rfl).symm.trans h27
  have h28low := (read32_of_read64_low (s := s) (a := (stack + 120))
    (v := (Operand.mem ((stack + 120)) : Operand 64).read s) rfl).symm.trans h28
  have h29low := (read32_of_read64_low (s := s) (a := (stack + 124))
    (v := (Operand.mem ((stack + 124)) : Operand 64).read s) rfl).symm.trans h29
  have h30low := (read32_of_read64_low (s := s) (a := (stack + 144))
    (v := (Operand.mem ((stack + 144)) : Operand 64).read s) rfl).symm.trans h30
  have h31low := (read32_of_read64_low (s := s) (a := (stack + 152))
    (v := (Operand.mem ((stack + 152)) : Operand 64).read s) rfl).symm.trans h31
  sha1_norm at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31
  simp only [genericCut038, Write.AllHold, ← ho.read_reg, ← ho.read_mem]
  sha1_norm [effect037, hs, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h13low, h14low, h15low, h16low, h17low, h18low, h19low, h20low, h21low, h23low, h24low, h25low, h26low, h27low, h28low, h29low, h30low, h31low,
    read32_memStore64_low, BitVec.setWidth_add, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, leaSpec]
  rw [hA36, hA37, hW36]
  all_goals sha1_norm [← BitVec.setWidth_eq_extractLsb' (by decide : 32 ≤ 64),
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
  simp_all (config := {implicitDefEqProofs := false, decide := true})
  all_goals repeat' first | (solve | ac_rfl) | apply And.intro

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
theorem effect037_words {stack input : BitVec 64}
    {H : Vector (BitVec 32) 5} {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s) (hw : Write.AllHold s (cut037 stack input H M))
    (he : (effect037 s).Holds s t) : Write.AllHold t (cut038 stack input H M) := by
  let A : Nat → BitVec 32 := fun n ↦ (workingAfter M H n).a
  let W : Fin 80 → BitVec 32 := scheduleWord M
  have hA36 : A 36 = (A 35).rotateLeft 5 + (A 34 ^^^ (A 33).rotateLeft 30 ^^^ (A 32).rotateLeft 30) + (A 31).rotateLeft 30 + 0x6ed9eba1 + W 35 := by
    dsimp [A, W]
    rw [workingAfter_step_a_values M H 31 (by decide +kernel),
      sha1_f_parity_first (by decide +kernel) (by decide +kernel)]
    simp [K, Parity]
  have hA37 : A 37 = (A 36).rotateLeft 5 + (A 35 ^^^ (A 34).rotateLeft 30 ^^^ (A 33).rotateLeft 30) + (A 32).rotateLeft 30 + 0x6ed9eba1 + W 36 := by
    dsimp [A, W]
    rw [workingAfter_step_a_values M H 32 (by decide +kernel),
      sha1_f_parity_first (by decide +kernel) (by decide +kernel)]
    simp [K, Parity]
  have hW36 : W 36 = (W 33 ^^^ W 28 ^^^ W 22 ^^^ W 20).rotateLeft 1 := by
    dsimp [W]
    change scheduleWord M (⟨36, by decide⟩ : Fin 80) = _
    rw [scheduleWord_recurrence M ⟨36, by decide⟩ (by decide)]
    simp only [Nat.reduceSub]
    rw [sha1Rotl_eq_rotateLeft 1 _ (by decide)]
    rfl
  have hpre : Write.AllHold s (genericCut037 stack input H A W) := by
    change Write.AllHold s (cut037 stack input H M)
    exact hw
  have hraw := genericWords037 A W hA36 hA37 hW36 hf.stackPointer hpre he
  change Write.AllHold t (cut038 stack input H M)
  exact hraw

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
theorem segment037 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x102cc7 0x102d12 cut037 cut038 := by
  have hout : ∀ d : Nat, d ≤ bytes037.length →
      0x102cc7 + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    simp only [bytes037, List.length_cons, List.length_nil] at hd
    apply outsideCompression_ne hOutside
    · change 0x1024e0 ≤ (0x102cc7 + d % 2^64) % 2^64
      omega
    · change (0x102cc7 + d % 2^64) % 2^64 < 0x1036df
      omega
  apply Segment.of_block (fun _ _ _ _ => effect037)
    (fun stack input H M => block037 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64 0x2cc7) bytes037,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact effect037_rip he
  · intro stack input H M s t _ hf _ he
    exact effect037_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect037_words hf hw he

def bytes038 : List UInt8 :=
  [0x8b, 0x54, 0x24, 0x4, 0x31, 0xc2, 0x44, 0x31, 0xe8, 0x4c, 0x8b, 0x6c, 0x24, 0x10, 0x44, 0x31, 0xea, 0x33, 0x44, 0x24, 0x30, 0x48, 0x8b, 0x5c, 0x24, 0x58, 0x31, 0xda, 0xd1, 0xc2, 0x89, 0x54, 0x24, 0x4, 0x31, 0xc8, 0xd1, 0xc0, 0x48, 0x89, 0xc7, 0x44, 0x31, 0xce, 0x41, 0x1, 0xd3, 0x41, 0x1, 0xf3, 0x44, 0x89, 0xd0, 0xc1, 0xc0, 0x5, 0x42, 0x8d, 0x34, 0x18, 0x81, 0xc6, 0xa1, 0xeb, 0xd9, 0x6e]

set_option maxHeartbeats 800000 in
def effect038 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq ((movR32M32LowEffect 0x102d12 2 (.sib 4 none 0 (.d8 0x4)))) (xorR32R32Effect 0x102d16 2 2 0)) (xorR32R32Effect 0x102d18 3 0 13)) (movR64M64Effect 0x102d1b 13 (.sib 4 none 0 (.d8 0x10)))) (xorR32R32Effect 0x102d20 3 2 13)) (xorR32M32LowEffect 0x102d23 0 (.sib 4 none 0 (.d8 0x30)))) (movR64M64Effect 0x102d27 3 (.sib 4 none 0 (.d8 0x58)))) (xorR32R32Effect 0x102d2c 2 2 3)) (rolR32Effect 0x102d2e 2 2 1)) (movM32R32LowEffect 0x102d30 2 (.sib 4 none 0 (.d8 0x4)))) (xorR32R32Effect 0x102d34 2 0 1)) (rolR32Effect 0x102d36 2 0 1)) (movR64R64Effect 0x102d38 7 0)) (xorR32R32Effect 0x102d3b 3 6 9)) (addR32R32Effect 0x102d3e 3 11 2)) (addR32R32Effect 0x102d41 3 11 6)) (movR32R32Effect 0x102d44 3 0 10)) (rolR32Effect 0x102d47 3 0 5)) (leaR32Effect 0x102d4a 4 6 (.sib 0 (some 11) 0 .none))) (addR32Imm32Effect 0x102d4e 6 6 0x6ed9eba1)

set_option maxHeartbeats 1600000 in
theorem block038 [Bindings] (boundary : ReturnBoundary)
    (stack input : BitVec 64) (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes038.length → 0x102d12 + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x102d12 ∧ FrameData stack input M s ∧
        Write.AllHold s (cut038 stack input H M))
      (codeRange 0x102d12 bytes038) effect038 := by
  unfold bytes038 at hout ⊢
  sha1_run_begin (mov_r32_m32_low_effect_step 0x102d12 2 (.sib 4 none 0 (.d8 0x4)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x102d16 0xc2 (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102d18 0x44 0xe8 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r64_m64_effect_step 0x102d1b 0x4c (by unfold RexWPrefix; decide +kernel) 5 (.sib 4 none 0 (.d8 0x10)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102d20 0x44 0xea (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_m32_low_effect_step 0x102d23 0 (.sib 4 none 0 (.d8 0x30)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r64_m64_effect_step 0x102d27 0x48 (by unfold RexWPrefix; decide +kernel) 3 (.sib 4 none 0 (.d8 0x58)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x102d2c 0xda (by decide +kernel))
  sha1_run_then (rol_r32_one_effect_step 0x102d2e 0xc2 (by decide +kernel) (by decide +kernel))
  sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m32_r32_low_effect_step 0x102d30 2 (.sib 4 none 0 (.d8 0x4)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x102d34 0xc8 (by decide +kernel))
  sha1_run_then (rol_r32_one_effect_step 0x102d36 0xc0 (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r64_r64_effect_step 0x102d38 0x48 0xc7 (by unfold RexWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102d3b 0x44 0xce (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x102d3e 0x41 0xd3 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x102d41 0x41 0xf3 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x102d44 0x44 0xd0 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x102d47 0xc0 0x5 (by decide +kernel) (by decide +kernel))
  sha1_run_then (lea_r32_rex_effect_step 0x102d4a 0x42 (by unfold RexNoWPrefix; decide +kernel) 6 (.sib 0 (some 11) 0 .none) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_imm32_effect_step 0x102d4e 0xc6 0x6ed9eba1 (by decide +kernel) (by decide +kernel))
  sha1_run_finish [effect038]



set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
theorem effect038_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s) (he : (effect038 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have hfoot : ∀ c ∈ (effect038 s).components, c ∈ [.mem ((Operand.reg 4 : Operand 64).read s + BitVec.ofNat 64 4) 4, .reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] := by
    unfold effect038
    iterate 19 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [movR32M32LowEffect_components, xorR32R32Effect_components, movR64M64Effect_components, xorR32M32LowEffect_components, rolR32Effect_components, movM32R32LowEffect, storeEffect_components, movR64R64Effect_components, addR32R32Effect_components, movR32R32Effect_components, leaR32Effect_components, addR32Imm32Effect_components, List.mem_cons, List.not_mem_nil, or_false,
        or_imp, forall_and, forall_eq, or_true]
    all_goals sha1_norm
  have ha := he.agrees.mono hfoot
  rw [hs] at ha
  apply ha.widen
  · intro c hc hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all (config := {decide := true, implicitDefEqProofs := false}) only
      [Component.isMem, scratchComponents, x86_compose]
  · intro address c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hCov.elim
      | exact scratchComponents_stack (Or.inl (by decide +kernel)) hCov

theorem effect038_rip {s t : RamState} (he : (effect038 s).Holds s t) :
    t.RIP = 0x102d54 := by
  exact he.rip.trans (by rfl)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem genericWords038 {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) {s t : RamState}
    (hA38 : A 38 = (A 37).rotateLeft 5 + (A 36 ^^^ (A 35).rotateLeft 30 ^^^ (A 34).rotateLeft 30) + (A 33).rotateLeft 30 + 0x6ed9eba1 + W 37)
    (hW37 : W 37 = (W 34 ^^^ W 29 ^^^ W 23 ^^^ W 21).rotateLeft 1)
    (hW39 : W 39 = (W 36 ^^^ W 31 ^^^ W 25 ^^^ W 23).rotateLeft 1)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (hw : Write.AllHold s (genericCut038 stack input H A W))
    (he : (effect038 s).Holds s t) :
    Write.AllHold t (genericCut039 stack input H A W) := by
  have hfull : ∀ w ∈ (effect038 s).writes, w.Full := by
    apply Effect.Local.full
    unfold effect038
    repeat' first | (solve | x86_local) | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  sha1_norm at hs
  simp only [genericCut038, Write.AllHold] at hw
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30⟩ := hw
  have h12low := (read32_of_read64_low (s := s) (a := (stack + 0))
    (v := (Operand.mem ((stack + 0)) : Operand 64).read s) rfl).symm.trans h12
  have h13low := (read32_of_read64_low (s := s) (a := (stack + 4))
    (v := (Operand.mem ((stack + 4)) : Operand 64).read s) rfl).symm.trans h13
  have h14low := (read32_of_read64_low (s := s) (a := (stack + 8))
    (v := (Operand.mem ((stack + 8)) : Operand 64).read s) rfl).symm.trans h14
  have h15low := (read32_of_read64_low (s := s) (a := (stack + 12))
    (v := (Operand.mem ((stack + 12)) : Operand 64).read s) rfl).symm.trans h15
  have h16low := (read32_of_read64_low (s := s) (a := (stack + 16))
    (v := (Operand.mem ((stack + 16)) : Operand 64).read s) rfl).symm.trans h16
  have h17low := (read32_of_read64_low (s := s) (a := (stack + 24))
    (v := (Operand.mem ((stack + 24)) : Operand 64).read s) rfl).symm.trans h17
  have h18low := (read32_of_read64_low (s := s) (a := (stack + 32))
    (v := (Operand.mem ((stack + 32)) : Operand 64).read s) rfl).symm.trans h18
  have h19low := (read32_of_read64_low (s := s) (a := (stack + 48))
    (v := (Operand.mem ((stack + 48)) : Operand 64).read s) rfl).symm.trans h19
  have h20low := (read32_of_read64_low (s := s) (a := (stack + 56))
    (v := (Operand.mem ((stack + 56)) : Operand 64).read s) rfl).symm.trans h20
  have h22low := (read32_of_read64_low (s := s) (a := (stack + 72))
    (v := (Operand.mem ((stack + 72)) : Operand 64).read s) rfl).symm.trans h22
  have h23low := (read32_of_read64_low (s := s) (a := (stack + 80))
    (v := (Operand.mem ((stack + 80)) : Operand 64).read s) rfl).symm.trans h23
  have h24low := (read32_of_read64_low (s := s) (a := (stack + 88))
    (v := (Operand.mem ((stack + 88)) : Operand 64).read s) rfl).symm.trans h24
  have h25low := (read32_of_read64_low (s := s) (a := (stack + 96))
    (v := (Operand.mem ((stack + 96)) : Operand 64).read s) rfl).symm.trans h25
  have h26low := (read32_of_read64_low (s := s) (a := (stack + 116))
    (v := (Operand.mem ((stack + 116)) : Operand 64).read s) rfl).symm.trans h26
  have h27low := (read32_of_read64_low (s := s) (a := (stack + 120))
    (v := (Operand.mem ((stack + 120)) : Operand 64).read s) rfl).symm.trans h27
  have h28low := (read32_of_read64_low (s := s) (a := (stack + 124))
    (v := (Operand.mem ((stack + 124)) : Operand 64).read s) rfl).symm.trans h28
  have h29low := (read32_of_read64_low (s := s) (a := (stack + 144))
    (v := (Operand.mem ((stack + 144)) : Operand 64).read s) rfl).symm.trans h29
  have h30low := (read32_of_read64_low (s := s) (a := (stack + 152))
    (v := (Operand.mem ((stack + 152)) : Operand 64).read s) rfl).symm.trans h30
  sha1_norm at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30
  simp only [genericCut039, Write.AllHold, ← ho.read_reg, ← ho.read_mem]
  sha1_norm [effect038, hs, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h12low, h13low, h14low, h15low, h16low, h17low, h18low, h19low, h20low, h22low, h23low, h24low, h25low, h26low, h27low, h28low, h29low, h30low,
    read32_memStore64_low, BitVec.setWidth_add, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, leaSpec]
  rw [hA38, hW37, hW39]
  all_goals sha1_norm [← BitVec.setWidth_eq_extractLsb' (by decide : 32 ≤ 64),
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
  simp_all (config := {implicitDefEqProofs := false, decide := true})
  all_goals repeat' first | (solve | ac_rfl) | apply And.intro

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
theorem effect038_words {stack input : BitVec 64}
    {H : Vector (BitVec 32) 5} {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s) (hw : Write.AllHold s (cut038 stack input H M))
    (he : (effect038 s).Holds s t) : Write.AllHold t (cut039 stack input H M) := by
  let A : Nat → BitVec 32 := fun n ↦ (workingAfter M H n).a
  let W : Fin 80 → BitVec 32 := scheduleWord M
  have hA38 : A 38 = (A 37).rotateLeft 5 + (A 36 ^^^ (A 35).rotateLeft 30 ^^^ (A 34).rotateLeft 30) + (A 33).rotateLeft 30 + 0x6ed9eba1 + W 37 := by
    dsimp [A, W]
    rw [workingAfter_step_a_values M H 33 (by decide +kernel),
      sha1_f_parity_first (by decide +kernel) (by decide +kernel)]
    simp [K, Parity]
  have hW37 : W 37 = (W 34 ^^^ W 29 ^^^ W 23 ^^^ W 21).rotateLeft 1 := by
    dsimp [W]
    change scheduleWord M (⟨37, by decide⟩ : Fin 80) = _
    rw [scheduleWord_recurrence M ⟨37, by decide⟩ (by decide)]
    simp only [Nat.reduceSub]
    rw [sha1Rotl_eq_rotateLeft 1 _ (by decide)]
    rfl
  have hW39 : W 39 = (W 36 ^^^ W 31 ^^^ W 25 ^^^ W 23).rotateLeft 1 := by
    dsimp [W]
    change scheduleWord M (⟨39, by decide⟩ : Fin 80) = _
    rw [scheduleWord_recurrence M ⟨39, by decide⟩ (by decide)]
    simp only [Nat.reduceSub]
    rw [sha1Rotl_eq_rotateLeft 1 _ (by decide)]
    rfl
  have hpre : Write.AllHold s (genericCut038 stack input H A W) := by
    change Write.AllHold s (cut038 stack input H M)
    exact hw
  have hraw := genericWords038 A W hA38 hW37 hW39 hf.stackPointer hpre he
  change Write.AllHold t (cut039 stack input H M)
  exact hraw

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
theorem segment038 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x102d12 0x102d54 cut038 cut039 := by
  have hout : ∀ d : Nat, d ≤ bytes038.length →
      0x102d12 + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    simp only [bytes038, List.length_cons, List.length_nil] at hd
    apply outsideCompression_ne hOutside
    · change 0x1024e0 ≤ (0x102d12 + d % 2^64) % 2^64
      omega
    · change (0x102d12 + d % 2^64) % 2^64 < 0x1036df
      omega
  apply Segment.of_block (fun _ _ _ _ => effect038)
    (fun stack input H M => block038 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64 0x2d12) bytes038,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact effect038_rip he
  · intro stack input H M s t _ hf _ he
    exact effect038_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect038_words hf hw he

theorem segments027_038 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x102a8f 0x102d54 cut027 cut039 := by
  have h0 := segment027 boundary hOutside
  have h1 := h0.seq (segment028 boundary hOutside)
  have h2 := h1.seq (segment029 boundary hOutside)
  have h3 := h2.seq (segment030 boundary hOutside)
  have h4 := h3.seq (segment031 boundary hOutside)
  have h5 := h4.seq (segment032 boundary hOutside)
  have h6 := h5.seq (segment033 boundary hOutside)
  have h7 := h6.seq (segment034 boundary hOutside)
  have h8 := h7.seq (segment035 boundary hOutside)
  have h9 := h8.seq (segment036 boundary hOutside)
  have h10 := h9.seq (segment037 boundary hOutside)
  have h11 := h10.seq (segment038 boundary hOutside)
  exact h11


end Sha1.Proofs.Compress.Machine
