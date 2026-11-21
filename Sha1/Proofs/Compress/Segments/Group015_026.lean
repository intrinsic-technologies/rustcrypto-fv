import Sha1.Proofs.Compress.Machine.Run
import Sha1.Proofs.Compress.Rounds.Scalar
import Sha1.Proofs.Common.Instructions.MovStore.Triple
import X86Proofs.Instructions.Mov.Generated.RM.Triple
import X86Proofs.Instructions.Lea.Generated.RM.Triple
import X86Proofs.Instructions.Bswap.Generated.R.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RM.Triple
import X86Proofs.Instructions.Add.Generated.Imm32.Triple
import X86Proofs.Instructions.Add.Generated.AccImm32.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Or.Generated.RR.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.Xor.Generated.RM.Triple
import X86Proofs.Instructions.Rol.Generated.R.Triple
namespace Sha1.Proofs.Compress.Machine
open Prelude X86 X86.Machine X86.UserProcess X86Proofs Sha1.Spec.Program
open Standards.NIST.SHA1 Sha1.Proofs.Compress.Rounds
attribute [local irreducible] workingAfter scheduleWord messageSchedule

private def genericCut015 (stack input : BitVec 64) (H : Vector (BitVec 32) 5)
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) : List Write :=
  [⟨(.reg 0 : Operand 32), ((A 11)).rotateLeft 30⟩,
    ⟨(.reg 1 : Operand 32), (A 12)⟩,
    ⟨(.reg 2 : Operand 32), (A 13)⟩,
    ⟨(.reg 5 : Operand 32), (W 13)⟩,
    ⟨(.reg 6 : Operand 32), (A 14)⟩,
    ⟨(.reg 7 : Operand 32), ((A 10)).rotateLeft 30⟩,
    ⟨(.reg 12 : Operand 32), (W 2)⟩,
    ⟨(.reg 13 : Operand 32), (W 10)⟩,
    ⟨(.reg 14 : Operand 32), (W 8)⟩,
    ⟨(.reg 15 : Operand 32), (W 0)⟩,
    ⟨(.mem (stack + 0) : Operand 32), (W 9)⟩,
    ⟨(.mem (stack + 4) : Operand 32), (W 5)⟩,
    ⟨(.mem (stack + 8) : Operand 32), (W 4)⟩,
    ⟨(.mem (stack + 16) : Operand 32), (W 13)⟩,
    ⟨(.mem (stack + 24) : Operand 32), (W 10)⟩,
    ⟨(.mem (stack + 32) : Operand 32), (W 6)⟩,
    ⟨(.mem (stack + 40) : Operand 32), (W 7)⟩,
    ⟨(.mem (stack + 56) : Operand 32), (W 3)⟩,
    ⟨(.mem (stack + 64) : Operand 64), input⟩,
    ⟨(.mem (stack + 80) : Operand 32), (W 11)⟩,
    ⟨(.mem (stack + 88) : Operand 32), (W 1)⟩,
    ⟨(.mem (stack + 96) : Operand 32), (W 12)⟩,
    ⟨(.mem (stack + 116) : Operand 32), H[0]⟩,
    ⟨(.mem (stack + 120) : Operand 32), H[3]⟩,
    ⟨(.mem (stack + 124) : Operand 32), H[4]⟩,
    ⟨(.mem (stack + 144) : Operand 32), H[2]⟩,
    ⟨(.mem (stack + 152) : Operand 32), H[1]⟩]

private def genericCut016 (stack input : BitVec 64) (H : Vector (BitVec 32) 5)
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) : List Write :=
  [⟨(.reg 0 : Operand 32), ((A 11)).rotateLeft 30⟩,
    ⟨(.reg 1 : Operand 32), ((A 12)).rotateLeft 30⟩,
    ⟨(.reg 2 : Operand 32), (A 13)⟩,
    ⟨(.reg 5 : Operand 32), (W 13)⟩,
    ⟨(.reg 6 : Operand 32), (A 14)⟩,
    ⟨(.reg 7 : Operand 32), (A 15)⟩,
    ⟨(.reg 11 : Operand 32), (W 14)⟩,
    ⟨(.reg 12 : Operand 32), (W 2)⟩,
    ⟨(.reg 13 : Operand 32), (W 10)⟩,
    ⟨(.reg 14 : Operand 32), (W 8)⟩,
    ⟨(.reg 15 : Operand 32), (W 0)⟩,
    ⟨(.mem (stack + 0) : Operand 32), (W 9)⟩,
    ⟨(.mem (stack + 4) : Operand 32), (W 5)⟩,
    ⟨(.mem (stack + 8) : Operand 32), (W 4)⟩,
    ⟨(.mem (stack + 16) : Operand 32), (W 13)⟩,
    ⟨(.mem (stack + 24) : Operand 32), (W 10)⟩,
    ⟨(.mem (stack + 32) : Operand 32), (W 6)⟩,
    ⟨(.mem (stack + 40) : Operand 32), (W 7)⟩,
    ⟨(.mem (stack + 56) : Operand 32), (W 3)⟩,
    ⟨(.mem (stack + 64) : Operand 64), input⟩,
    ⟨(.mem (stack + 72) : Operand 32), (W 14)⟩,
    ⟨(.mem (stack + 80) : Operand 32), (W 11)⟩,
    ⟨(.mem (stack + 88) : Operand 32), (W 1)⟩,
    ⟨(.mem (stack + 96) : Operand 32), (W 12)⟩,
    ⟨(.mem (stack + 116) : Operand 32), H[0]⟩,
    ⟨(.mem (stack + 120) : Operand 32), H[3]⟩,
    ⟨(.mem (stack + 124) : Operand 32), H[4]⟩,
    ⟨(.mem (stack + 144) : Operand 32), H[2]⟩,
    ⟨(.mem (stack + 152) : Operand 32), H[1]⟩]

private def genericCut017 (stack input : BitVec 64) (H : Vector (BitVec 32) 5)
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) : List Write :=
  [⟨(.reg 1 : Operand 32), ((A 12)).rotateLeft 30⟩,
    ⟨(.reg 2 : Operand 32), ((A 13)).rotateLeft 30⟩,
    ⟨(.reg 3 : Operand 32), (A 16)⟩,
    ⟨(.reg 5 : Operand 32), (W 13)⟩,
    ⟨(.reg 6 : Operand 32), (A 14)⟩,
    ⟨(.reg 7 : Operand 32), (A 15)⟩,
    ⟨(.reg 9 : Operand 32), (W 15)⟩,
    ⟨(.reg 11 : Operand 32), (W 14)⟩,
    ⟨(.reg 12 : Operand 32), (W 2)⟩,
    ⟨(.reg 13 : Operand 32), (W 10)⟩,
    ⟨(.reg 14 : Operand 32), (W 8)⟩,
    ⟨(.reg 15 : Operand 32), (W 0)⟩,
    ⟨(.mem (stack + 0) : Operand 32), (W 9)⟩,
    ⟨(.mem (stack + 4) : Operand 32), (W 5)⟩,
    ⟨(.mem (stack + 8) : Operand 32), (W 4)⟩,
    ⟨(.mem (stack + 16) : Operand 32), (W 13)⟩,
    ⟨(.mem (stack + 24) : Operand 32), (W 10)⟩,
    ⟨(.mem (stack + 32) : Operand 32), (W 6)⟩,
    ⟨(.mem (stack + 40) : Operand 32), (W 7)⟩,
    ⟨(.mem (stack + 48) : Operand 32), (W 15)⟩,
    ⟨(.mem (stack + 56) : Operand 32), (W 3)⟩,
    ⟨(.mem (stack + 64) : Operand 64), input⟩,
    ⟨(.mem (stack + 72) : Operand 32), (W 14)⟩,
    ⟨(.mem (stack + 80) : Operand 32), (W 11)⟩,
    ⟨(.mem (stack + 88) : Operand 32), (W 1)⟩,
    ⟨(.mem (stack + 96) : Operand 32), (W 12)⟩,
    ⟨(.mem (stack + 116) : Operand 32), H[0]⟩,
    ⟨(.mem (stack + 120) : Operand 32), H[3]⟩,
    ⟨(.mem (stack + 124) : Operand 32), H[4]⟩,
    ⟨(.mem (stack + 144) : Operand 32), H[2]⟩,
    ⟨(.mem (stack + 152) : Operand 32), H[1]⟩]

private def genericCut018 (stack input : BitVec 64) (H : Vector (BitVec 32) 5)
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) : List Write :=
  [⟨(.reg 1 : Operand 32), ((A 12)).rotateLeft 30⟩,
    ⟨(.reg 2 : Operand 32), ((A 13)).rotateLeft 30⟩,
    ⟨(.reg 3 : Operand 32), (A 16)⟩,
    ⟨(.reg 5 : Operand 32), (W 3)⟩,
    ⟨(.reg 6 : Operand 32), (A 14)⟩,
    ⟨(.reg 7 : Operand 32), (A 15)⟩,
    ⟨(.reg 10 : Operand 32), (W 4)⟩,
    ⟨(.reg 12 : Operand 32), ((W 0) ^^^ (W 13) ^^^ (W 2) ^^^ (W 8))⟩,
    ⟨(.reg 13 : Operand 32), ((W 10) ^^^ (W 15) ^^^ (W 2) ^^^ (W 4))⟩,
    ⟨(.reg 14 : Operand 32), (W 8)⟩,
    ⟨(.reg 15 : Operand 32), ((W 1) ^^^ (W 14) ^^^ (W 3) ^^^ (W 9))⟩,
    ⟨(.mem (stack + 0) : Operand 32), (W 9)⟩,
    ⟨(.mem (stack + 4) : Operand 32), (W 5)⟩,
    ⟨(.mem (stack + 16) : Operand 32), (W 13)⟩,
    ⟨(.mem (stack + 24) : Operand 32), (W 10)⟩,
    ⟨(.mem (stack + 32) : Operand 32), (W 6)⟩,
    ⟨(.mem (stack + 40) : Operand 32), (W 7)⟩,
    ⟨(.mem (stack + 48) : Operand 32), (W 15)⟩,
    ⟨(.mem (stack + 64) : Operand 64), input⟩,
    ⟨(.mem (stack + 72) : Operand 32), (W 14)⟩,
    ⟨(.mem (stack + 80) : Operand 32), (W 11)⟩,
    ⟨(.mem (stack + 96) : Operand 32), (W 12)⟩,
    ⟨(.mem (stack + 116) : Operand 32), H[0]⟩,
    ⟨(.mem (stack + 120) : Operand 32), H[3]⟩,
    ⟨(.mem (stack + 124) : Operand 32), H[4]⟩,
    ⟨(.mem (stack + 144) : Operand 32), H[2]⟩,
    ⟨(.mem (stack + 152) : Operand 32), H[1]⟩]

private def genericCut019 (stack input : BitVec 64) (H : Vector (BitVec 32) 5)
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) : List Write :=
  [⟨(.reg 1 : Operand 32), (A 17)⟩,
    ⟨(.reg 2 : Operand 32), ((A 13)).rotateLeft 30⟩,
    ⟨(.reg 3 : Operand 32), (A 16)⟩,
    ⟨(.reg 5 : Operand 32), (W 3)⟩,
    ⟨(.reg 6 : Operand 32), ((A 14)).rotateLeft 30⟩,
    ⟨(.reg 7 : Operand 32), (((A 16) &&& ((A 14)).rotateLeft 30) ^^^ ((A 16) &&& ((A 15)).rotateLeft
      30))⟩,
    ⟨(.reg 8 : Operand 32), ((A 15)).rotateLeft 30⟩,
    ⟨(.reg 10 : Operand 32), (W 4)⟩,
    ⟨(.reg 12 : Operand 32), (W 16)⟩,
    ⟨(.reg 13 : Operand 32), ((W 10) ^^^ (W 15) ^^^ (W 2) ^^^ (W 4))⟩,
    ⟨(.reg 14 : Operand 32), (W 8)⟩,
    ⟨(.reg 15 : Operand 32), (W 17)⟩,
    ⟨(.mem (stack + 0) : Operand 32), (W 9)⟩,
    ⟨(.mem (stack + 4) : Operand 32), (W 5)⟩,
    ⟨(.mem (stack + 16) : Operand 32), (W 13)⟩,
    ⟨(.mem (stack + 24) : Operand 32), (W 10)⟩,
    ⟨(.mem (stack + 32) : Operand 32), (W 6)⟩,
    ⟨(.mem (stack + 40) : Operand 32), (W 7)⟩,
    ⟨(.mem (stack + 48) : Operand 32), (W 15)⟩,
    ⟨(.mem (stack + 64) : Operand 64), input⟩,
    ⟨(.mem (stack + 72) : Operand 32), (W 14)⟩,
    ⟨(.mem (stack + 80) : Operand 32), (W 11)⟩,
    ⟨(.mem (stack + 96) : Operand 32), (W 12)⟩,
    ⟨(.mem (stack + 116) : Operand 32), H[0]⟩,
    ⟨(.mem (stack + 120) : Operand 32), H[3]⟩,
    ⟨(.mem (stack + 124) : Operand 32), H[4]⟩,
    ⟨(.mem (stack + 144) : Operand 32), H[2]⟩,
    ⟨(.mem (stack + 152) : Operand 32), H[1]⟩]

private def genericCut020 (stack input : BitVec 64) (H : Vector (BitVec 32) 5)
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) : List Write :=
  [⟨(.reg 1 : Operand 32), (A 17)⟩,
    ⟨(.reg 2 : Operand 32), (A 19)⟩,
    ⟨(.reg 3 : Operand 32), ((A 16)).rotateLeft 30⟩,
    ⟨(.reg 5 : Operand 32), (W 3)⟩,
    ⟨(.reg 7 : Operand 32), (A 18)⟩,
    ⟨(.reg 8 : Operand 32), ((A 15)).rotateLeft 30⟩,
    ⟨(.reg 9 : Operand 32), (W 18)⟩,
    ⟨(.reg 10 : Operand 32), (W 4)⟩,
    ⟨(.reg 12 : Operand 32), (W 16)⟩,
    ⟨(.reg 14 : Operand 32), (W 8)⟩,
    ⟨(.reg 15 : Operand 32), (W 17)⟩,
    ⟨(.mem (stack + 0) : Operand 32), (W 9)⟩,
    ⟨(.mem (stack + 4) : Operand 32), (W 5)⟩,
    ⟨(.mem (stack + 16) : Operand 32), (W 13)⟩,
    ⟨(.mem (stack + 24) : Operand 32), (W 10)⟩,
    ⟨(.mem (stack + 32) : Operand 32), (W 6)⟩,
    ⟨(.mem (stack + 40) : Operand 32), (W 7)⟩,
    ⟨(.mem (stack + 48) : Operand 32), (W 15)⟩,
    ⟨(.mem (stack + 64) : Operand 64), input⟩,
    ⟨(.mem (stack + 72) : Operand 32), (W 14)⟩,
    ⟨(.mem (stack + 80) : Operand 32), (W 11)⟩,
    ⟨(.mem (stack + 96) : Operand 32), (W 12)⟩,
    ⟨(.mem (stack + 116) : Operand 32), H[0]⟩,
    ⟨(.mem (stack + 120) : Operand 32), H[3]⟩,
    ⟨(.mem (stack + 124) : Operand 32), H[4]⟩,
    ⟨(.mem (stack + 144) : Operand 32), H[2]⟩,
    ⟨(.mem (stack + 152) : Operand 32), H[1]⟩]

private def genericCut021 (stack input : BitVec 64) (H : Vector (BitVec 32) 5)
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) : List Write :=
  [⟨(.reg 1 : Operand 32), ((A 17)).rotateLeft 30⟩,
    ⟨(.reg 2 : Operand 32), (A 19)⟩,
    ⟨(.reg 3 : Operand 32), ((A 16)).rotateLeft 30⟩,
    ⟨(.reg 5 : Operand 32), (W 19)⟩,
    ⟨(.reg 6 : Operand 32), ((W 19) + ((A 15)).rotateLeft 30 + (((A 18) &&& ((A 16)).rotateLeft 30)
      ^^^ ((A 18) &&& ((A 17)).rotateLeft 30) ^^^ ((A 16)).rotateLeft 30))⟩,
    ⟨(.reg 7 : Operand 32), ((A 18)).rotateLeft 30⟩,
    ⟨(.reg 8 : Operand 32), (W 6)⟩,
    ⟨(.reg 9 : Operand 32), (W 18)⟩,
    ⟨(.reg 10 : Operand 32), (W 4)⟩,
    ⟨(.reg 12 : Operand 32), (W 16)⟩,
    ⟨(.reg 13 : Operand 32), (W 5)⟩,
    ⟨(.reg 14 : Operand 32), (W 8)⟩,
    ⟨(.reg 15 : Operand 32), (W 17)⟩,
    ⟨(.mem (stack + 0) : Operand 32), (W 9)⟩,
    ⟨(.mem (stack + 16) : Operand 32), (W 13)⟩,
    ⟨(.mem (stack + 24) : Operand 32), (W 10)⟩,
    ⟨(.mem (stack + 40) : Operand 32), (W 7)⟩,
    ⟨(.mem (stack + 48) : Operand 32), (W 15)⟩,
    ⟨(.mem (stack + 56) : Operand 32), (W 19)⟩,
    ⟨(.mem (stack + 64) : Operand 64), input⟩,
    ⟨(.mem (stack + 72) : Operand 32), (W 14)⟩,
    ⟨(.mem (stack + 80) : Operand 32), (W 11)⟩,
    ⟨(.mem (stack + 96) : Operand 32), (W 12)⟩,
    ⟨(.mem (stack + 116) : Operand 32), H[0]⟩,
    ⟨(.mem (stack + 120) : Operand 32), H[3]⟩,
    ⟨(.mem (stack + 124) : Operand 32), H[4]⟩,
    ⟨(.mem (stack + 144) : Operand 32), H[2]⟩,
    ⟨(.mem (stack + 152) : Operand 32), H[1]⟩]

private def genericCut022 (stack input : BitVec 64) (H : Vector (BitVec 32) 5)
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) : List Write :=
  [⟨(.reg 1 : Operand 32), ((A 17)).rotateLeft 30⟩,
    ⟨(.reg 2 : Operand 32), (A 20)⟩,
    ⟨(.reg 3 : Operand 32), ((A 16)).rotateLeft 30⟩,
    ⟨(.reg 5 : Operand 32), (((A 18)).rotateLeft 30 ^^^ ((A 19)).rotateLeft 30)⟩,
    ⟨(.reg 7 : Operand 32), ((A 19) ^^^ ((A 17)).rotateLeft 30 ^^^ ((A 18)).rotateLeft 30)⟩,
    ⟨(.reg 8 : Operand 32), ((A 19)).rotateLeft 30⟩,
    ⟨(.reg 9 : Operand 32), (W 18)⟩,
    ⟨(.reg 10 : Operand 32), ((W 4) ^^^ (W 6))⟩,
    ⟨(.reg 12 : Operand 32), (W 16)⟩,
    ⟨(.reg 13 : Operand 32), (W 5)⟩,
    ⟨(.reg 14 : Operand 32), (W 8)⟩,
    ⟨(.reg 15 : Operand 32), (W 17)⟩,
    ⟨(.mem (stack + 0) : Operand 32), (W 9)⟩,
    ⟨(.mem (stack + 12) : Operand 32), ((W 22) + ((A 18)).rotateLeft 30)⟩,
    ⟨(.mem (stack + 16) : Operand 32), (W 13)⟩,
    ⟨(.mem (stack + 24) : Operand 32), (W 10)⟩,
    ⟨(.mem (stack + 32) : Operand 32), (W 22)⟩,
    ⟨(.mem (stack + 40) : Operand 32), (W 7)⟩,
    ⟨(.mem (stack + 48) : Operand 32), (W 15)⟩,
    ⟨(.mem (stack + 56) : Operand 32), (W 19)⟩,
    ⟨(.mem (stack + 64) : Operand 64), input⟩,
    ⟨(.mem (stack + 72) : Operand 32), (W 14)⟩,
    ⟨(.mem (stack + 80) : Operand 32), (W 11)⟩,
    ⟨(.mem (stack + 96) : Operand 32), (W 12)⟩,
    ⟨(.mem (stack + 116) : Operand 32), H[0]⟩,
    ⟨(.mem (stack + 120) : Operand 32), H[3]⟩,
    ⟨(.mem (stack + 124) : Operand 32), H[4]⟩,
    ⟨(.mem (stack + 144) : Operand 32), H[2]⟩,
    ⟨(.mem (stack + 152) : Operand 32), H[1]⟩]

private def genericCut023 (stack input : BitVec 64) (H : Vector (BitVec 32) 5)
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) : List Write :=
  [⟨(.reg 0 : Operand 32), (A 21)⟩,
    ⟨(.reg 1 : Operand 32), ((A 17)).rotateLeft 30⟩,
    ⟨(.reg 2 : Operand 32), (A 20)⟩,
    ⟨(.reg 3 : Operand 32), (W 13)⟩,
    ⟨(.reg 5 : Operand 32), (((A 18)).rotateLeft 30 ^^^ ((A 19)).rotateLeft 30)⟩,
    ⟨(.reg 7 : Operand 32), (W 7)⟩,
    ⟨(.reg 8 : Operand 32), ((A 19)).rotateLeft 30⟩,
    ⟨(.reg 9 : Operand 32), (W 18)⟩,
    ⟨(.reg 10 : Operand 32), (W 20)⟩,
    ⟨(.reg 11 : Operand 32), (W 12)⟩,
    ⟨(.reg 12 : Operand 32), (W 16)⟩,
    ⟨(.reg 13 : Operand 32), ((W 5) ^^^ (W 7))⟩,
    ⟨(.reg 14 : Operand 32), (W 8)⟩,
    ⟨(.reg 15 : Operand 32), (W 17)⟩,
    ⟨(.mem (stack + 0) : Operand 32), (W 9)⟩,
    ⟨(.mem (stack + 8) : Operand 32), (W 20)⟩,
    ⟨(.mem (stack + 12) : Operand 32), ((W 22) + ((A 18)).rotateLeft 30)⟩,
    ⟨(.mem (stack + 16) : Operand 32), (W 13)⟩,
    ⟨(.mem (stack + 24) : Operand 32), (W 10)⟩,
    ⟨(.mem (stack + 32) : Operand 32), (W 22)⟩,
    ⟨(.mem (stack + 48) : Operand 32), (W 15)⟩,
    ⟨(.mem (stack + 56) : Operand 32), (W 19)⟩,
    ⟨(.mem (stack + 64) : Operand 64), input⟩,
    ⟨(.mem (stack + 72) : Operand 32), (W 14)⟩,
    ⟨(.mem (stack + 80) : Operand 32), (W 11)⟩,
    ⟨(.mem (stack + 96) : Operand 32), (W 12)⟩,
    ⟨(.mem (stack + 116) : Operand 32), H[0]⟩,
    ⟨(.mem (stack + 120) : Operand 32), H[3]⟩,
    ⟨(.mem (stack + 124) : Operand 32), H[4]⟩,
    ⟨(.mem (stack + 144) : Operand 32), H[2]⟩,
    ⟨(.mem (stack + 152) : Operand 32), H[1]⟩]

private def genericCut024 (stack input : BitVec 64) (H : Vector (BitVec 32) 5)
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) : List Write :=
  [⟨(.reg 0 : Operand 32), (A 21)⟩,
    ⟨(.reg 1 : Operand 32), (A 22)⟩,
    ⟨(.reg 2 : Operand 32), ((A 20)).rotateLeft 30⟩,
    ⟨(.reg 3 : Operand 32), (W 13)⟩,
    ⟨(.reg 8 : Operand 32), ((A 19)).rotateLeft 30⟩,
    ⟨(.reg 9 : Operand 32), (W 18)⟩,
    ⟨(.reg 10 : Operand 32), (W 23)⟩,
    ⟨(.reg 11 : Operand 32), (W 12)⟩,
    ⟨(.reg 12 : Operand 32), (W 16)⟩,
    ⟨(.reg 13 : Operand 32), (W 21)⟩,
    ⟨(.reg 14 : Operand 32), (W 8)⟩,
    ⟨(.reg 15 : Operand 32), (W 17)⟩,
    ⟨(.mem (stack + 0) : Operand 32), (W 9)⟩,
    ⟨(.mem (stack + 4) : Operand 32), (W 21)⟩,
    ⟨(.mem (stack + 8) : Operand 32), (W 20)⟩,
    ⟨(.mem (stack + 12) : Operand 32), ((W 22) + ((A 18)).rotateLeft 30)⟩,
    ⟨(.mem (stack + 16) : Operand 32), (W 13)⟩,
    ⟨(.mem (stack + 24) : Operand 32), (W 10)⟩,
    ⟨(.mem (stack + 32) : Operand 32), (W 22)⟩,
    ⟨(.mem (stack + 48) : Operand 32), (W 15)⟩,
    ⟨(.mem (stack + 56) : Operand 32), (W 19)⟩,
    ⟨(.mem (stack + 64) : Operand 64), input⟩,
    ⟨(.mem (stack + 72) : Operand 32), (W 14)⟩,
    ⟨(.mem (stack + 80) : Operand 32), (W 11)⟩,
    ⟨(.mem (stack + 88) : Operand 32), (W 18)⟩,
    ⟨(.mem (stack + 96) : Operand 32), (W 12)⟩,
    ⟨(.mem (stack + 116) : Operand 32), H[0]⟩,
    ⟨(.mem (stack + 120) : Operand 32), H[3]⟩,
    ⟨(.mem (stack + 124) : Operand 32), H[4]⟩,
    ⟨(.mem (stack + 144) : Operand 32), H[2]⟩,
    ⟨(.mem (stack + 152) : Operand 32), H[1]⟩]

private def genericCut025 (stack input : BitVec 64) (H : Vector (BitVec 32) 5)
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) : List Write :=
  [⟨(.reg 0 : Operand 32), ((A 21)).rotateLeft 30⟩,
    ⟨(.reg 1 : Operand 32), ((A 22)).rotateLeft 30⟩,
    ⟨(.reg 2 : Operand 32), ((A 20)).rotateLeft 30⟩,
    ⟨(.reg 3 : Operand 32), (W 13)⟩,
    ⟨(.reg 6 : Operand 32), (A 23)⟩,
    ⟨(.reg 7 : Operand 32), (W 10)⟩,
    ⟨(.reg 8 : Operand 32), ((W 23) + ((A 19)).rotateLeft 30 + ((A 22) ^^^ ((A 20)).rotateLeft 30
      ^^^ ((A 21)).rotateLeft 30))⟩,
    ⟨(.reg 9 : Operand 32), (W 18)⟩,
    ⟨(.reg 10 : Operand 32), (W 23)⟩,
    ⟨(.reg 11 : Operand 32), (W 12)⟩,
    ⟨(.reg 12 : Operand 32), (W 16)⟩,
    ⟨(.reg 13 : Operand 32), (W 21)⟩,
    ⟨(.reg 14 : Operand 32), (W 8)⟩,
    ⟨(.reg 15 : Operand 32), (W 17)⟩,
    ⟨(.mem (stack + 0) : Operand 32), (W 9)⟩,
    ⟨(.mem (stack + 4) : Operand 32), (W 21)⟩,
    ⟨(.mem (stack + 8) : Operand 32), (W 20)⟩,
    ⟨(.mem (stack + 16) : Operand 32), (W 13)⟩,
    ⟨(.mem (stack + 32) : Operand 32), (W 22)⟩,
    ⟨(.mem (stack + 40) : Operand 32), (W 23)⟩,
    ⟨(.mem (stack + 48) : Operand 32), (W 15)⟩,
    ⟨(.mem (stack + 56) : Operand 32), (W 19)⟩,
    ⟨(.mem (stack + 64) : Operand 64), input⟩,
    ⟨(.mem (stack + 72) : Operand 32), (W 14)⟩,
    ⟨(.mem (stack + 80) : Operand 32), (W 11)⟩,
    ⟨(.mem (stack + 88) : Operand 32), (W 18)⟩,
    ⟨(.mem (stack + 96) : Operand 32), (W 12)⟩,
    ⟨(.mem (stack + 116) : Operand 32), H[0]⟩,
    ⟨(.mem (stack + 120) : Operand 32), H[3]⟩,
    ⟨(.mem (stack + 124) : Operand 32), H[4]⟩,
    ⟨(.mem (stack + 144) : Operand 32), H[2]⟩,
    ⟨(.mem (stack + 152) : Operand 32), H[1]⟩]

private def genericCut026 (stack input : BitVec 64) (H : Vector (BitVec 32) 5)
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) : List Write :=
  [⟨(.reg 0 : Operand 32), ((A 21)).rotateLeft 30⟩,
    ⟨(.reg 1 : Operand 32), ((A 23) ^^^ ((A 21)).rotateLeft 30 ^^^ ((A 22)).rotateLeft 30)⟩,
    ⟨(.reg 2 : Operand 32), ((A 20)).rotateLeft 30⟩,
    ⟨(.reg 3 : Operand 32), (W 13)⟩,
    ⟨(.reg 5 : Operand 32), (((A 22)).rotateLeft 30 ^^^ ((A 23)).rotateLeft 30)⟩,
    ⟨(.reg 6 : Operand 32), (A 24)⟩,
    ⟨(.reg 7 : Operand 32), ((A 23)).rotateLeft 30⟩,
    ⟨(.reg 9 : Operand 32), ((W 26) + ((A 22)).rotateLeft 30)⟩,
    ⟨(.reg 12 : Operand 32), (W 16)⟩,
    ⟨(.reg 13 : Operand 32), (W 21)⟩,
    ⟨(.reg 14 : Operand 32), ((W 10) ^^^ (W 8))⟩,
    ⟨(.reg 15 : Operand 32), (W 17)⟩,
    ⟨(.mem (stack + 0) : Operand 32), (W 9)⟩,
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
    ⟨(.mem (stack + 80) : Operand 32), (W 11)⟩,
    ⟨(.mem (stack + 88) : Operand 32), (W 18)⟩,
    ⟨(.mem (stack + 96) : Operand 32), (W 12)⟩,
    ⟨(.mem (stack + 116) : Operand 32), H[0]⟩,
    ⟨(.mem (stack + 120) : Operand 32), H[3]⟩,
    ⟨(.mem (stack + 124) : Operand 32), H[4]⟩,
    ⟨(.mem (stack + 144) : Operand 32), H[2]⟩,
    ⟨(.mem (stack + 152) : Operand 32), H[1]⟩]

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

def bytes015 : List UInt8 :=
  [0x4c, 0x8b, 0x44, 0x24, 0x40, 0x45, 0x8b, 0x58, 0x38, 0x41, 0x0f, 0xcb, 0xc1, 0xc1, 0x1e, 0x44,
    0x01, 0xdf, 0x4c, 0x89, 0x5c, 0x24, 0x48, 0x41, 0x89, 0xf0, 0x41, 0xc1, 0xc0, 0x05, 0x41, 0x89,
    0xca, 0x41, 0x31, 0xc2, 0x41, 0x21, 0xd2, 0x41, 0x31, 0xc2, 0x41, 0x01, 0xfa, 0x43, 0x8d, 0x3c,
    0x10, 0x81, 0xc7, 0x99, 0x79, 0x82, 0x5a]

set_option maxHeartbeats 800000 in
def effect015 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq ((movR64M64Effect
    0x1027f8 8 (.sib 4 none 0 (.d8 0x40)))) (movR32M32Effect 0x1027fd 11 (.base 8 (.d8 0x38))))
    (bswapR32Effect 0x102801 3 11)) (rolR32Effect 0x102804 3 1 30)) (addR32R32Effect 0x102807 3 7
    11)) (movM64R64Effect 0x10280a 11 (.sib 4 none 0 (.d8 0x48)))) (movR32R32Effect 0x10280f 3 8 6))
    (rolR32Effect 0x102812 4 8 5)) (movR32R32Effect 0x102816 3 10 1)) (xorR32R32Effect 0x102819 3 10
    0)) (andR32R32Effect 0x10281c 3 10 2)) (xorR32R32Effect 0x10281f 3 10 0)) (addR32R32Effect
    0x102822 3 10 7)) (leaR32Effect 0x102825 4 7 (.sib 8 (some 10) 0 .none))) (addR32Imm32Effect
    0x102829 6 7 0x5a827999)

set_option maxHeartbeats 800000 in
theorem block015 [Bindings] (boundary : ReturnBoundary) (stack input : BitVec 64)
    (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes015.length →
      0x1027f8 + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x1027f8 ∧ FrameData stack input M s ∧
        Write.AllHold s (cut015 stack input H M))
      (codeRange 0x1027f8 bytes015) effect015 := by
  unfold bytes015 at hout ⊢
  sha1_run_begin (mov_r64_m64_effect_step 0x1027f8 0x4c (by unfold RexWPrefix; decide +kernel) 0
    (.sib 4 none 0 (.d8 0x40)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_m32_effect_step 0x1027fd 0x45 (by unfold RexNoWPrefix; decide +kernel) 3
    (.base 8 (.d8 0x38)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (bswap_r32_rex_effect_step 0x102801 0x41 (by unfold RexNoWPrefix; decide +kernel)
    0xcb (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x102804 0xc1 0x1e (by decide +kernel)
    (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x102807 0x44 0xdf
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m64_r64_effect_step 0x10280a 0x4c
    (by unfold RexWPrefix; decide +kernel) 3 (.sib 4 none 0 (.d8 0x48)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x10280f 0x41 0xf0
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_imm8_rex_effect_step 0x102812 0x41 0xc0 0x5
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x102816 0x41 0xca
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102819 0x41 0xc2
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (and_r32_r32_rex_effect_step 0x10281c 0x41 0xd2
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x10281f 0x41 0xc2
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x102822 0x41 0xfa
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (lea_r32_rex_effect_step 0x102825 0x43 (by unfold RexNoWPrefix; decide +kernel) 7
    (.sib 8 (some 10) 0 .none) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_imm32_effect_step 0x102829 0xc7 0x5a827999 (by decide +kernel)
    (by decide +kernel))
  sha1_run_finish [effect015]

theorem effect015_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s)
    (he : (effect015 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have hfoot : ∀ c ∈ (effect015 s).components, c ∈ [.mem ((Operand.reg 4 : Operand 64).read s +
    BitVec.ofNat 64 72) 8, .reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9,
    .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] := by
    unfold effect015
    iterate 14 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [leaR32Effect_components, bswapR32Effect_components, addR32Imm32Effect_components,
        addR32R32Effect_components, andR32R32Effect_components, movM64R64Effect_components,
        movR32M32Effect_components, movR32R32Effect_components, movR64M64Effect_components,
        rolR32Effect_components, xorR32R32Effect_components, List.mem_cons, List.not_mem_nil,
        or_false, or_imp, forall_and, forall_eq, or_true]
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only [x86_compose]
  have ha := he.agrees.mono hfoot
  rw [hs] at ha
  apply ha.widen
  · intro c hc hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl
    all_goals simp_all (config := {decide := true, implicitDefEqProofs := false}) only
      [Component.isMem, scratchComponents, x86_compose]
  · intro address c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl
    all_goals first
      | exact hCov.elim
      | exact scratchComponents_stack (Or.inl (by decide +kernel)) hCov

theorem effect015_rip {s t : RamState}
    (he : (effect015 s).Holds s t) :
    t.RIP = 0x10282f := by
  exact he.rip.trans (by rfl)

set_option maxHeartbeats 800000 in
private theorem rawR1_015 {s t : RamState}
    (v : BitVec 32)
    (hv : (Operand.reg 1 : Operand 32).read s = v)
    (he : (effect015 s).Holds s t) :
    (Operand.reg 1 : Operand 32).read t = v.rotateLeft 30 := by
  have hfull : ∀ w ∈ (effect015 s).writes, w.Full := by
    apply Effect.Local.full
    unfold effect015
    repeat' first | (solve | x86_local) | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  sha1_norm at hv
  simp only [← ho.read_reg]
  sha1_norm [effect015, hv, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]

set_option maxHeartbeats 800000 in
private theorem rawR11_015 {s t : RamState}
    (stack input : BitVec 64) (w : BitVec 32)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (hp : (Operand.mem (stack + 64) : Operand 64).read s = input)
    (hw : (Operand.mem (input + 56) : Operand 32).read s = bswapSpec w)
    (he : (effect015 s).Holds s t) :
    (Operand.reg 11 : Operand 32).read t = w := by
  have hfull : ∀ w ∈ (effect015 s).writes, w.Full := by
    apply Effect.Local.full
    unfold effect015
    repeat' first | (solve | x86_local) | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  sha1_norm at hs hp hw
  simp only [← ho.read_reg]
  sha1_norm [effect015, hs, hp, hw, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
  simp (config := {decide := true, implicitDefEqProofs := false}) only [bswap32_bswap32]

set_option maxHeartbeats 800000 in
private theorem rawM72_015 {s t : RamState}
    (stack input : BitVec 64) (w : BitVec 32)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (hp : (Operand.mem (stack + 64) : Operand 64).read s = input)
    (hw : (Operand.mem (input + 56) : Operand 32).read s = bswapSpec w)
    (he : (effect015 s).Holds s t) :
    (Operand.mem (stack + 72) : Operand 32).read t = w := by
  have hfull : ∀ w ∈ (effect015 s).writes, w.Full := by
    apply Effect.Local.full
    unfold effect015
    repeat' first | (solve | x86_local) | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  sha1_norm at hs hp hw
  simp only [← ho.read_mem]
  sha1_norm [effect015, hs, hp, hw, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
  rw [read32_memStore64_low]
  simp (config := {decide := true, implicitDefEqProofs := false}) only [bswap32_bswap32,
    extractLsb'_zero_eq_setWidth, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]

set_option maxHeartbeats 800000 in
private theorem rawR7_015 {s t : RamState}
    (stack input : BitVec 64) (v0 v1 v2 v6 v7 w : BitVec 32)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (hp : (Operand.mem (stack + 64) : Operand 64).read s = input)
    (hw : (Operand.mem (input + 56) : Operand 32).read s = bswapSpec w)
    (h0 : (Operand.reg 0 : Operand 32).read s = v0)
    (h1 : (Operand.reg 1 : Operand 32).read s = v1)
    (h2 : (Operand.reg 2 : Operand 32).read s = v2)
    (h6 : (Operand.reg 6 : Operand 32).read s = v6)
    (h7 : (Operand.reg 7 : Operand 32).read s = v7)
    (he : (effect015 s).Holds s t) :
    (Operand.reg 7 : Operand 32).read t =
      v6.rotateLeft 5 + ((v1.rotateLeft 30 ^^^ v0) &&& v2 ^^^ v0) +
      v7 + 0x5a827999 + w := by
  have hfull : ∀ w ∈ (effect015 s).writes, w.Full := by
    apply Effect.Local.full
    unfold effect015
    repeat' first | (solve | x86_local) | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  sha1_norm at hs hp hw h0 h1 h2 h6 h7
  simp only [← ho.read_reg]
  sha1_norm [effect015, hs, hp, hw, h0, h1, h2, h6, h7, BitVec.setWidth_setWidth_of_le,
    BitVec.setWidth_eq]
  simp (config := {decide := true, implicitDefEqProofs := false}) only [bswap32_bswap32,
    BitVec.shiftLeft_zero, BitVec.add_zero]
  try simp (config := {decide := true}) only [leaSpec, BitVec.setWidth_add,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
  all_goals try sha1_norm [leaSpec, BitVec.setWidth_add, BitVec.setWidth_setWidth_of_le,
    BitVec.setWidth_eq]
  all_goals ac_rfl

set_option maxHeartbeats 800000 in
private theorem genericWords015 {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) {s t : RamState}
    (hWork : A 15 = (A 14).rotateLeft 5 +
      (((A 12).rotateLeft 30 ^^^ (A 11).rotateLeft 30) &&& A 13 ^^^ (A 11).rotateLeft 30) +
      (A 10).rotateLeft 30 + 0x5a827999 + W 14)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (hInput14 : (Operand.mem (input + 56) : Operand 32).read s = bswapSpec (W 14))
    (hw : Write.AllHold s (genericCut015 stack input H A W))
    (he : (effect015 s).Holds s t) :
    Write.AllHold t (genericCut016 stack input H A W) := by
  simp only [genericCut015, Write.AllHold] at hw
  obtain ⟨h0,h1,h2,h5,h6,h7,h12,h13,h14,h15,
    hM0,hM4,hM8,hM16,hM24,hM32,hM40,hM56,hM64,hM80,hM88,hM96,
    hM116,hM120,hM124,hM144,hM152⟩ := hw
  have hR1 := rawR1_015 (A 12) h1 he
  have hR11 := rawR11_015 stack input (W 14) hs hM64 hInput14 he
  have hM72 := rawM72_015 stack input (W 14) hs hM64 hInput14 he
  have hR7 := (rawR7_015 stack input ((A 11).rotateLeft 30) (A 12) (A 13)
    (A 14) ((A 10).rotateLeft 30) (W 14) hs hM64 hInput14 h0 h1 h2 h6 h7 he).trans hWork.symm
  have hfoot : ∀ c ∈ (effect015 s).components,
      c ∈ [.mem ((Operand.reg 4 : Operand 64).read s + 72) 8,
        .reg 1, .reg 7, .reg 8, .reg 10, .reg 11, .flags, .rip] := by
    unfold effect015
    iterate 14 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [leaR32Effect_components,
       bswapR32Effect_components,
       addR32Imm32Effect_components, addR32R32Effect_components,
       andR32R32Effect_components, movM64R64Effect_components,
       movR32M32Effect_components, movR32R32Effect_components,
       movR64M64Effect_components, rolR32Effect_components, xorR32R32Effect_components,
       List.mem_cons, List.not_mem_nil, or_false, or_imp, forall_and, forall_eq, or_true]
    all_goals sha1_norm
  have ha := he.agrees.mono hfoot
  rw [hs] at ha
  have hmem {n : Nat} (off : BitVec 64) (hb : OffsetsApart 72 8 off (n / 8))
      (hsize : 8 + n / 8 < 2 ^ 64) :
      (Operand.mem (stack + off) : Operand n).read t =
      (Operand.mem (stack + off) : Operand n).read s := by
    apply memLoad_congr
    intro i hi
    apply congrArg (fun b : Option UInt8 ↦ b.getD 0)
    apply ha.byte
    intro c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨j,hj,heq⟩ := hCov
      exact hb.ne stack hj hi hsize heq.symm
    all_goals exact hCov.elim
  simp only [genericCut016, Write.AllHold]
  refine ⟨?f0, ?f1, ?f2, ?f3, ?f4, ?f5, ?f6, ?f7, ?f8, ?f9, ?f10, ?f11, ?f12, ?f13, ?f14, ?f15,
    ?f16, ?f17, ?f18, ?f19, ?f20, ?f21, ?f22, ?f23, ?f24, ?f25, ?f26, ?f27, ?f28⟩
  case f0 =>
    exact (ha.read (by simp)).trans h0
  case f1 =>
    exact hR1
  case f2 =>
    exact (ha.read (by simp)).trans h2
  case f3 =>
    exact (ha.read (by simp)).trans h5
  case f4 =>
    exact (ha.read (by simp)).trans h6
  case f5 =>
    exact hR7
  case f6 =>
    exact hR11
  case f7 =>
    exact (ha.read (by simp)).trans h12
  case f8 =>
    exact (ha.read (by simp)).trans h13
  case f9 =>
    exact (ha.read (by simp)).trans h14
  case f10 =>
    exact (ha.read (by simp)).trans h15
  case f11 =>
    exact (hmem 0 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM0
  case f12 =>
    exact (hmem 4 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM4
  case f13 =>
    exact (hmem 8 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans hM8
  case f14 =>
    exact (hmem 16 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans
      hM16
  case f15 =>
    exact (hmem 24 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans
      hM24
  case f16 =>
    exact (hmem 32 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans
      hM32
  case f17 =>
    exact (hmem 40 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans
      hM40
  case f18 =>
    exact (hmem 56 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans
      hM56
  case f19 =>
    exact (hmem 64 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans
      hM64
  case f20 =>
    exact hM72
  case f21 =>
    exact (hmem 80 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans
      hM80
  case f22 =>
    exact (hmem 88 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans
      hM88
  case f23 =>
    exact (hmem 96 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans
      hM96
  case f24 =>
    exact (hmem 116 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans
      hM116
  case f25 =>
    exact (hmem 120 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans
      hM120
  case f26 =>
    exact (hmem 124 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans
      hM124
  case f27 =>
    exact (hmem 144 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans
      hM144
  case f28 =>
    exact (hmem 152 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)).trans
      hM152

theorem effect015_words {stack input : BitVec 64}
    {H : Vector (BitVec 32) 5} {M : Vector (BitVec 32) 16}
    {s t : RamState}
    (hf : FrameData stack input M s)
    (hw : Write.AllHold s (cut015 stack input H M))
    (he : (effect015 s).Holds s t) :
    Write.AllHold t (cut016 stack input H M) := by
  have hCh (x y z : BitVec 32) :
      Standards.NIST.SHA2.SHA256.Ch x y z = (y ^^^ z) &&& x ^^^ z := by
    rw [sha1Ch_eq, BitVec.and_comm x (y ^^^ z), BitVec.xor_comm]
  have hWork := workingAfter_step_a_values M H 10 (by decide +kernel)
  rw [sha1_f_choice (t := ⟨14, by decide⟩) (by decide)] at hWork
  simp only [Nat.reduceAdd] at hWork
  rw [show K (⟨14, by decide⟩ : Fin 80) = 0x5a827999 by decide, hCh] at hWork
  have hInput14 := hf.words (⟨14, by decide⟩ : Fin 16)
  have hW14 : scheduleWord M ⟨14, by decide⟩ = M[(⟨14, by decide⟩ : Fin 16)] := by
    rw [scheduleWord_initial M ⟨14, by decide⟩ (by decide)]
    rfl
  rw [← hW14] at hInput14
  exact genericWords015 (fun n ↦ (workingAfter M H n).a) (scheduleWord M)
    hWork hf.stackPointer hInput14 hw he

theorem segment015 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x1027f8 0x10282f
      cut015 cut016 := by
  apply Segment.of_block (fun _ _ _ _ ↦ effect015)
    (fun stack input H M ↦ block015 boundary stack input H M (by
      intro d hd
      apply outsideCompression_ne hOutside <;>
        simp only [bytes015, List.length_cons, List.length_nil] at hd
      all_goals simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat]
      all_goals omega))
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64
      0x27f8) bytes015,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact effect015_rip he
  · intro stack input H M s t _ hf _ he
    exact effect015_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect015_words hf hw he

def bytes016 : List UInt8 :=
  [0x4c, 0x8b, 0x44, 0x24, 0x40, 0x45, 0x8b, 0x48, 0x3c, 0x41, 0x0f, 0xc9, 0x44, 0x01, 0xc8, 0x4c,
    0x89, 0x4c, 0x24, 0x30, 0xc1, 0xc2, 0x1e, 0x41, 0x89, 0xd0, 0x41, 0x31, 0xc8, 0x41, 0x21, 0xf0,
    0x41, 0x31, 0xc8, 0x41, 0x01, 0xc0, 0x89, 0xf8, 0xc1, 0xc0, 0x05, 0x42, 0x8d, 0x1c, 0x00, 0x81,
    0xc3, 0x99, 0x79, 0x82, 0x5a]

set_option maxHeartbeats 800000 in
def effect016 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq ((movR64M64Effect
    0x10282f 8 (.sib 4 none 0 (.d8 0x40)))) (movR32M32Effect 0x102834 9 (.base 8 (.d8 0x3c))))
    (bswapR32Effect 0x102838 3 9)) (addR32R32Effect 0x10283b 3 0 9)) (movM64R64Effect 0x10283e 9
    (.sib 4 none 0 (.d8 0x30)))) (rolR32Effect 0x102843 3 2 30)) (movR32R32Effect 0x102846 3 8 2))
    (xorR32R32Effect 0x102849 3 8 1)) (andR32R32Effect 0x10284c 3 8 6)) (xorR32R32Effect 0x10284f 3
    8 1)) (addR32R32Effect 0x102852 3 8 0)) (movR32R32Effect 0x102855 2 0 7)) (rolR32Effect 0x102857
    3 0 5)) (leaR32Effect 0x10285a 4 3 (.sib 0 (some 8) 0 .none))) (addR32Imm32Effect 0x10285e 6 3
    0x5a827999)

set_option maxHeartbeats 800000 in
theorem block016 [Bindings] (boundary : ReturnBoundary) (stack input : BitVec 64)
    (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes016.length →
      0x10282f + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x10282f ∧ FrameData stack input M s ∧
        Write.AllHold s (cut016 stack input H M))
      (codeRange 0x10282f bytes016) effect016 := by
  unfold bytes016 at hout ⊢
  sha1_run_begin (mov_r64_m64_effect_step 0x10282f 0x4c (by unfold RexWPrefix; decide +kernel) 0
    (.sib 4 none 0 (.d8 0x40)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_m32_effect_step 0x102834 0x45 (by unfold RexNoWPrefix; decide +kernel) 1
    (.base 8 (.d8 0x3c)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (bswap_r32_rex_effect_step 0x102838 0x41 (by unfold RexNoWPrefix; decide +kernel)
    0xc9 (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x10283b 0x44 0xc8
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m64_r64_effect_step 0x10283e 0x4c
    (by unfold RexWPrefix; decide +kernel) 1 (.sib 4 none 0 (.d8 0x30)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x102843 0xc2 0x1e (by decide +kernel)
    (by decide +kernel))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x102846 0x41 0xd0
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102849 0x41 0xc8
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (and_r32_r32_rex_effect_step 0x10284c 0x41 0xf0
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x10284f 0x41 0xc8
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x102852 0x41 0xc0
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_effect_step 0x102855 0xf8 (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x102857 0xc0 0x5 (by decide +kernel) (by decide +kernel))
  sha1_run_then (lea_r32_rex_effect_step 0x10285a 0x42 (by unfold RexNoWPrefix; decide +kernel) 3
    (.sib 0 (some 8) 0 .none) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_imm32_effect_step 0x10285e 0xc3 0x5a827999 (by decide +kernel)
    (by decide +kernel))
  sha1_run_finish [effect016]

theorem effect016_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s)
    (he : (effect016 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have hfoot : ∀ c ∈ (effect016 s).components, c ∈ [.mem ((Operand.reg 4 : Operand 64).read s +
    BitVec.ofNat 64 48) 8, .reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9,
    .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] := by
    unfold effect016
    iterate 14 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [leaR32Effect_components, bswapR32Effect_components, addR32Imm32Effect_components,
        addR32R32Effect_components, andR32R32Effect_components, movM64R64Effect_components,
        movR32M32Effect_components, movR32R32Effect_components, movR64M64Effect_components,
        rolR32Effect_components, xorR32R32Effect_components, List.mem_cons, List.not_mem_nil,
        or_false, or_imp, forall_and, forall_eq, or_true]
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only [x86_compose]
  have ha := he.agrees.mono hfoot
  rw [hs] at ha
  apply ha.widen
  · intro c hc hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl
    all_goals simp_all (config := {decide := true, implicitDefEqProofs := false}) only
      [Component.isMem, scratchComponents, x86_compose]
  · intro address c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl
    all_goals first
      | exact hCov.elim
      | exact scratchComponents_stack (Or.inl (by decide +kernel)) hCov

theorem effect016_rip {s t : RamState}
    (he : (effect016 s).Holds s t) :
    t.RIP = 0x102864 := by
  exact he.rip.trans (by rfl)

section Words016
set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem genericWords016 {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) {s t : RamState}
    (hWork : A 16 = (A 15).rotateLeft 5 +
      Standards.NIST.SHA2.SHA256.Ch (A 14) ((A 13).rotateLeft 30)
        ((A 12).rotateLeft 30) + (A 11).rotateLeft 30 +
        0x5a827999 + W ⟨15, by decide⟩)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (hInput15 : (Operand.mem (input + BitVec.ofNat 64 60) : Operand 32).read s =
      bswapSpec (W ⟨15, by decide⟩))
    (hw : Write.AllHold s (genericCut016 stack input H A W))
    (he : (effect016 s).Holds s t) :
    Write.AllHold t (genericCut017 stack input H A W) := by
  have hfull : ∀ wr ∈ (effect016 s).writes, wr.Full := by
    apply Effect.Local.full
    unfold effect016
    repeat' first | (solve | x86_local) | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  have hfoot : ∀ c ∈ (effect016 s).components,
      c ∈ [.mem ((Operand.reg 4 : Operand 64).read s + 48) 8,
        .reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7,
        .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15,
        .flags, .rip] := by
    unfold effect016
    iterate 14 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [leaR32Effect_components,
       bswapR32Effect_components,
       addR32Imm32Effect_components, addR32R32Effect_components,
       andR32R32Effect_components, movM64R64Effect_components,
       movR32M32Effect_components, movR32R32Effect_components,
       movR64M64Effect_components, rolR32Effect_components,
       xorR32R32Effect_components, List.mem_cons, List.not_mem_nil, or_false,
       or_imp, forall_and, forall_eq, or_true]
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [x86_compose]
  have ha := he.agrees.mono hfoot
  rw [hs] at ha
  have hmem {n : Nat} (off : BitVec 64)
      (hb : OffsetsApart 48 8 off (n / 8)) (hsize : 8 + n / 8 < 2 ^ 64) :
      (Operand.mem (stack + off) : Operand n).read t =
      (Operand.mem (stack + off) : Operand n).read s := by
    apply memLoad_congr
    intro i hi
    apply congrArg (fun b : Option UInt8 ↦ b.getD 0)
    apply ha.byte
    intro c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨j, hj, heq⟩ := hCov
      exact hb.ne stack hj hi hsize heq.symm
    all_goals exact hCov.elim
  have hm0 := hmem (n := 32) 0 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)
  have hm4 := hmem (n := 32) 4 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)
  have hm8 := hmem (n := 32) 8 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)
  have hm16 := hmem (n := 32) 16 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)
  have hm24 := hmem (n := 32) 24 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)
  have hm32 := hmem (n := 32) 32 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)
  have hm40 := hmem (n := 32) 40 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)
  have hm56 := hmem (n := 32) 56 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)
  have hm64 := hmem (n := 64) 64 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)
  have hm72 := hmem (n := 32) 72 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)
  have hm80 := hmem (n := 32) 80 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)
  have hm88 := hmem (n := 32) 88 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)
  have hm96 := hmem (n := 32) 96 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)
  have hm116 := hmem (n := 32) 116 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)
  have hm120 := hmem (n := 32) 120 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)
  have hm124 := hmem (n := 32) 124 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)
  have hm144 := hmem (n := 32) 144 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)
  have hm152 := hmem (n := 32) 152 (by unfold OffsetsApart; decide +kernel) (by decide +kernel)
  simp only [genericCut016, Write.AllHold] at hw
  obtain ⟨h0, h1, h2, h5, h6, h7, h11, h12, h13, h14, h15,
    hM0, hM4, hM8, hM16, hM24, hM32, hM40, hM56, hM64,
    hM72, hM80, hM88, hM96, hM116, hM120, hM124, hM144, hM152⟩ := hw
  sha1_norm at hs hM64 hInput15
  have hStore48 : (Operand.mem (stack + 48) : Operand 32).read t = W ⟨15, by decide⟩ := by
    simp only [← ho.read_mem]
    sha1_norm [effect016, hs, hM64, hInput15,
      read32_memStore64_low,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
      BitVec.setWidth_add, bswap32_bswap32, extractLsb'_zero_eq_setWidth]
  sha1_norm at hm0 hm4 hm8 hm16 hm24 hm32 hm40 hm56 hm64 hm72 hm80 hm88
  sha1_norm at hm96 hm116 hm120 hm124 hm144 hm152 hStore48
  sha1_norm at h0 h1 h2 h5 h6 h7 h11 h12 h13 h14 h15
  sha1_norm at hM0 hM4 hM8 hM16 hM24 hM32 hM40 hM56 hM64 hM72 hM80 hM88 hM96 hM116 hM120 hM124 hM144
  sha1_norm at hM152
  sha1_norm [genericCut017, Write.AllHold, ← ho.read_reg]
  sha1_norm [effect016, hs, h0, h1, h2, h5, h6, h7, h11, h12, h13, h14,
    h15, hM0, hM4, hM8, hM16, hM24, hM32, hM40, hM56, hM64,
    bswap32_bswap32, hm0, hm4, hm8, hm16, hm24, hm32, hm40, hm56,
    hm64, hm72, hm80, hm88, hm96, hm116, hm120, hm124, hm144, hm152,
    hStore48, hM72, hM80, hM88, hM96, hM116, hM120, hM124, hM144,
    hM152, hInput15]
  rw [hWork]
  simp only [sha1Ch_eq]
  sha1_norm [Parity, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
    BitVec.ofNat_eq_ofNat]
  generalize hR1 : (A 15).rotateLeft 5 = r1 at *
  generalize hR2 : (A 14) = r2 at *
  generalize hR3 : (A 13).rotateLeft 30 = r3 at *
  generalize hR4 : (A 12).rotateLeft 30 = r4 at *
  generalize hR5 : (A 11).rotateLeft 30 = r5 at *
  generalize hW : W ⟨15, by decide⟩ = w at *
  simp_all (config := {decide := true, implicitDefEqProofs := false})
    [bswap32_bswap32,
      BitVec.shiftLeft_zero,
      BitVec.add_zero]
  repeat' apply And.intro
  all_goals try simp only [Operand.read]
  all_goals try sha1_norm [leaSpec, BitVec.setWidth_add, BitVec.setWidth_setWidth_of_le,
    BitVec.setWidth_eq]
  all_goals ac_rfl

theorem effect016_words {stack input : BitVec 64}
    {H : Vector (BitVec 32) 5} {M : Vector (BitVec 32) 16}
    {s t : RamState}
    (hf : FrameData stack input M s)
    (hw : Write.AllHold s (cut016 stack input H M))
    (he : (effect016 s).Holds s t) :
    Write.AllHold t (cut017 stack input H M) := by
  have hWork : (workingAfter M H 16).a =
      ((workingAfter M H 15).a).rotateLeft 5 +
        Standards.NIST.SHA2.SHA256.Ch (workingAfter M H 14).a
          (((workingAfter M H 13).a).rotateLeft 30)
          (((workingAfter M H 12).a).rotateLeft 30) +
        ((workingAfter M H 11).a).rotateLeft 30 +
        0x5a827999 + scheduleWord M ⟨15, by decide⟩ := by
    have h := workingAfter_step_a_values M H 11 (by decide +kernel)
    have hK : K ⟨15, by decide⟩ = 0x5a827999 := by decide
    simpa only [sha1_f_choice (t := ⟨15, by decide⟩) (by decide), sha1Ch_eq,
      hK] using h
  have hW15 : scheduleWord M ⟨15, by decide⟩ = M[15]'(by decide) :=
    scheduleWord_initial M ⟨15, by decide⟩ (by decide)
  have hInput15 := hf.words ⟨15, by decide⟩
  change (Operand.mem (input + BitVec.ofNat 64 60) : Operand 32).read s =
    bswapSpec (M[15]'(by decide)) at hInput15
  rw [← hW15] at hInput15
  exact genericWords016 (fun n ↦ (workingAfter M H n).a) (scheduleWord M)
    hWork hf.stackPointer hInput15 hw he
end Words016

theorem segment016 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x10282f 0x102864
      cut016 cut017 := by
  apply Segment.of_block (fun _ _ _ _ ↦ effect016)
    (fun stack input H M ↦ block016 boundary stack input H M (by
      intro d hd
      apply outsideCompression_ne hOutside <;>
        simp only [bytes016, List.length_cons, List.length_nil] at hd
      all_goals simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat]
      all_goals omega))
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64
      0x282f) bytes016,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact effect016_rip he
  · intro stack input H M s t _ hf _ he
    exact effect016_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect016_words hf hw he

def bytes017 : List UInt8 :=
  [0x4c, 0x89, 0xe0, 0x41, 0x31, 0xc7, 0x45, 0x89, 0xf4, 0x41, 0x31, 0xec, 0x45, 0x31, 0xfc, 0x44,
    0x8b, 0x44, 0x24, 0x58, 0x48, 0x8b, 0x6c, 0x24, 0x38, 0x41, 0x31, 0xe8, 0x44, 0x8b, 0x14, 0x24,
    0x45, 0x89, 0xd7, 0x45, 0x31, 0xdf, 0x45, 0x31, 0xc7, 0x44, 0x8b, 0x54, 0x24, 0x08, 0x44, 0x31,
    0xd0, 0x45, 0x31, 0xcd, 0x41, 0x31, 0xc5]

set_option maxHeartbeats 800000 in
def effect017 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    ((movR64R64Effect 0x102864 0 12)) (xorR32R32Effect 0x102867 3 15 0)) (movR32R32Effect 0x10286a 3
    12 14)) (xorR32R32Effect 0x10286d 3 12 5)) (xorR32R32Effect 0x102870 3 12 15)) (movR32M32Effect
    0x102873 8 (.sib 4 none 0 (.d8 0x58)))) (movR64M64Effect 0x102878 5 (.sib 4 none 0 (.d8 0x38))))
    (xorR32R32Effect 0x10287d 3 8 5)) (movR32M32Effect 0x102880 10 (.sib 4 none 0 .none)))
    (movR32R32Effect 0x102884 3 15 10)) (xorR32R32Effect 0x102887 3 15 11)) (xorR32R32Effect
    0x10288a 3 15 8)) (movR32M32Effect 0x10288d 10 (.sib 4 none 0 (.d8 0x8)))) (xorR32R32Effect
    0x102892 3 0 10)) (xorR32R32Effect 0x102895 3 13 9)) (xorR32R32Effect 0x102898 3 13 0)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 800000 in
theorem block017 [Bindings] (boundary : ReturnBoundary) (stack input : BitVec 64)
    (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes017.length →
      0x102864 + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x102864 ∧ FrameData stack input M s ∧
        Write.AllHold s (cut017 stack input H M))
      (codeRange 0x102864 bytes017) effect017 := by
  unfold bytes017 at hout ⊢
  sha1_run_begin (mov_r64_r64_effect_step 0x102864 0x4c 0xe0 (by unfold RexWPrefix; decide +kernel)
    (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102867 0x41 0xc7
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x10286a 0x45 0xf4
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x10286d 0x41 0xec
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102870 0x45 0xfc
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_m32_effect_step 0x102873 0x44 (by unfold RexNoWPrefix; decide +kernel) 0
    (.sib 4 none 0 (.d8 0x58)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r64_m64_effect_step 0x102878 0x48 (by unfold RexWPrefix; decide +kernel) 5
    (.sib 4 none 0 (.d8 0x38)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x10287d 0x41 0xe8
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_m32_effect_step 0x102880 0x44 (by unfold RexNoWPrefix; decide +kernel) 2
    (.sib 4 none 0 .none) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x102884 0x45 0xd7
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102887 0x45 0xdf
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x10288a 0x45 0xc7
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_m32_effect_step 0x10288d 0x44 (by unfold RexNoWPrefix; decide +kernel) 2
    (.sib 4 none 0 (.d8 0x8)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102892 0x44 0xd0
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102895 0x45 0xcd
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102898 0x41 0xc5
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_finish [effect017]

theorem effect017_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (_hf : FrameData stack input M s)
    (he : (effect017 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hfoot : ∀ c ∈ (effect017 s).components, c ∈ [.reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6,
    .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] :=
    by
    unfold effect017
    iterate 15 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [movR32M32Effect_components, movR32R32Effect_components, movR64M64Effect_components,
        movR64R64Effect_components, xorR32R32Effect_components, List.mem_cons, List.not_mem_nil,
        or_false, or_imp, forall_and, forall_eq]
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only [x86_compose]
  have ha := he.agrees.mono hfoot
  apply ha.widen
  · intro c hc hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl
    all_goals simp_all (config := {decide := true, implicitDefEqProofs := false}) only
      [scratchComponents, x86_compose]
  · intro address c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl
    all_goals first
      | exact hCov.elim

theorem effect017_rip {s t : RamState}
    (he : (effect017 s).Holds s t) :
    t.RIP = 0x10289b := by
  exact he.rip.trans (by rfl)

section Words017
set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem genericWords017 {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) {s t : RamState}
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (hw : Write.AllHold s (genericCut017 stack input H A W))
    (he : (effect017 s).Holds s t) :
    Write.AllHold t (genericCut018 stack input H A W) := by
  have hfull : ∀ wr ∈ (effect017 s).writes, wr.Full := by
    apply Effect.Local.full
    unfold effect017
    repeat' first | (solve | x86_local) | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  simp only [genericCut017, Write.AllHold] at hw
  obtain ⟨h1, h2, h3, h5, h6, h7, h9, h11, h12, h13, h14, h15,
    hM0, hM4, hM8, hM16, hM24, hM32, hM40, hM48, hM56, hM64,
    hM72, hM80, hM88, hM96, hM116, hM120, hM124, hM144, hM152⟩ := hw
  have lo56 := (read32_of_read64_low
    (s:=s) (a:=stack+56) (v:=(Operand.mem (stack+56) : Operand 64).read s) rfl).symm.trans hM56
  sha1_norm at hs
  sha1_norm at h1 h2 h3 h5 h6 h7 h9 h11 h12 h13 h14 h15
  sha1_norm at hM0 hM4 hM8 hM16 hM24 hM32 hM40 hM48 hM56 hM64
  sha1_norm at hM72 hM80 hM88 hM96 hM116 hM120 hM124 hM144 hM152
  sha1_norm [genericCut018, Write.AllHold, ← ho.read_reg, ← ho.read_mem]
  sha1_norm [effect017, hs, h1, h2, h3, h5, h6, h7, h9, h11,
    h12, h13, h14, h15, hM0, hM4, hM8, hM16, hM24, hM32, hM40,
    hM48, hM56, lo56, hM64, hM72, hM80, hM88, hM96, hM116, hM120,
    hM124, hM144, hM152, read32_memStore64_low,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add]
  simp_all (config := {decide := true, implicitDefEqProofs := false})
    [read32_of_read64_low,
      BitVec.add_zero]
  repeat' apply And.intro
  all_goals try simp only [Operand.read]
  all_goals try sha1_norm [leaSpec, BitVec.setWidth_add, BitVec.setWidth_setWidth_of_le,
    BitVec.setWidth_eq]
  all_goals ac_rfl

theorem effect017_words {stack input : BitVec 64}
    {H : Vector (BitVec 32) 5} {M : Vector (BitVec 32) 16}
    {s t : RamState}
    (hf : FrameData stack input M s)
    (hw : Write.AllHold s (cut017 stack input H M))
    (he : (effect017 s).Holds s t) :
    Write.AllHold t (cut018 stack input H M) := by
  exact genericWords017 (fun n ↦ (workingAfter M H n).a) (scheduleWord M)
    hf.stackPointer hw he
end Words017

theorem segment017 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x102864 0x10289b
      cut017 cut018 := by
  apply Segment.of_block (fun _ _ _ _ ↦ effect017)
    (fun stack input H M ↦ block017 boundary stack input H M (by
      intro d hd
      apply outsideCompression_ne hOutside <;>
        simp only [bytes017, List.length_cons, List.length_nil] at hd
      all_goals simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat]
      all_goals omega))
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64
      0x2864) bytes017,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact effect017_rip he
  · intro stack input H M s t _ hf _ he
    exact effect017_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect017_words hf hw he

def bytes021 : List UInt8 :=
  [0x45, 0x31, 0xc2, 0x45, 0x31, 0xf0, 0x44, 0x33, 0x44, 0x24, 0x48, 0x41, 0x31, 0xe8, 0x41, 0xd1,
    0xc0, 0x4c, 0x89, 0xc0, 0x4c, 0x89, 0x44, 0x24, 0x20, 0x41, 0x89, 0xd0, 0x41, 0xc1, 0xc0, 0x1e,
    0x44, 0x89, 0xc5, 0x31, 0xfd, 0x01, 0xf8, 0x89, 0x44, 0x24, 0x0c, 0x31, 0xcf, 0x31, 0xd7, 0xc1,
    0xc2, 0x05, 0x01, 0xf2, 0x81, 0xc2, 0x99, 0x79, 0x82, 0x5a]

set_option maxHeartbeats 800000 in
def effect021 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    (Effect.seq ((xorR32R32Effect 0x10293d 3 10 8)) (xorR32R32Effect 0x102940 3 8 14))
    (xorR32M32Effect 0x102943 8 (.sib 4 none 0 (.d8 0x48)))) (xorR32R32Effect 0x102948 3 8 5))
    (rolR32Effect 0x10294b 3 8 1)) (movR64R64Effect 0x10294e 0 8)) (movM64R64Effect 0x102951 8 (.sib
    4 none 0 (.d8 0x20)))) (movR32R32Effect 0x102956 3 8 2)) (rolR32Effect 0x102959 4 8 30))
    (movR32R32Effect 0x10295d 3 5 8)) (xorR32R32Effect 0x102960 2 5 7)) (addR32R32Effect 0x102962 2
    0 7)) (movM32R32LowEffect 0x102964 0 (.sib 4 none 0 (.d8 0xc)))) (xorR32R32Effect 0x102968 2 7
    1)) (xorR32R32Effect 0x10296a 2 7 2)) (rolR32Effect 0x10296c 3 2 5)) (addR32R32Effect 0x10296f 2
    2 6)) (addR32Imm32Effect 0x102971 6 2 0x5a827999)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 800000 in
theorem block021 [Bindings] (boundary : ReturnBoundary) (stack input : BitVec 64)
    (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes021.length →
      0x10293d + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x10293d ∧ FrameData stack input M s ∧
        Write.AllHold s (cut021 stack input H M))
      (codeRange 0x10293d bytes021) effect021 := by
  unfold bytes021 at hout ⊢
  sha1_run_begin (xor_r32_r32_rex_effect_step 0x10293d 0x45 0xc2
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102940 0x45 0xf0
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_m32_effect_step 0x102943 0x44 (by decide +kernel) 0 (.sib 4 none 0 (.d8
    0x48)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102948 0x41 0xe8
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_one_rex_effect_step 0x10294b 0x41 0xc0
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r64_r64_effect_step 0x10294e 0x4c 0xc0 (by unfold RexWPrefix; decide +kernel)
    (by decide +kernel))
  sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m64_r64_effect_step 0x102951 0x4c
    (by unfold RexWPrefix; decide +kernel) 0 (.sib 4 none 0 (.d8 0x20)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x102956 0x41 0xd0
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_imm8_rex_effect_step 0x102959 0x41 0xc0 0x1e
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x10295d 0x44 0xc5
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x102960 0xfd (by decide +kernel))
  sha1_run_then (add_r32_r32_effect_step 0x102962 0xf8 (by decide +kernel))
  sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m32_r32_low_effect_step 0x102964 0
    (.sib 4 none 0 (.d8 0xc)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x102968 0xcf (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x10296a 0xd7 (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x10296c 0xc2 0x5 (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_effect_step 0x10296f 0xf2 (by decide +kernel))
  sha1_run_then (add_r32_imm32_effect_step 0x102971 0xc2 0x5a827999 (by decide +kernel)
    (by decide +kernel))
  sha1_run_finish [effect021]

theorem effect021_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s)
    (he : (effect021 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have hfoot : ∀ c ∈ (effect021 s).components, c ∈ [.mem ((Operand.reg 4 : Operand 64).read s +
    BitVec.ofNat 64 12) 4, .mem ((Operand.reg 4 : Operand 64).read s + BitVec.ofNat 64 32) 8, .reg
    0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12,
    .reg 13, .reg 14, .reg 15, .flags, .rip] := by
    unfold effect021
    iterate 17 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [addR32Imm32Effect_components, addR32R32Effect_components, movM32R32LowEffect,
        movM64R64Effect_components, movR32R32Effect_components, movR64R64Effect_components,
        rolR32Effect_components, xorR32M32Effect_components, xorR32R32Effect_components,
        List.mem_cons, List.not_mem_nil, or_false, or_imp, forall_and, forall_eq, or_true]
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only [x86_compose]
  have ha := he.agrees.mono hfoot
  rw [hs] at ha
  apply ha.widen
  · intro c hc hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all (config := {decide := true, implicitDefEqProofs := false}) only
      [Component.isMem, scratchComponents, x86_compose]
  · intro address c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hCov.elim
      | exact scratchComponents_stack (Or.inl (by decide +kernel)) hCov
      | exact scratchComponents_stack (Or.inl (by decide +kernel)) hCov

theorem effect021_rip {s t : RamState}
    (he : (effect021 s).Holds s t) :
    t.RIP = 0x102977 := by
  exact he.rip.trans (by rfl)

section Words021
private theorem compiler_choice_bool021 (e b c : BitVec 32) :
    (e &&& c ^^^ e &&& b) ^^^ c = ((b ^^^ c) &&& e) ^^^ c := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and]
  cases e.getLsbD i <;> cases b.getLsbD i <;> cases c.getLsbD i <;> decide

private theorem compiler_choice_order021 (a b c d e w : BitVec 32) :
    a + (w + d + (e &&& c ^^^ e &&& b ^^^ c)) + 0x5a827999 =
      a + Standards.NIST.SHA2.SHA256.Ch e b c + d +
        0x5a827999 + w := by
  rw [compiler_choice_bool021 e b c]
  simp only [sha1Ch_eq, BitVec.xor_comm, BitVec.and_comm]
  try simp (config := {decide := true}) only [leaSpec, BitVec.setWidth_add,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
  all_goals try sha1_norm [leaSpec, BitVec.setWidth_add, BitVec.setWidth_setWidth_of_le,
    BitVec.setWidth_eq]
  all_goals ac_rfl

private theorem obs021 {s t : RamState} (he : (effect021 s).Holds s t) :
    Obs ((effect021 s).after s true) t := by
  apply he.obsAfter _ true
  apply Effect.Local.full
  unfold effect021
  repeat' first | (solve | x86_local) | apply Effect.Local.seq

private theorem rawR2_021 {s t : RamState} (v2 v6 : BitVec 32)
    (h2 : (Operand.reg 2 : Operand 32).read s = v2)
    (h6 : (Operand.reg 6 : Operand 32).read s = v6)
    (he : (effect021 s).Holds s t) :
    (Operand.reg 2 : Operand 32).read t = v2.rotateLeft 5 + v6 + 0x5a827999 := by
  sha1_norm at h2 h6
  have ho := obs021 he
  simp only [← ho.read_reg]
  sha1_norm [effect021, h2, h6,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]

private theorem rawR5_021 {s t : RamState} (v2 v7 : BitVec 32)
    (h2 : (Operand.reg 2 : Operand 32).read s = v2)
    (h7 : (Operand.reg 7 : Operand 32).read s = v7)
    (he : (effect021 s).Holds s t) :
    (Operand.reg 5 : Operand 32).read t = v2.rotateLeft 30 ^^^ v7 := by
  sha1_norm at h2 h7
  have ho := obs021 he
  simp only [← ho.read_reg]
  sha1_norm [effect021, h2, h7,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]

private theorem rawR7_021 {s t : RamState} (v1 v2 v7 : BitVec 32)
    (h1 : (Operand.reg 1 : Operand 32).read s = v1)
    (h2 : (Operand.reg 2 : Operand 32).read s = v2)
    (h7 : (Operand.reg 7 : Operand 32).read s = v7)
    (he : (effect021 s).Holds s t) :
    (Operand.reg 7 : Operand 32).read t = v7 ^^^ v1 ^^^ v2 := by
  sha1_norm at h1 h2 h7
  have ho := obs021 he
  simp only [← ho.read_reg]
  sha1_norm [effect021, h1, h2, h7,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]

private theorem rawR8_021 {s t : RamState} (v2 : BitVec 32)
    (h2 : (Operand.reg 2 : Operand 32).read s = v2)
    (he : (effect021 s).Holds s t) :
    (Operand.reg 8 : Operand 32).read t = v2.rotateLeft 30 := by
  sha1_norm at h2
  have ho := obs021 he
  simp only [← ho.read_reg]
  sha1_norm [effect021, h2,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]

private theorem rawR10_021 {s t : RamState} (v8 v10 : BitVec 32)
    (h8 : (Operand.reg 8 : Operand 32).read s = v8)
    (h10 : (Operand.reg 10 : Operand 32).read s = v10)
    (he : (effect021 s).Holds s t) :
    (Operand.reg 10 : Operand 32).read t = v10 ^^^ v8 := by
  sha1_norm at h8 h10
  have ho := obs021 he
  simp only [← ho.read_reg]
  sha1_norm [effect021, h8, h10,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]

private theorem rawM12_021 {s t : RamState} (stack : BitVec 64)
    (v5 v7 v8 v14 m72 : BitVec 32)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (h5 : (Operand.reg 5 : Operand 32).read s = v5)
    (h7 : (Operand.reg 7 : Operand 32).read s = v7)
    (h8 : (Operand.reg 8 : Operand 32).read s = v8)
    (h14 : (Operand.reg 14 : Operand 32).read s = v14)
    (hM72 : (Operand.mem (stack + 72) : Operand 32).read s = m72)
    (he : (effect021 s).Holds s t) :
    (Operand.mem (stack + 12) : Operand 32).read t = (v8 ^^^ v14 ^^^ m72 ^^^ v5).rotateLeft 1 + v7
      := by
  sha1_norm at hs h5 h7 h8 h14 hM72
  have ho := obs021 he
  simp only [← ho.read_mem]
  sha1_norm [effect021, hs, h5, h7, h8, h14, hM72]
  simp (config := {decide := true, implicitDefEqProofs := false}) only
    [BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]

private theorem rawM32_021 {s t : RamState} (stack : BitVec 64)
    (v5 v8 v14 m72 : BitVec 32)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (h5 : (Operand.reg 5 : Operand 32).read s = v5)
    (h8 : (Operand.reg 8 : Operand 32).read s = v8)
    (h14 : (Operand.reg 14 : Operand 32).read s = v14)
    (hM72 : (Operand.mem (stack + 72) : Operand 32).read s = m72)
    (he : (effect021 s).Holds s t) :
    (Operand.mem (stack + 32) : Operand 32).read t = (v8 ^^^ v14 ^^^ m72 ^^^ v5).rotateLeft 1 := by
  sha1_norm at hs h5 h8 h14 hM72
  have ho := obs021 he
  simp only [← ho.read_mem]
  sha1_norm [effect021, hs, h5, h8, h14, hM72]
  simp (config := {decide := true, implicitDefEqProofs := false}) only
    [read32_memStore64_low,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
      ← BitVec.setWidth_eq_extractLsb']

private theorem genericWords021 {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32)
    (hWork : (A 19).rotateLeft 5 +
      (W 19 + (A 15).rotateLeft 30 +
        (A 18 &&& (A 16).rotateLeft 30 ^^^ A 18 &&& (A 17).rotateLeft 30 ^^^
          (A 16).rotateLeft 30)) + 0x5a827999 = A 20)
    (hSchedule22 : W 22 = (W 19 ^^^ W 14 ^^^ W 8 ^^^ W 6).rotateLeft 1)
    {s t : RamState} (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (hw : Write.AllHold s (genericCut021 stack input H A W))
    (he : (effect021 s).Holds s t) :
    Write.AllHold t (genericCut022 stack input H A W) := by
  simp only [genericCut021, Write.AllHold] at hw
  obtain ⟨h1,h2,h3,h5,h6,h7,h8,h9,h10,h12,h13,h14,h15,
    hM0,hM16,hM24,hM40,hM48,hM56,hM64,hM72,hM80,hM96,
    hM116,hM120,hM124,hM144,hM152⟩ := hw
  have hR2 := rawR2_021 (A 19)
    (W 19 + (A 15).rotateLeft 30 +
      (A 18 &&& (A 16).rotateLeft 30 ^^^ A 18 &&& (A 17).rotateLeft 30 ^^^
        (A 16).rotateLeft 30)) h2 h6 he
  have hR5 := rawR5_021 (A 19) ((A 18).rotateLeft 30) h2 h7 he
  have hR7 := rawR7_021 ((A 17).rotateLeft 30) (A 19) ((A 18).rotateLeft 30)
    h1 h2 h7 he
  have hR8 := rawR8_021 (A 19) h2 he
  have hR10 := rawR10_021 (W 6) (W 4) h8 h10 he
  have hV22 : (W 6 ^^^ W 8 ^^^ W 14 ^^^ W 19).rotateLeft 1 = W 22 := by
    rw [hSchedule22]
    apply congrArg (fun x : BitVec 32 ↦ x.rotateLeft 1)
    try simp (config := {decide := true}) only [leaSpec, BitVec.setWidth_add,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
    all_goals try sha1_norm [leaSpec, BitVec.setWidth_add, BitVec.setWidth_setWidth_of_le,
      BitVec.setWidth_eq]
    all_goals ac_rfl
  have hM12 := rawM12_021 stack (W 19) ((A 18).rotateLeft 30) (W 6) (W 8) (W 14)
    hs h5 h7 h8 h14 hM72 he
  have hM32 := rawM32_021 stack (W 19) (W 6) (W 8) (W 14)
    hs h5 h8 h14 hM72 he
  rw [hV22] at hM12 hM32
  rw [hWork] at hR2
  have hfoot : ∀ c ∈ (effect021 s).components,
      c ∈ [.mem ((Operand.reg 4 : Operand 64).read s + 12) 4,
        .mem ((Operand.reg 4 : Operand 64).read s + 32) 8,
        .reg 0,.reg 2,.reg 5,.reg 7,.reg 8,.reg 10,.flags,.rip] := by
    unfold effect021
    iterate 17 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [addR32Imm32Effect_components, addR32R32Effect_components,
       movM32R32LowEffect, movM64R64Effect_components, movR32R32Effect_components,
       movR64R64Effect_components, rolR32Effect_components, xorR32M32Effect_components,
       xorR32R32Effect_components, List.mem_cons, List.not_mem_nil, or_false,
       or_imp, forall_and, forall_eq, or_true]
    all_goals sha1_norm
  have ha := he.agrees.mono hfoot
  rw [hs] at ha
  have hmem {n : Nat} (off : BitVec 64)
      (h12 : OffsetsApart 12 4 off (n / 8))
      (h32 : OffsetsApart 32 8 off (n / 8))
      (hn12 : 4 + n / 8 < 2 ^ 64) (hn32 : 8 + n / 8 < 2 ^ 64) :
      (Operand.mem (stack + off) : Operand n).read t =
      (Operand.mem (stack + off) : Operand n).read s := by
    apply memLoad_congr
    intro i hi
    apply congrArg (fun b : Option UInt8 ↦ b.getD 0)
    apply ha.byte
    intro c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨j,hj,heq⟩ := hCov
      exact h12.ne stack hj hi hn12 heq.symm
    · obtain ⟨j,hj,heq⟩ := hCov
      exact h32.ne stack hj hi hn32 heq.symm
    all_goals exact hCov.elim
  simp only [genericCut022, Write.AllHold]
  refine ⟨?f0, ?f1, ?f2, ?f3, ?f4, ?f5, ?f6, ?f7, ?f8, ?f9, ?f10, ?f11, ?f12, ?f13, ?f14, ?f15,
    ?f16, ?f17, ?f18, ?f19, ?f20, ?f21, ?f22, ?f23, ?f24, ?f25, ?f26, ?f27, ?f28⟩
  case f0 =>
    exact (ha.read (by simp)).trans h1
  case f1 =>
    exact hR2
  case f2 =>
    exact (ha.read (by simp)).trans h3
  case f3 =>
    exact hR5.trans (BitVec.xor_comm _ _)
  case f4 =>
    exact hR7.trans (by ac_rfl)
  case f5 =>
    exact hR8
  case f6 =>
    exact (ha.read (by simp)).trans h9
  case f7 =>
    exact hR10
  case f8 =>
    exact (ha.read (by simp)).trans h12
  case f9 =>
    exact (ha.read (by simp)).trans h13
  case f10 =>
    exact (ha.read (by simp)).trans h14
  case f11 =>
    exact (ha.read (by simp)).trans h15
  case f12 =>
    exact (hmem 0 (by unfold OffsetsApart; decide +kernel)
      (by unfold OffsetsApart; decide +kernel) (by decide +kernel) (by decide +kernel)).trans hM0
  case f13 =>
    exact hM12
  case f14 =>
    exact (hmem 16 (by unfold OffsetsApart; decide +kernel)
      (by unfold OffsetsApart; decide +kernel) (by decide +kernel) (by decide +kernel)).trans hM16
  case f15 =>
    exact (hmem 24 (by unfold OffsetsApart; decide +kernel)
      (by unfold OffsetsApart; decide +kernel) (by decide +kernel) (by decide +kernel)).trans hM24
  case f16 =>
    exact hM32
  case f17 =>
    exact (hmem 40 (by unfold OffsetsApart; decide +kernel)
      (by unfold OffsetsApart; decide +kernel) (by decide +kernel) (by decide +kernel)).trans hM40
  case f18 =>
    exact (hmem 48 (by unfold OffsetsApart; decide +kernel)
      (by unfold OffsetsApart; decide +kernel) (by decide +kernel) (by decide +kernel)).trans hM48
  case f19 =>
    exact (hmem 56 (by unfold OffsetsApart; decide +kernel)
      (by unfold OffsetsApart; decide +kernel) (by decide +kernel) (by decide +kernel)).trans hM56
  case f20 =>
    exact (hmem 64 (by unfold OffsetsApart; decide +kernel)
      (by unfold OffsetsApart; decide +kernel) (by decide +kernel) (by decide +kernel)).trans hM64
  case f21 =>
    exact (hmem 72 (by unfold OffsetsApart; decide +kernel)
      (by unfold OffsetsApart; decide +kernel) (by decide +kernel) (by decide +kernel)).trans hM72
  case f22 =>
    exact (hmem 80 (by unfold OffsetsApart; decide +kernel)
      (by unfold OffsetsApart; decide +kernel) (by decide +kernel) (by decide +kernel)).trans hM80
  case f23 =>
    exact (hmem 96 (by unfold OffsetsApart; decide +kernel)
      (by unfold OffsetsApart; decide +kernel) (by decide +kernel) (by decide +kernel)).trans hM96
  case f24 =>
    exact (hmem 116 (by unfold OffsetsApart; decide +kernel)
      (by unfold OffsetsApart; decide +kernel) (by decide +kernel) (by decide +kernel)).trans hM116
  case f25 =>
    exact (hmem 120 (by unfold OffsetsApart; decide +kernel)
      (by unfold OffsetsApart; decide +kernel) (by decide +kernel) (by decide +kernel)).trans hM120
  case f26 =>
    exact (hmem 124 (by unfold OffsetsApart; decide +kernel)
      (by unfold OffsetsApart; decide +kernel) (by decide +kernel) (by decide +kernel)).trans hM124
  case f27 =>
    exact (hmem 144 (by unfold OffsetsApart; decide +kernel)
      (by unfold OffsetsApart; decide +kernel) (by decide +kernel) (by decide +kernel)).trans hM144
  case f28 =>
    exact (hmem 152 (by unfold OffsetsApart; decide +kernel)
      (by unfold OffsetsApart; decide +kernel) (by decide +kernel) (by decide +kernel)).trans hM152

theorem effect021_words {stack input : BitVec 64}
    {H : Vector (BitVec 32) 5} {M : Vector (BitVec 32) 16}
    {s t : RamState}
    (hf : FrameData stack input M s)
    (hw : Write.AllHold s (cut021 stack input H M))
    (he : (effect021 s).Holds s t) :
    Write.AllHold t (cut022 stack input H M) := by
  let A : Nat → BitVec 32 := fun n ↦ (workingAfter M H n).a
  let W : Fin 80 → BitVec 32 := scheduleWord M
  have hWork : A 20 = (A 19).rotateLeft 5 +
      f ⟨19, by decide⟩ (A 18) ((A 17).rotateLeft 30)
        ((A 16).rotateLeft 30) + (A 15).rotateLeft 30 +
      K ⟨19, by decide⟩ + W 19 := by
    change (workingAfter M H 20).a =
      ((workingAfter M H 19).a).rotateLeft 5 +
        f ⟨19, by decide⟩ (workingAfter M H 18).a
          (((workingAfter M H 17).a).rotateLeft 30)
          (((workingAfter M H 16).a).rotateLeft 30) +
        ((workingAfter M H 15).a).rotateLeft 30 +
        K ⟨19, by decide⟩ + scheduleWord M ⟨19, by decide⟩
    exact workingAfter_step_a_values M H 15 (by decide +kernel)
  have hSchedule22 : W 22 = (W 19 ^^^ W 14 ^^^ W 8 ^^^ W 6).rotateLeft 1 := by
    dsimp [W]
    change scheduleWord M (⟨22, by decide⟩ : Fin 80) = _
    rw [scheduleWord_recurrence M ⟨22, by decide⟩ (by decide)]
    simp only [Nat.reduceSub]
    rw [sha1Rotl_eq_rotateLeft 1 _ (by decide)]
    rfl
  have hMachine : (A 19).rotateLeft 5 +
      (W 19 + (A 15).rotateLeft 30 +
        (A 18 &&& (A 16).rotateLeft 30 ^^^ A 18 &&& (A 17).rotateLeft 30 ^^^
          (A 16).rotateLeft 30)) + 0x5a827999 = A 20 := by
    calc
      _ = (A 19).rotateLeft 5 + Standards.NIST.SHA2.SHA256.Ch (A 18)
          ((A 17).rotateLeft 30) ((A 16).rotateLeft 30) +
          (A 15).rotateLeft 30 + 0x5a827999 + W 19 :=
        compiler_choice_order021 _ _ _ _ _ _
      _ = A 20 := by
        rw [hWork]
        simp only [sha1_f_choice (t := ⟨19, by decide⟩) (by decide),
          show K ⟨19, by decide⟩ = 0x5a827999 by decide]
  have hpre : Write.AllHold s (genericCut021 stack input H A W) := by
    simpa only [genericCut021, cut021, A, W] using hw
  have hraw := genericWords021 (stack := stack) (input := input) (H := H)
    A W hMachine hSchedule22 (s := s) (t := t) hf.stackPointer hpre he
  simpa only [genericCut022, cut022, A, W] using hraw
end Words021

theorem segment021 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x10293d 0x102977
      cut021 cut022 := by
  apply Segment.of_block (fun _ _ _ _ ↦ effect021)
    (fun stack input H M ↦ block021 boundary stack input H M (by
      intro d hd
      apply outsideCompression_ne hOutside <;>
        simp only [bytes021, List.length_cons, List.length_nil] at hd
      all_goals simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat]
      all_goals omega))
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64
      0x293d) bytes021,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact effect021_rip he
  · intro stack input H M s t _ hf _ he
    exact effect021_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect021_words hf hw he

def bytes022 : List UInt8 :=
  [0x44, 0x89, 0xd6, 0x4c, 0x8b, 0x5c, 0x24, 0x60, 0x44, 0x31, 0xde, 0x44, 0x31, 0xfe, 0xd1, 0xc6,
    0x41, 0x89, 0xf2, 0x89, 0xd6, 0xc1, 0xc6, 0x05, 0x44, 0x01, 0xd3, 0x44, 0x89, 0x54, 0x24, 0x08,
    0x01, 0xfb, 0x8d, 0x04, 0x1e, 0x05, 0xa1, 0xeb, 0xd9, 0x6e, 0x48, 0x8b, 0x7c, 0x24, 0x28, 0x41,
    0x31, 0xfd, 0x48, 0x8b, 0x5c, 0x24, 0x10]

set_option maxHeartbeats 800000 in
def effect022 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    ((movR32R32Effect 0x102977 3 6 10)) (movR64M64Effect 0x10297a 11 (.sib 4 none 0 (.d8 0x60))))
    (xorR32R32Effect 0x10297f 3 6 11)) (xorR32R32Effect 0x102982 3 6 15)) (rolR32Effect 0x102985 2 6
    1)) (movR32R32Effect 0x102987 3 10 6)) (movR32R32Effect 0x10298a 2 6 2)) (rolR32Effect 0x10298c
    3 6 5)) (addR32R32Effect 0x10298f 3 3 10)) (movM32R32Effect 0x102992 10 (.sib 4 none 0 (.d8
    0x8)))) (addR32R32Effect 0x102997 2 3 7)) (leaR32Effect 0x102999 3 0 (.sib 6 (some 3) 0 .none)))
    (addEaxImm32Effect 0x10299c 0x6ed9eba1)) (movR64M64Effect 0x1029a1 7 (.sib 4 none 0 (.d8
    0x28)))) (xorR32R32Effect 0x1029a6 3 13 7)) (movR64M64Effect 0x1029a9 3 (.sib 4 none 0 (.d8
    0x10)))

set_option maxHeartbeats 800000 in
theorem block022 [Bindings] (boundary : ReturnBoundary) (stack input : BitVec 64)
    (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes022.length →
      0x102977 + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x102977 ∧ FrameData stack input M s ∧
        Write.AllHold s (cut022 stack input H M))
      (codeRange 0x102977 bytes022) effect022 := by
  have hRaw :
      AdvancesBlock boundary
        (fun s ↦ s.RIP = 0x102977 ∧ FrameData stack input M s)
        (codeRange 0x102977 bytes022) effect022 := by
    unfold bytes022 at hout ⊢
    sha1_run_begin (mov_r32_r32_rex_effect_step 0x102977 0x44 0xd6
      (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
    sha1_run_then (mov_r64_m64_effect_step 0x10297a 0x4c (by unfold RexWPrefix; decide +kernel) 3
      (.sib 4 none 0 (.d8 0x60)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    sha1_run_then (xor_r32_r32_rex_effect_step 0x10297f 0x44 0xde
      (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
    sha1_run_then (xor_r32_r32_rex_effect_step 0x102982 0x44 0xfe
      (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
    sha1_run_then (rol_r32_one_effect_step 0x102985 0xc6 (by decide +kernel) (by decide +kernel))
    sha1_run_then (mov_r32_r32_rex_effect_step 0x102987 0x41 0xf2
      (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
    sha1_run_then (mov_r32_r32_effect_step 0x10298a 0xd6 (by decide +kernel))
    sha1_run_then (rol_r32_imm8_effect_step 0x10298c 0xc6 0x5 (by decide +kernel)
      (by decide +kernel))
    sha1_run_then (add_r32_r32_rex_effect_step 0x10298f 0x44 0xd3
      (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
    sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m32_r32_effect_step 0x102992 0x44
      (by unfold RexNoWPrefix; decide +kernel) 2 (.sib 4 none 0 (.d8 0x8)) (by decide +kernel)
      (by decide +kernel) (by decide +kernel))
    sha1_run_then (add_r32_r32_effect_step 0x102997 0xfb (by decide +kernel))
    sha1_run_then (lea_r32_effect_step 0x102999 0 (.sib 6 (some 3) 0 .none) (by decide +kernel)
      (by decide +kernel) (by decide +kernel))
    sha1_run_then (add_eax_imm32_effect_step 0x10299c 0x6ed9eba1)
    sha1_run_then (mov_r64_m64_effect_step 0x1029a1 0x48 (by unfold RexWPrefix; decide +kernel) 7
      (.sib 4 none 0 (.d8 0x28)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    sha1_run_then (xor_r32_r32_rex_effect_step 0x1029a6 0x41 0xfd
      (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
    sha1_run_then (mov_r64_m64_effect_step 0x1029a9 0x48 (by unfold RexWPrefix; decide +kernel) 3
      (.sib 4 none 0 (.d8 0x10)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    sha1_run_finish [effect022]
  intro s hr hc hp
  exact hRaw s hr hc ⟨hp.1, hp.2.1⟩

theorem effect022_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s)
    (he : (effect022 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have hfoot : ∀ c ∈ (effect022 s).components, c ∈ [.mem ((Operand.reg 4 : Operand 64).read s +
    BitVec.ofNat 64 8) 4, .reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9,
    .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] := by
    unfold effect022
    iterate 15 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [leaR32Effect_components, addEaxImm32Effect_components, addR32R32Effect_components,
        movM32R32Effect_components, movR32R32Effect_components, movR64M64Effect_components,
        rolR32Effect_components, xorR32R32Effect_components, List.mem_cons, List.not_mem_nil,
        or_false, or_imp, forall_and, forall_eq, or_true]
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only [x86_compose]
  have ha := he.agrees.mono hfoot
  rw [hs] at ha
  apply ha.widen
  · intro c hc hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl
    all_goals simp_all (config := {decide := true, implicitDefEqProofs := false}) only
      [Component.isMem, scratchComponents, x86_compose]
  · intro address c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl
    all_goals first
      | exact hCov.elim
      | exact scratchComponents_stack (Or.inl (by decide +kernel)) hCov

theorem effect022_rip {s t : RamState}
    (he : (effect022 s).Holds s t) :
    t.RIP = 0x1029ae := by
  exact he.rip.trans (by rfl)

section Words022
private theorem genericWords022 {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32)
    (hWork : A 21 = (A 20).rotateLeft 5 +
      ((A 19) ^^^ (A 18).rotateLeft 30 ^^^ (A 17).rotateLeft 30) +
      (A 16).rotateLeft 30 + 0x6ed9eba1 + W 20)
    (hSchedule20 : W 20 = (W 17 ^^^ W 12 ^^^ W 6 ^^^ W 4).rotateLeft 1)
    {s t : RamState} (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (hw : Write.AllHold s (genericCut022 stack input H A W))
    (he : (effect022 s).Holds s t) :
    Write.AllHold t (genericCut023 stack input H A W) := by
  have hfull : ∀ w ∈ (effect022 s).writes, w.Full := by
    apply Effect.Local.full
    unfold effect022
    repeat' first | (solve | x86_local) | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  sha1_norm at hs
  simp only [genericCut022, Write.AllHold] at hw
  obtain ⟨h1, h2, h3, h5, h7, h8, h9, h10, h12, h13, h14, h15,
    hM0, hM12, hM16, hM24, hM32, hM40, hM48, hM56, hM64, hM72, hM80,
    hM96, hM116, hM120, hM124, hM144, hM152⟩ := hw
  have lo16 := (read32_of_read64_low
    (s := s) (a := stack + 16)
    (v := (Operand.mem (stack + 16) : Operand 64).read s) rfl).symm.trans hM16
  have lo40 := (read32_of_read64_low
    (s := s) (a := stack + 40)
    (v := (Operand.mem (stack + 40) : Operand 64).read s) rfl).symm.trans hM40
  have lo96 := (read32_of_read64_low
    (s := s) (a := stack + 96)
    (v := (Operand.mem (stack + 96) : Operand 64).read s) rfl).symm.trans hM96
  sha1_norm at h1 h2 h3 h5 h7 h8 h9 h10 h12 h13 h14 h15
  sha1_norm at hM0 hM12 hM16 hM24 hM32 hM40 hM48 hM56 hM64 hM72 hM80
  sha1_norm at hM96 hM116 hM120 hM124 hM144 hM152
  simp only [genericCut023, Write.AllHold, ← ho.read_reg, ← ho.read_mem]
  sha1_norm [effect022, hs, h1, h2, h3, h5, h7, h8, h9, h10, h12, h13,
    h14, h15, hM0, hM12, lo16, hM24, hM32, lo40, hM48, hM56, hM64,
    hM72, hM80, lo96, hM116, hM120, hM124, hM144, hM152]
  rw [hWork, hSchedule20]
  sha1_norm [read32_of_read64_low,
    BitVec.setWidth_add,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq] at *
  simp_all (config := {decide := true, implicitDefEqProofs := false})
  have hXor20 : (W 4 ^^^ W 6 ^^^ W 12 ^^^ W 17).rotateLeft 1 =
      (W 17 ^^^ W 12 ^^^ W 6 ^^^ W 4).rotateLeft 1 := by
    congr 1
    try simp (config := {decide := true}) only [leaSpec, BitVec.setWidth_add,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
    all_goals try sha1_norm [leaSpec, BitVec.setWidth_add, BitVec.setWidth_setWidth_of_le,
      BitVec.setWidth_eq]
    all_goals ac_rfl
  rw [hXor20]
  repeat' apply And.intro
  all_goals
    try generalize hR1 : (A 20).rotateLeft 5 = r1 at ⊢
    try generalize hR2 : (A 17).rotateLeft 30 = r2 at ⊢
    try generalize hR3 : (A 18).rotateLeft 30 = r3 at ⊢
    try generalize hR4 : (A 19).rotateLeft 30 = r4 at ⊢
    try generalize hA : A 16 = a at ⊢
    try generalize hW : (W 17 ^^^ W 12 ^^^ W 6 ^^^ W 4).rotateLeft 1 = w at ⊢
    try simp (config := {decide := true}) only [leaSpec, BitVec.setWidth_add,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
    all_goals try sha1_norm [leaSpec, BitVec.setWidth_add, BitVec.setWidth_setWidth_of_le,
      BitVec.setWidth_eq]
    all_goals ac_rfl

theorem effect022_words {stack input : BitVec 64}
    {H : Vector (BitVec 32) 5} {M : Vector (BitVec 32) 16}
    {s t : RamState}
    (hf : FrameData stack input M s)
    (hw : Write.AllHold s (cut022 stack input H M))
    (he : (effect022 s).Holds s t) :
    Write.AllHold t (cut023 stack input H M) := by
  let A : Nat → BitVec 32 := fun n ↦ (workingAfter M H n).a
  let W : Fin 80 → BitVec 32 := scheduleWord M
  have hWork : A 21 = (A 20).rotateLeft 5 +
      ((A 19) ^^^ (A 18).rotateLeft 30 ^^^ (A 17).rotateLeft 30) +
      (A 16).rotateLeft 30 + 0x6ed9eba1 + W 20 := by
    dsimp [A, W]
    rw [workingAfter_step_a_values M H 16 (by decide), sha1_f_parity_first (by decide) (by decide)]
    simp [K, Parity]
  have hSchedule20 : W 20 = (W 17 ^^^ W 12 ^^^ W 6 ^^^ W 4).rotateLeft 1 := by
    dsimp [W]
    change scheduleWord M (⟨20, by decide⟩ : Fin 80) = _
    rw [scheduleWord_recurrence M ⟨20, by decide⟩ (by decide)]
    simp only [Nat.reduceSub]
    rw [sha1Rotl_eq_rotateLeft 1 _ (by decide)]
    rfl
  have hpre : Write.AllHold s (genericCut022 stack input H A W) := by
    change Write.AllHold s (cut022 stack input H M)
    exact hw
  have hraw := genericWords022 A W hWork hSchedule20 hf.stackPointer hpre he
  change Write.AllHold t (cut023 stack input H M)
  exact hraw
end Words022

theorem segment022 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x102977 0x1029ae
      cut022 cut023 := by
  apply Segment.of_block (fun _ _ _ _ ↦ effect022)
    (fun stack input H M ↦ block022 boundary stack input H M (by
      intro d hd
      apply outsideCompression_ne hOutside <;>
        simp only [bytes022, List.length_cons, List.length_nil] at hd
      all_goals simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat]
      all_goals omega))
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64
      0x2977) bytes022,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact effect022_rip he
  · intro stack input H M s t _ hf _ he
    exact effect022_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect022_words hf hw he

def bytes018 : List UInt8 :=
  [0xc1, 0xc6, 0x1e, 0x41, 0x89, 0xf0, 0x41, 0x31, 0xd0, 0x41, 0x21, 0xf8, 0x41, 0xd1, 0xc4, 0x41,
    0x89, 0xd9, 0x41, 0xc1, 0xc1, 0x5, 0x41, 0x31, 0xd0, 0x44, 0x1, 0xe1, 0x44, 0x1, 0xc1, 0x44,
    0x1, 0xc9, 0x81, 0xc1, 0x99, 0x79, 0x82, 0x5a, 0x41, 0xd1, 0xc7, 0x41, 0x89, 0xf8, 0x41, 0xc1,
    0xc0, 0x1e, 0x44, 0x89, 0xc7, 0x31, 0xf7, 0x21, 0xdf]

set_option maxHeartbeats 800000 in
def effect018 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    (Effect.seq ((rolR32Effect 0x10289b 3 6 30)) (movR32R32Effect 0x10289e 3 8 6)) (xorR32R32Effect
    0x1028a1 3 8 2)) (andR32R32Effect 0x1028a4 3 8 7)) (rolR32Effect 0x1028a7 3 12 1))
    (movR32R32Effect 0x1028aa 3 9 3)) (rolR32Effect 0x1028ad 4 9 5)) (xorR32R32Effect 0x1028b1 3 8
    2)) (addR32R32Effect 0x1028b4 3 1 12)) (addR32R32Effect 0x1028b7 3 1 8)) (addR32R32Effect
    0x1028ba 3 1 9)) (addR32Imm32Effect 0x1028bd 6 1 0x5a827999)) (rolR32Effect 0x1028c3 3 15 1))
    (movR32R32Effect 0x1028c6 3 8 7)) (rolR32Effect 0x1028c9 4 8 30)) (movR32R32Effect 0x1028cd 3 7
    8)) (xorR32R32Effect 0x1028d0 2 7 6)) (andR32R32Effect 0x1028d2 2 7 3)

set_option maxHeartbeats 1600000 in
theorem block018 [Bindings] (boundary : ReturnBoundary)
    (stack input : BitVec 64) (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes018.length → 0x10289b + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x10289b ∧ FrameData stack input M s ∧
        Write.AllHold s (cut018 stack input H M))
      (codeRange 0x10289b bytes018) effect018 := by
  unfold bytes018 at hout ⊢
  sha1_run_begin (rol_r32_imm8_effect_step 0x10289b 0xc6 0x1e (by decide +kernel)
    (by decide +kernel))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x10289e 0x41 0xf0
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x1028a1 0x41 0xd0
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (and_r32_r32_rex_effect_step 0x1028a4 0x41 0xf8
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_one_rex_effect_step 0x1028a7 0x41 0xc4
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x1028aa 0x41 0xd9
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_imm8_rex_effect_step 0x1028ad 0x41 0xc1 0x5
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x1028b1 0x41 0xd0
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x1028b4 0x44 0xe1
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x1028b7 0x44 0xc1
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x1028ba 0x44 0xc9
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_imm32_effect_step 0x1028bd 0xc1 0x5a827999 (by decide +kernel)
    (by decide +kernel))
  sha1_run_then (rol_r32_one_rex_effect_step 0x1028c3 0x41 0xc7
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x1028c6 0x41 0xf8
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_imm8_rex_effect_step 0x1028c9 0x41 0xc0 0x1e
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x1028cd 0x44 0xc7
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x1028d0 0xf7 (by decide +kernel))
  sha1_run_then (and_r32_r32_effect_step 0x1028d2 0xdf (by decide +kernel))
  sha1_run_finish [effect018]

def bytes019 : List UInt8 :=
  [0x31, 0xf7, 0x44, 0x1, 0xfa, 0x1, 0xfa, 0x89, 0xcf, 0xc1, 0xc7, 0x5, 0x1, 0xd7, 0x81, 0xc7, 0x99,
    0x79, 0x82, 0x5a, 0x41, 0xd1, 0xc5, 0x42, 0x8d, 0x14, 0x2e, 0x4d, 0x89, 0xe9, 0xc1, 0xc3, 0x1e,
    0x89, 0xde, 0x44, 0x31, 0xc6, 0x21, 0xce, 0x44, 0x31, 0xc6, 0x1, 0xd6, 0x89, 0xfa, 0xc1, 0xc2,
    0x5, 0x1, 0xf2, 0x81, 0xc2, 0x99, 0x79, 0x82, 0x5a]

set_option maxHeartbeats 800000 in
def effect019 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    (Effect.seq (Effect.seq (Effect.seq ((xorR32R32Effect 0x1028d4 2 7 6)) (addR32R32Effect 0x1028d6
    3 2 15)) (addR32R32Effect 0x1028d9 2 2 7)) (movR32R32Effect 0x1028db 2 7 1)) (rolR32Effect
    0x1028dd 3 7 5)) (addR32R32Effect 0x1028e0 2 7 2)) (addR32Imm32Effect 0x1028e2 6 7 0x5a827999))
    (rolR32Effect 0x1028e8 3 13 1)) (leaR32Effect 0x1028eb 4 2 (.sib 6 (some 13) 0 .none)))
    (movR64R64Effect 0x1028ef 9 13)) (rolR32Effect 0x1028f2 3 3 30)) (movR32R32Effect 0x1028f5 2 6
    3)) (xorR32R32Effect 0x1028f7 3 6 8)) (andR32R32Effect 0x1028fa 2 6 1)) (xorR32R32Effect
    0x1028fc 3 6 8)) (addR32R32Effect 0x1028ff 2 6 2)) (movR32R32Effect 0x102901 2 2 7))
    (rolR32Effect 0x102903 3 2 5)) (addR32R32Effect 0x102906 2 2 6)) (addR32Imm32Effect 0x102908 6 2
    0x5a827999)

set_option maxHeartbeats 1600000 in
theorem block019 [Bindings] (boundary : ReturnBoundary)
    (stack input : BitVec 64) (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes019.length → 0x1028d4 + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x1028d4 ∧ FrameData stack input M s ∧
        Write.AllHold s (cut019 stack input H M))
      (codeRange 0x1028d4 bytes019) effect019 := by
  unfold bytes019 at hout ⊢
  sha1_run_begin (xor_r32_r32_effect_step 0x1028d4 0xf7 (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x1028d6 0x44 0xfa
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_effect_step 0x1028d9 0xfa (by decide +kernel))
  sha1_run_then (mov_r32_r32_effect_step 0x1028db 0xcf (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x1028dd 0xc7 0x5 (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_effect_step 0x1028e0 0xd7 (by decide +kernel))
  sha1_run_then (add_r32_imm32_effect_step 0x1028e2 0xc7 0x5a827999 (by decide +kernel)
    (by decide +kernel))
  sha1_run_then (rol_r32_one_rex_effect_step 0x1028e8 0x41 0xc5
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (lea_r32_rex_effect_step 0x1028eb 0x42 (by unfold RexNoWPrefix; decide +kernel) 2
    (.sib 6 (some 13) 0 .none) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r64_r64_effect_step 0x1028ef 0x4d 0xe9 (by unfold RexWPrefix; decide +kernel)
    (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x1028f2 0xc3 0x1e (by decide +kernel)
    (by decide +kernel))
  sha1_run_then (mov_r32_r32_effect_step 0x1028f5 0xde (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x1028f7 0x44 0xc6
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (and_r32_r32_effect_step 0x1028fa 0xce (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x1028fc 0x44 0xc6
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_effect_step 0x1028ff 0xd6 (by decide +kernel))
  sha1_run_then (mov_r32_r32_effect_step 0x102901 0xfa (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x102903 0xc2 0x5 (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_effect_step 0x102906 0xf2 (by decide +kernel))
  sha1_run_then (add_r32_imm32_effect_step 0x102908 0xc2 0x5a827999 (by decide +kernel)
    (by decide +kernel))
  sha1_run_finish [effect019]

def bytes020 : List UInt8 :=
  [0x44, 0x8b, 0x6c, 0x24, 0x4, 0x44, 0x31, 0xed, 0x33, 0x6c, 0x24, 0x50, 0x44, 0x31, 0xe5, 0xd1,
    0xc5, 0x41, 0x1, 0xe8, 0x48, 0x89, 0x6c, 0x24, 0x38, 0xc1, 0xc1, 0x1e, 0x89, 0xce, 0x31, 0xde,
    0x21, 0xfe, 0x31, 0xde, 0x44, 0x1, 0xc6, 0xc1, 0xc7, 0x1e, 0x4c, 0x8b, 0x44, 0x24, 0x20]

set_option maxHeartbeats 800000 in
def effect020 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq ((movR32M32Effect
    0x10290e 13 (.sib 4 none 0 (.d8 0x4)))) (xorR32R32Effect 0x102913 3 5 13)) (xorR32M32LowEffect
    0x102916 5 (.sib 4 none 0 (.d8 0x50)))) (xorR32R32Effect 0x10291a 3 5 12)) (rolR32Effect
    0x10291d 2 5 1)) (addR32R32Effect 0x10291f 3 8 5)) (movM64R64Effect 0x102922 5 (.sib 4 none 0
    (.d8 0x38)))) (rolR32Effect 0x102927 3 1 30)) (movR32R32Effect 0x10292a 2 6 1)) (xorR32R32Effect
    0x10292c 2 6 3)) (andR32R32Effect 0x10292e 2 6 7)) (xorR32R32Effect 0x102930 2 6 3))
    (addR32R32Effect 0x102932 3 6 8)) (rolR32Effect 0x102935 3 7 30)) (movR64M64Effect 0x102938 8
    (.sib 4 none 0 (.d8 0x20)))

set_option maxHeartbeats 1600000 in
theorem block020 [Bindings] (boundary : ReturnBoundary)
    (stack input : BitVec 64) (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes020.length → 0x10290e + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x10290e ∧ FrameData stack input M s ∧
        Write.AllHold s (cut020 stack input H M))
      (codeRange 0x10290e bytes020) effect020 := by
  unfold bytes020 at hout ⊢
  sha1_run_begin (mov_r32_m32_effect_step 0x10290e 0x44 (by unfold RexNoWPrefix; decide +kernel) 5
    (.sib 4 none 0 (.d8 0x4)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102913 0x44 0xed
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_m32_low_effect_step 0x102916 5 (.sib 4 none 0 (.d8 0x50))
    (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x10291a 0x44 0xe5
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_one_effect_step 0x10291d 0xc5 (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x10291f 0x41 0xe8
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m64_r64_effect_step 0x102922 0x48
    (by unfold RexWPrefix; decide +kernel) 5 (.sib 4 none 0 (.d8 0x38)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x102927 0xc1 0x1e (by decide +kernel)
    (by decide +kernel))
  sha1_run_then (mov_r32_r32_effect_step 0x10292a 0xce (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x10292c 0xde (by decide +kernel))
  sha1_run_then (and_r32_r32_effect_step 0x10292e 0xfe (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x102930 0xde (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x102932 0x44 0xc6
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x102935 0xc7 0x1e (by decide +kernel)
    (by decide +kernel))
  sha1_run_then (mov_r64_m64_effect_step 0x102938 0x4c (by unfold RexWPrefix; decide +kernel) 0
    (.sib 4 none 0 (.d8 0x20)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_finish [effect020]

def bytes023 : List UInt8 :=
  [0x41, 0x31, 0xdd, 0x4c, 0x89, 0x4c, 0x24, 0x58, 0x45, 0x31, 0xcd, 0x41, 0xd1, 0xc5, 0x31, 0xd5,
    0x44, 0x1, 0xe9, 0x44, 0x89, 0x6c, 0x24, 0x4, 0x1, 0xe9, 0x48, 0x89, 0xfe, 0x33, 0x34, 0x24,
    0x33, 0x74, 0x24, 0x30, 0x44, 0x31, 0xd6, 0xd1, 0xc6, 0x49, 0x89, 0xf2, 0x89, 0xc6, 0xc1, 0xc6,
    0x5, 0xc1, 0xc2, 0x1e, 0x1, 0xf1, 0x81, 0xc1, 0xa1, 0xeb, 0xd9, 0x6e]

set_option maxHeartbeats 800000 in
def effect023 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    (Effect.seq (Effect.seq ((xorR32R32Effect 0x1029ae 3 13 3)) (movM64R64Effect 0x1029b1 9 (.sib 4
    none 0 (.d8 0x58)))) (xorR32R32Effect 0x1029b6 3 13 9)) (rolR32Effect 0x1029b9 3 13 1))
    (xorR32R32Effect 0x1029bc 2 5 2)) (addR32R32Effect 0x1029be 3 1 13)) (movM32R32Effect 0x1029c1
    13 (.sib 4 none 0 (.d8 0x4)))) (addR32R32Effect 0x1029c6 2 1 5)) (movR64R64Effect 0x1029c8 6 7))
    (xorR32M32LowEffect 0x1029cb 6 (.sib 4 none 0 .none))) (xorR32M32LowEffect 0x1029ce 6 (.sib 4
    none 0 (.d8 0x30)))) (xorR32R32Effect 0x1029d2 3 6 10)) (rolR32Effect 0x1029d5 2 6 1))
    (movR64R64Effect 0x1029d7 10 6)) (movR32R32Effect 0x1029da 2 6 0)) (rolR32Effect 0x1029dc 3 6
    5)) (rolR32Effect 0x1029df 3 2 30)) (addR32R32Effect 0x1029e2 2 1 6)) (addR32Imm32Effect
    0x1029e4 6 1 0x6ed9eba1)

set_option maxHeartbeats 1600000 in
theorem block023 [Bindings] (boundary : ReturnBoundary)
    (stack input : BitVec 64) (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes023.length → 0x1029ae + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x1029ae ∧ FrameData stack input M s ∧
        Write.AllHold s (cut023 stack input H M))
      (codeRange 0x1029ae bytes023) effect023 := by
  unfold bytes023 at hout ⊢
  sha1_run_begin (xor_r32_r32_rex_effect_step 0x1029ae 0x41 0xdd
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m64_r64_effect_step 0x1029b1 0x4c
    (by unfold RexWPrefix; decide +kernel) 1 (.sib 4 none 0 (.d8 0x58)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x1029b6 0x45 0xcd
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_one_rex_effect_step 0x1029b9 0x41 0xc5
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x1029bc 0xd5 (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x1029be 0x44 0xe9
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m32_r32_effect_step 0x1029c1 0x44
    (by unfold RexNoWPrefix; decide +kernel) 5 (.sib 4 none 0 (.d8 0x4)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_effect_step 0x1029c6 0xe9 (by decide +kernel))
  sha1_run_then (mov_r64_r64_effect_step 0x1029c8 0x48 0xfe (by unfold RexWPrefix; decide +kernel)
    (by decide +kernel))
  sha1_run_then (xor_r32_m32_low_effect_step 0x1029cb 6 (.sib 4 none 0 .none) (by decide +kernel)
    (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_m32_low_effect_step 0x1029ce 6 (.sib 4 none 0 (.d8 0x30))
    (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x1029d2 0x44 0xd6
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_one_effect_step 0x1029d5 0xc6 (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r64_r64_effect_step 0x1029d7 0x49 0xf2 (by unfold RexWPrefix; decide +kernel)
    (by decide +kernel))
  sha1_run_then (mov_r32_r32_effect_step 0x1029da 0xc6 (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x1029dc 0xc6 0x5 (by decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x1029df 0xc2 0x1e (by decide +kernel)
    (by decide +kernel))
  sha1_run_then (add_r32_r32_effect_step 0x1029e2 0xf1 (by decide +kernel))
  sha1_run_then (add_r32_imm32_effect_step 0x1029e4 0xc1 0x6ed9eba1 (by decide +kernel)
    (by decide +kernel))
  sha1_run_finish [effect023]

def bytes024 : List UInt8 :=
  [0x89, 0xce, 0xc1, 0xc6, 0x5, 0x43, 0x8d, 0x3c, 0x2, 0x4c, 0x89, 0x54, 0x24, 0x28, 0x41, 0x31,
    0xd0, 0x41, 0x31, 0xc0, 0x44, 0x3, 0x44, 0x24, 0xc, 0x44, 0x1, 0xc6, 0x81, 0xc6, 0xa1, 0xeb,
    0xd9, 0x6e, 0xc1, 0xc0, 0x1e, 0x41, 0x89, 0xc0, 0x41, 0x31, 0xd0, 0x41, 0x31, 0xc8, 0x41, 0x1,
    0xf8, 0xc1, 0xc1, 0x1e, 0x48, 0x8b, 0x7c, 0x24, 0x18]

set_option maxHeartbeats 800000 in
def effect024 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    ((movR32R32Effect 0x1029ea 2 6 1)) (rolR32Effect 0x1029ec 3 6 5)) (leaR32Effect 0x1029ef 4 7
    (.sib 10 (some 8) 0 .none))) (movM64R64Effect 0x1029f3 10 (.sib 4 none 0 (.d8 0x28))))
    (xorR32R32Effect 0x1029f8 3 8 2)) (xorR32R32Effect 0x1029fb 3 8 0)) (addR32M32Effect 0x1029fe 5
    8 (.sib 4 none 0 (.d8 0xc)))) (addR32R32Effect 0x102a03 3 6 8)) (addR32Imm32Effect 0x102a06 6 6
    0x6ed9eba1)) (rolR32Effect 0x102a0c 3 0 30)) (movR32R32Effect 0x102a0f 3 8 0)) (xorR32R32Effect
    0x102a12 3 8 2)) (xorR32R32Effect 0x102a15 3 8 1)) (addR32R32Effect 0x102a18 3 8 7))
    (rolR32Effect 0x102a1b 3 1 30)) (movR64M64Effect 0x102a1e 7 (.sib 4 none 0 (.d8 0x18)))

set_option maxHeartbeats 1600000 in
theorem block024 [Bindings] (boundary : ReturnBoundary)
    (stack input : BitVec 64) (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes024.length → 0x1029ea + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x1029ea ∧ FrameData stack input M s ∧
        Write.AllHold s (cut024 stack input H M))
      (codeRange 0x1029ea bytes024) effect024 := by
  unfold bytes024 at hout ⊢
  sha1_run_begin (mov_r32_r32_effect_step 0x1029ea 0xce (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x1029ec 0xc6 0x5 (by decide +kernel) (by decide +kernel))
  sha1_run_then (lea_r32_rex_effect_step 0x1029ef 0x43 (by unfold RexNoWPrefix; decide +kernel) 7
    (.sib 10 (some 8) 0 .none) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m64_r64_effect_step 0x1029f3 0x4c
    (by unfold RexWPrefix; decide +kernel) 2 (.sib 4 none 0 (.d8 0x28)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x1029f8 0x41 0xd0
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x1029fb 0x41 0xc0
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_m32_rex_effect_step 0x1029fe 0x44 (by unfold RexNoWPrefix; decide +kernel)
    0 (.sib 4 none 0 (.d8 0xc)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x102a03 0x44 0xc6
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_imm32_effect_step 0x102a06 0xc6 0x6ed9eba1 (by decide +kernel)
    (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x102a0c 0xc0 0x1e (by decide +kernel)
    (by decide +kernel))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x102a0f 0x41 0xc0
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102a12 0x41 0xd0
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102a15 0x41 0xc8
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x102a18 0x41 0xf8
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x102a1b 0xc1 0x1e (by decide +kernel)
    (by decide +kernel))
  sha1_run_then (mov_r64_m64_effect_step 0x102a1e 0x48 (by unfold RexWPrefix; decide +kernel) 7
    (.sib 4 none 0 (.d8 0x18)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_finish [effect024]

def bytes025 : List UInt8 :=
  [0x41, 0x31, 0xfe, 0x44, 0x31, 0xdf, 0x44, 0x31, 0xcf, 0x44, 0x31, 0xd7, 0xd1, 0xc7, 0x49, 0x89,
    0xf9, 0x48, 0x89, 0x7c, 0x24, 0x18, 0x89, 0xf7, 0xc1, 0xc7, 0x1e, 0x89, 0xfd, 0x31, 0xcd, 0x41,
    0x1, 0xc9, 0x31, 0xc1, 0x31, 0xf1, 0xc1, 0xc6, 0x5, 0x44, 0x1, 0xc6, 0x81, 0xc6, 0xa1, 0xeb,
    0xd9, 0x6e]

set_option maxHeartbeats 800000 in
def effect025 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    ((xorR32R32Effect 0x102a23 3 14 7)) (xorR32R32Effect 0x102a26 3 7 11)) (xorR32R32Effect 0x102a29
    3 7 9)) (xorR32R32Effect 0x102a2c 3 7 10)) (rolR32Effect 0x102a2f 2 7 1)) (movR64R64Effect
    0x102a31 9 7)) (movM64R64Effect 0x102a34 7 (.sib 4 none 0 (.d8 0x18)))) (movR32R32Effect
    0x102a39 2 7 6)) (rolR32Effect 0x102a3b 3 7 30)) (movR32R32Effect 0x102a3e 2 5 7))
    (xorR32R32Effect 0x102a40 2 5 1)) (addR32R32Effect 0x102a42 3 9 1)) (xorR32R32Effect 0x102a45 2
    1 0)) (xorR32R32Effect 0x102a47 2 1 6)) (rolR32Effect 0x102a49 3 6 5)) (addR32R32Effect 0x102a4c
    3 6 8)) (addR32Imm32Effect 0x102a4f 6 6 0x6ed9eba1)

set_option maxHeartbeats 1600000 in
theorem block025 [Bindings] (boundary : ReturnBoundary)
    (stack input : BitVec 64) (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes025.length → 0x102a23 + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x102a23 ∧ FrameData stack input M s ∧
        Write.AllHold s (cut025 stack input H M))
      (codeRange 0x102a23 bytes025) effect025 := by
  unfold bytes025 at hout ⊢
  sha1_run_begin (xor_r32_r32_rex_effect_step 0x102a23 0x41 0xfe
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102a26 0x44 0xdf
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102a29 0x44 0xcf
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102a2c 0x44 0xd7
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_one_effect_step 0x102a2f 0xc7 (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r64_r64_effect_step 0x102a31 0x49 0xf9 (by unfold RexWPrefix; decide +kernel)
    (by decide +kernel))
  sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m64_r64_effect_step 0x102a34 0x48
    (by unfold RexWPrefix; decide +kernel) 7 (.sib 4 none 0 (.d8 0x18)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_effect_step 0x102a39 0xf7 (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x102a3b 0xc7 0x1e (by decide +kernel)
    (by decide +kernel))
  sha1_run_then (mov_r32_r32_effect_step 0x102a3e 0xfd (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x102a40 0xcd (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x102a42 0x41 0xc9
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x102a45 0xc1 (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x102a47 0xf1 (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x102a49 0xc6 0x5 (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x102a4c 0x44 0xc6
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_imm32_effect_step 0x102a4f 0xc6 0x6ed9eba1 (by decide +kernel)
    (by decide +kernel))
  sha1_run_finish [effect025]

def bytes026 : List UInt8 :=
  [0x45, 0x31, 0xe6, 0x45, 0x31, 0xee, 0x41, 0xd1, 0xc6, 0x41, 0x89, 0xf0, 0x41, 0xc1, 0xc0, 0x5,
    0x44, 0x1, 0xf2, 0x4c, 0x89, 0x74, 0x24, 0x68, 0x1, 0xca, 0x41, 0x8d, 0xc, 0x10, 0x81, 0xc1,
    0xa1, 0xeb, 0xd9, 0x6e, 0x8b, 0x14, 0x24, 0x4c, 0x8b, 0x44, 0x24, 0x50, 0x44, 0x31, 0xc2, 0x44,
    0x31, 0xfa, 0x4c, 0x8b, 0x5c, 0x24, 0x20, 0x44, 0x31, 0xda]

set_option maxHeartbeats 800000 in
def effect026 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    ((xorR32R32Effect 0x102a55 3 14 12)) (xorR32R32Effect 0x102a58 3 14 13)) (rolR32Effect 0x102a5b
    3 14 1)) (movR32R32Effect 0x102a5e 3 8 6)) (rolR32Effect 0x102a61 4 8 5)) (addR32R32Effect
    0x102a65 3 2 14)) (movM64R64Effect 0x102a68 14 (.sib 4 none 0 (.d8 0x68)))) (addR32R32Effect
    0x102a6d 2 2 1)) (leaR32Effect 0x102a6f 4 1 (.sib 8 (some 2) 0 .none))) (addR32Imm32Effect
    0x102a73 6 1 0x6ed9eba1)) (movR32M32LowEffect 0x102a79 2 (.sib 4 none 0 .none)))
    (movR64M64Effect 0x102a7c 8 (.sib 4 none 0 (.d8 0x50)))) (xorR32R32Effect 0x102a81 3 2 8))
    (xorR32R32Effect 0x102a84 3 2 15)) (movR64M64Effect 0x102a87 11 (.sib 4 none 0 (.d8 0x20))))
    (xorR32R32Effect 0x102a8c 3 2 11)

set_option maxHeartbeats 1600000 in
theorem block026 [Bindings] (boundary : ReturnBoundary)
    (stack input : BitVec 64) (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes026.length → 0x102a55 + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x102a55 ∧ FrameData stack input M s ∧
        Write.AllHold s (cut026 stack input H M))
      (codeRange 0x102a55 bytes026) effect026 := by
  unfold bytes026 at hout ⊢
  sha1_run_begin (xor_r32_r32_rex_effect_step 0x102a55 0x45 0xe6
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102a58 0x45 0xee
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_one_rex_effect_step 0x102a5b 0x41 0xc6
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x102a5e 0x41 0xf0
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_imm8_rex_effect_step 0x102a61 0x41 0xc0 0x5
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x102a65 0x44 0xf2
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m64_r64_effect_step 0x102a68 0x4c
    (by unfold RexWPrefix; decide +kernel) 6 (.sib 4 none 0 (.d8 0x68)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_effect_step 0x102a6d 0xca (by decide +kernel))
  sha1_run_then (lea_r32_rex_effect_step 0x102a6f 0x41 (by unfold RexNoWPrefix; decide +kernel) 1
    (.sib 8 (some 2) 0 .none) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_imm32_effect_step 0x102a73 0xc1 0x6ed9eba1 (by decide +kernel)
    (by decide +kernel))
  sha1_run_then (mov_r32_m32_low_effect_step 0x102a79 2 (.sib 4 none 0 .none) (by decide +kernel)
    (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r64_m64_effect_step 0x102a7c 0x4c (by unfold RexWPrefix; decide +kernel) 0
    (.sib 4 none 0 (.d8 0x50)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102a81 0x44 0xc2
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102a84 0x44 0xfa
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r64_m64_effect_step 0x102a87 0x4c (by unfold RexWPrefix; decide +kernel) 3
    (.sib 4 none 0 (.d8 0x20)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102a8c 0x44 0xda
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_finish [effect026]

private theorem bitVec_and_xor_distrib_right (a b c : BitVec 32) :
    (a ^^^ b) &&& c = a &&& c ^^^ b &&& c := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_xor, Bool.and_xor_distrib_right]

private theorem bitVec_and_xor_distrib_left (a b c : BitVec 32) :
    a &&& (b ^^^ c) = a &&& b ^^^ a &&& c := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_xor, Bool.and_xor_distrib_left]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem genericWords018 {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) {s t : RamState}
    (hA17 : A 17 = (A 16).rotateLeft 5 + (((A 14).rotateLeft 30 ^^^ (A 13).rotateLeft 30) &&& A 15
      ^^^ (A 13).rotateLeft 30) + (A 12).rotateLeft 30 + 0x5a827999 + W 16)
    (hW16 : W 16 = ((W 13 ^^^ W 8 ^^^ W 2 ^^^ W 0)).rotateLeft 1)
    (hW17 : W 17 = ((W 14 ^^^ W 9 ^^^ W 3 ^^^ W 1)).rotateLeft 1)
    (_hs : (Operand.reg 4 : Operand 64).read s = stack)
    (hw : Write.AllHold s (genericCut018 stack input H A W))
    (he : (effect018 s).Holds s t) :
    Write.AllHold t (genericCut019 stack input H A W) := by
  have hfull : ∀ w ∈ (effect018 s).writes, w.Full := by
    apply Effect.Local.full
    unfold effect018
    repeat' first | (solve | x86_local) | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  simp only [genericCut018, Write.AllHold] at hw
  obtain ⟨h1, h2, h3, h5, h6, h7, h10, h12, h13, h14, h15, hM0, hM4, hM16, hM24, hM32, hM40, hM48,
    hM64, hM72, hM80, hM96, hM116, hM120, hM124, hM144, hM152⟩ := hw
  sha1_norm at _hs h1 h2 h3 h5 h6 h7 h10 h12 h13 h14 h15 hM0 hM4 hM16 hM24 hM32 hM40 hM48 hM64 hM72
  sha1_norm at hM80 hM96 hM116 hM120 hM124 hM144 hM152
  simp only [genericCut019, Write.AllHold, hA17, hW16, hW17, ← ho.read_reg, ← ho.read_mem]
  sha1_norm [effect018, _hs, h1, h2, h3, h5, h6, h7, h10, h12, h13, h14, h15, hM0, hM4, hM16, hM24,
    hM32, hM40, hM48, hM64, hM72, hM80, hM96, hM116, hM120, hM124, hM144, hM152,
    read32_memStore64_low,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, leaSpec]
  try sha1_norm [leaSpec, BitVec.setWidth_add, extractLsb'_zero_eq_setWidth,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.shiftLeft_zero, BitVec.add_zero,
    bitVec_and_xor_distrib_left, bitVec_and_xor_distrib_right, BitVec.and_comm, h1, h2, h3, h5, h6,
      h7, h10, h12, h13, h14, h15, hM0, hM4, hM16, hM24, hM32, hM40, hM48, hM64, hM72, hM80, hM96,
      hM116, hM120, hM124, hM144, hM152]
  repeat' apply And.intro
  all_goals ac_rfl

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1600000 in
private theorem genericWords019 {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) {s t : RamState}
    (hA18 : A 18 = (A 17).rotateLeft 5 + (((A 15).rotateLeft 30 ^^^ (A 14).rotateLeft 30) &&& A 16
      ^^^ (A 14).rotateLeft 30) + (A 13).rotateLeft 30 + 0x5a827999 + W 17)
    (hA19 : A 19 = (A 18).rotateLeft 5 + (((A 16).rotateLeft 30 ^^^ (A 15).rotateLeft 30) &&& A 17
      ^^^ (A 15).rotateLeft 30) + (A 14).rotateLeft 30 + 0x5a827999 + W 18)
    (hW18 : W 18 = ((W 15 ^^^ W 10 ^^^ W 4 ^^^ W 2)).rotateLeft 1)
    (_hs : (Operand.reg 4 : Operand 64).read s = stack)
    (hw : Write.AllHold s (genericCut019 stack input H A W))
    (he : (effect019 s).Holds s t) :
    Write.AllHold t (genericCut020 stack input H A W) := by
  have hfull : ∀ w ∈ (effect019 s).writes, w.Full := by
    apply Effect.Local.full
    unfold effect019
    repeat' first | (solve | x86_local) | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  simp only [genericCut019, Write.AllHold] at hw
  obtain ⟨h1, h2, h3, h5, h6, h7, h8, h10, h12, h13, h14, h15, hM0, hM4, hM16, hM24, hM32, hM40,
    hM48, hM64, hM72, hM80, hM96, hM116, hM120, hM124, hM144, hM152⟩ := hw
  sha1_norm at _hs h1 h2 h3 h5 h6 h7 h8 h10 h12 h13 h14 h15 hM0 hM4 hM16 hM24 hM32 hM40 hM48 hM64
  sha1_norm at hM72 hM80 hM96 hM116 hM120 hM124 hM144 hM152
  simp only [genericCut020, Write.AllHold, hA18, hA19, hW18, ← ho.read_reg, ← ho.read_mem]
  sha1_norm [effect019, _hs, h1, h2, h3, h5, h6, h7, h8, h10, h12, h13, h14, h15, hM0, hM4, hM16,
    hM24, hM32, hM40, hM48, hM64, hM72, hM80, hM96, hM116, hM120, hM124, hM144, hM152,
    read32_memStore64_low,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, leaSpec]
  try sha1_norm [leaSpec, BitVec.setWidth_add, extractLsb'_zero_eq_setWidth,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.shiftLeft_zero, BitVec.add_zero,
    bitVec_and_xor_distrib_left, bitVec_and_xor_distrib_right, BitVec.and_comm, h1, h2, h3, h5, h6,
      h7, h8, h10, h12, h13, h14, h15, hM0, hM4, hM16, hM24, hM32, hM40, hM48, hM64, hM72, hM80,
      hM96, hM116, hM120, hM124, hM144, hM152]
  repeat' apply And.intro
  all_goals ac_rfl

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem genericWords020 {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) {s t : RamState}
    (hW19 : W 19 = ((W 16 ^^^ W 11 ^^^ W 5 ^^^ W 3)).rotateLeft 1)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (hw : Write.AllHold s (genericCut020 stack input H A W))
    (he : (effect020 s).Holds s t) :
    Write.AllHold t (genericCut021 stack input H A W) := by
  have hfull : ∀ w ∈ (effect020 s).writes, w.Full := by
    apply Effect.Local.full
    unfold effect020
    repeat' first | (solve | x86_local) | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  simp only [genericCut020, Write.AllHold] at hw
  obtain ⟨h1, h2, h3, h5, h7, h8, h9, h10, h12, h14, h15, hM0, hM4, hM16, hM24, hM32, hM40, hM48,
    hM64, hM72, hM80, hM96, hM116, hM120, hM124, hM144, hM152⟩ := hw
  have lo32 := (read32_of_read64_low
    (s:=s) (a:=stack+32) (v:=(Operand.mem (stack+32) : Operand 64).read s) rfl).symm.trans hM32
  sha1_norm at hs h1 h2 h3 h5 h7 h8 h9 h10 h12 h14 h15 hM0 hM4 hM16 hM24 hM32 hM40 hM48 hM64 hM72
  sha1_norm at hM80 hM96 hM116 hM120 hM124 hM144 hM152 lo32
  simp only [genericCut021, Write.AllHold, hW19, ← ho.read_reg, ← ho.read_mem]
  sha1_norm [effect020, hs, h1, h2, h3, h5, h7, h8, h9, h10, h12, h14, h15, hM0, hM4, hM16, hM24,
    hM32, hM40, hM48, hM64, hM72, hM80, hM96, hM116, hM120, hM124, hM144, hM152, lo32,
    read32_memStore64_low,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, leaSpec]
  try sha1_norm [leaSpec, BitVec.setWidth_add, extractLsb'_zero_eq_setWidth,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.shiftLeft_zero, BitVec.add_zero,
    bitVec_and_xor_distrib_left, bitVec_and_xor_distrib_right, BitVec.and_comm, h1, h2, h3, h5, h7,
      h8, h9, h10, h12, h14, h15, hM0, hM4, hM16, hM24, hM32, hM40, hM48, hM64, hM72, hM80, hM96,
      hM116, hM120, hM124, hM144, hM152, lo32]
  repeat' apply And.intro
  all_goals ac_rfl

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem genericWords023 {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) {s t : RamState}
    (hA22 : A 22 = (A 21).rotateLeft 5 + (A 20 ^^^ (A 19).rotateLeft 30 ^^^ (A 18).rotateLeft 30) +
      (A 17).rotateLeft 30 + 0x6ed9eba1 + W 21)
    (hW21 : W 21 = ((W 18 ^^^ W 13 ^^^ W 7 ^^^ W 5)).rotateLeft 1)
    (hW23 : W 23 = ((W 20 ^^^ W 15 ^^^ W 9 ^^^ W 7)).rotateLeft 1)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (hw : Write.AllHold s (genericCut023 stack input H A W))
    (he : (effect023 s).Holds s t) :
    Write.AllHold t (genericCut024 stack input H A W) := by
  have hfull : ∀ w ∈ (effect023 s).writes, w.Full := by
    apply Effect.Local.full
    unfold effect023
    repeat' first | (solve | x86_local) | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  simp only [genericCut023, Write.AllHold] at hw
  obtain ⟨h0, h1, h2, h3, h5, h7, h8, h9, h10, h11, h12, h13, h14, h15, hM0, hM8, hM12, hM16, hM24,
    hM32, hM48, hM56, hM64, hM72, hM80, hM96, hM116, hM120, hM124, hM144, hM152⟩ := hw
  sha1_norm at hs h0 h1 h2 h3 h5 h7 h8 h9 h10 h11 h12 h13 h14 h15 hM0 hM8 hM12 hM16 hM24 hM32 hM48
  sha1_norm at hM56 hM64 hM72 hM80 hM96 hM116 hM120 hM124 hM144 hM152
  simp only [genericCut024, Write.AllHold, hA22, hW21, hW23, ← ho.read_reg, ← ho.read_mem]
  sha1_norm [effect023, hs, h0, h1, h2, h3, h5, h7, h8, h9, h10, h11, h12, h13, h14, h15, hM0, hM8,
    hM12, hM16, hM24, hM32, hM48, hM56, hM64, hM72, hM80, hM96, hM116, hM120, hM124, hM144, hM152,
    read32_memStore64_low,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, leaSpec]
  try sha1_norm [leaSpec, BitVec.setWidth_add, extractLsb'_zero_eq_setWidth,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.shiftLeft_zero, BitVec.add_zero,
    bitVec_and_xor_distrib_left, bitVec_and_xor_distrib_right, BitVec.and_comm, h0, h1, h2, h3, h5,
      h7, h8, h9, h10, h11, h12, h13, h14, h15, hM0, hM8, hM12, hM16, hM24, hM32, hM48, hM56, hM64,
      hM72, hM80, hM96, hM116, hM120, hM124, hM144, hM152]
  repeat' apply And.intro
  all_goals ac_rfl

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem genericWords024 {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) {s t : RamState}
    (hA23 : A 23 = (A 22).rotateLeft 5 + (A 21 ^^^ (A 20).rotateLeft 30 ^^^ (A 19).rotateLeft 30) +
      (A 18).rotateLeft 30 + 0x6ed9eba1 + W 22)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (hw : Write.AllHold s (genericCut024 stack input H A W))
    (he : (effect024 s).Holds s t) :
    Write.AllHold t (genericCut025 stack input H A W) := by
  have hfull : ∀ w ∈ (effect024 s).writes, w.Full := by
    apply Effect.Local.full
    unfold effect024
    repeat' first | (solve | x86_local) | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  simp only [genericCut024, Write.AllHold] at hw
  obtain ⟨h0, h1, h2, h3, h8, h9, h10, h11, h12, h13, h14, h15, hM0, hM4, hM8, hM12, hM16, hM24,
    hM32, hM48, hM56, hM64, hM72, hM80, hM88, hM96, hM116, hM120, hM124, hM144, hM152⟩ := hw
  have lo24 := (read32_of_read64_low
    (s:=s) (a:=stack+24) (v:=(Operand.mem (stack+24) : Operand 64).read s) rfl).symm.trans hM24
  sha1_norm at hs h0 h1 h2 h3 h8 h9 h10 h11 h12 h13 h14 h15 hM0 hM4 hM8 hM12 hM16 hM24 hM32 hM48
  sha1_norm at hM56 hM64 hM72 hM80 hM88 hM96 hM116 hM120 hM124 hM144 hM152 lo24
  simp only [genericCut025, Write.AllHold, hA23, ← ho.read_reg, ← ho.read_mem]
  sha1_norm [effect024, hs, h0, h1, h2, h3, h8, h9, h10, h11, h12, h13, h14, h15, hM0, hM4, hM8,
    hM12, hM16, hM24, hM32, hM48, hM56, hM64, hM72, hM80, hM88, hM96, hM116, hM120, hM124, hM144,
    hM152, lo24, read32_memStore64_low,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, leaSpec]
  try sha1_norm [leaSpec, BitVec.setWidth_add, extractLsb'_zero_eq_setWidth,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.shiftLeft_zero, BitVec.add_zero,
    bitVec_and_xor_distrib_left, bitVec_and_xor_distrib_right, BitVec.and_comm, h0, h1, h2, h3, h8,
      h9, h10, h11, h12, h13, h14, h15, hM0, hM4, hM8, hM12, hM16, hM24, hM32, hM48, hM56, hM64,
      hM72, hM80, hM88, hM96, hM116, hM120, hM124, hM144, hM152, lo24]
  repeat' apply And.intro
  all_goals ac_rfl

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem genericWords025 {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) {s t : RamState}
    (hA24 : A 24 = (A 23).rotateLeft 5 + (A 22 ^^^ (A 21).rotateLeft 30 ^^^ (A 20).rotateLeft 30) +
      (A 19).rotateLeft 30 + 0x6ed9eba1 + W 23)
    (hW26 : W 26 = ((W 23 ^^^ W 18 ^^^ W 12 ^^^ W 10)).rotateLeft 1)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (hw : Write.AllHold s (genericCut025 stack input H A W))
    (he : (effect025 s).Holds s t) :
    Write.AllHold t (genericCut026 stack input H A W) := by
  have hfull : ∀ w ∈ (effect025 s).writes, w.Full := by
    apply Effect.Local.full
    unfold effect025
    repeat' first | (solve | x86_local) | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  simp only [genericCut025, Write.AllHold] at hw
  obtain ⟨h0, h1, h2, h3, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, hM0, hM4, hM8, hM16, hM32,
    hM40, hM48, hM56, hM64, hM72, hM80, hM88, hM96, hM116, hM120, hM124, hM144, hM152⟩ := hw
  sha1_norm at hs h0 h1 h2 h3 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 hM0 hM4 hM8 hM16 hM32 hM40 hM48
  sha1_norm at hM56 hM64 hM72 hM80 hM88 hM96 hM116 hM120 hM124 hM144 hM152
  simp only [genericCut026, Write.AllHold, hA24, hW26, ← ho.read_reg, ← ho.read_mem]
  sha1_norm [effect025, hs, h0, h1, h2, h3, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, hM0, hM4,
    hM8, hM16, hM32, hM40, hM48, hM56, hM64, hM72, hM80, hM88, hM96, hM116, hM120, hM124, hM144,
    hM152, read32_memStore64_low,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, leaSpec]
  try sha1_norm [leaSpec, BitVec.setWidth_add, extractLsb'_zero_eq_setWidth,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.shiftLeft_zero, BitVec.add_zero,
    bitVec_and_xor_distrib_left, bitVec_and_xor_distrib_right, BitVec.and_comm, h0, h1, h2, h3, h6,
      h7, h8, h9, h10, h11, h12, h13, h14, h15, hM0, hM4, hM8, hM16, hM32, hM40, hM48, hM56, hM64,
      hM72, hM80, hM88, hM96, hM116, hM120, hM124, hM144, hM152]
  repeat' apply And.intro
  all_goals ac_rfl

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
private theorem genericWords026 {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) {s t : RamState}
    (hA25 : A 25 = (A 24).rotateLeft 5 + (A 23 ^^^ (A 22).rotateLeft 30 ^^^ (A 21).rotateLeft 30) +
      (A 20).rotateLeft 30 + 0x6ed9eba1 + W 24)
    (hW24 : W 24 = ((W 21 ^^^ W 16 ^^^ W 10 ^^^ W 8)).rotateLeft 1)
    (hs : (Operand.reg 4 : Operand 64).read s = stack)
    (hw : Write.AllHold s (genericCut026 stack input H A W))
    (he : (effect026 s).Holds s t) :
    Write.AllHold t (genericCut027 stack input H A W) := by
  have hfull : ∀ w ∈ (effect026 s).writes, w.Full := by
    apply Effect.Local.full
    unfold effect026
    repeat' first | (solve | x86_local) | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  simp only [genericCut026, Write.AllHold] at hw
  obtain ⟨h0, h1, h2, h3, h5, h6, h7, h9, h12, h13, h14, h15, hM0, hM4, hM8, hM16, hM24, hM32, hM40,
    hM48, hM56, hM64, hM72, hM80, hM88, hM96, hM116, hM120, hM124, hM144, hM152⟩ := hw
  have lo80 := (read32_of_read64_low
    (s:=s) (a:=stack+80) (v:=(Operand.mem (stack+80) : Operand 64).read s) rfl).symm.trans hM80
  have lo32 := (read32_of_read64_low
    (s:=s) (a:=stack+32) (v:=(Operand.mem (stack+32) : Operand 64).read s) rfl).symm.trans hM32
  sha1_norm at hs h0 h1 h2 h3 h5 h6 h7 h9 h12 h13 h14 h15 hM0 hM4 hM8 hM16 hM24 hM32 hM40 hM48 hM56
  sha1_norm at hM64 hM72 hM80 hM88 hM96 hM116 hM120 hM124 hM144 hM152 lo80 lo32
  simp only [genericCut027, Write.AllHold, hA25, hW24, ← ho.read_reg, ← ho.read_mem]
  sha1_norm [effect026, hs, h0, h1, h2, h3, h5, h6, h7, h9, h12, h13, h14, h15, hM0, hM4, hM8, hM16,
    hM24, hM32, hM40, hM48, hM56, hM64, hM72, hM80, hM88, hM96, hM116, hM120, hM124, hM144, hM152,
    lo80, lo32, read32_memStore64_low,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, leaSpec]
  try sha1_norm [leaSpec, BitVec.setWidth_add, extractLsb'_zero_eq_setWidth,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.shiftLeft_zero, BitVec.add_zero,
    bitVec_and_xor_distrib_left, bitVec_and_xor_distrib_right, BitVec.and_comm, h0, h1, h2, h3, h5,
      h6, h7, h9, h12, h13, h14, h15, hM0, hM4, hM8, hM16, hM24, hM32, hM40, hM48, hM56, hM64, hM72,
      hM80, hM88, hM96, hM116, hM120, hM124, hM144, hM152, lo80, lo32]
  repeat' apply And.intro
  all_goals ac_rfl

theorem effect018_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s) (he : (effect018 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have hfoot : ∀ c ∈ (effect018 s).components, c ∈ [.reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6,
    .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] :=
    by
    unfold effect018
    iterate 17 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [addR32Imm32Effect_components, addR32R32Effect_components, andR32R32Effect_components,
        movR32R32Effect_components, rolR32Effect_components, xorR32R32Effect_components,
       List.mem_cons, List.not_mem_nil, or_false, or_imp, forall_and, forall_eq]
    all_goals sha1_norm
  have ha := he.agrees.mono hfoot
  try rw [hs] at ha
  apply ha.widen
  · intro c hc hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl
    all_goals simp_all (config := {decide := true}) only [scratchComponents, x86_compose]
  · intro address c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl
    all_goals first
      | exact hCov.elim
      | exact scratchComponents_stack (Or.inl (by decide +kernel)) hCov

theorem effect018_rip {s t : RamState} (he : (effect018 s).Holds s t) :
    t.RIP = 0x1028d4 := he.rip.trans (by rfl)
theorem effect019_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s) (he : (effect019 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have hfoot : ∀ c ∈ (effect019 s).components, c ∈ [.reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6,
    .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] :=
    by
    unfold effect019
    iterate 19 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [addR32Imm32Effect_components, addR32R32Effect_components, andR32R32Effect_components,
        leaR32Effect_components, movR32R32Effect_components, movR64R64Effect_components,
        rolR32Effect_components, xorR32R32Effect_components,
       List.mem_cons, List.not_mem_nil, or_false, or_imp, forall_and, forall_eq]
    all_goals sha1_norm
  have ha := he.agrees.mono hfoot
  try rw [hs] at ha
  apply ha.widen
  · intro c hc hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl
    all_goals simp_all (config := {decide := true}) only [scratchComponents, x86_compose]
  · intro address c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl
    all_goals first
      | exact hCov.elim
      | exact scratchComponents_stack (Or.inl (by decide +kernel)) hCov

theorem effect019_rip {s t : RamState} (he : (effect019 s).Holds s t) :
    t.RIP = 0x10290e := he.rip.trans (by rfl)
theorem effect020_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s) (he : (effect020 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have hfoot : ∀ c ∈ (effect020 s).components, c ∈ [.mem ((Operand.reg 4 : Operand 64).read s +
    BitVec.ofNat 64 56) 8, .reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9,
    .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] := by
    unfold effect020
    iterate 14 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [addR32R32Effect_components, andR32R32Effect_components, movM64R64Effect_components,
        movR32M32Effect_components, movR32R32Effect_components, movR64M64Effect_components,
        rolR32Effect_components, xorR32M32LowEffect_components, xorR32R32Effect_components,
       List.mem_cons, List.not_mem_nil, or_false, or_imp, forall_and, forall_eq, or_true]
    all_goals sha1_norm
  have ha := he.agrees.mono hfoot
  try rw [hs] at ha
  apply ha.widen
  · intro c hc hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl
    all_goals simp_all (config := {decide := true}) only [Component.isMem, scratchComponents,
      x86_compose]
  · intro address c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl
    all_goals first
      | exact hCov.elim
      | exact scratchComponents_stack (Or.inl (by decide +kernel)) hCov

theorem effect020_rip {s t : RamState} (he : (effect020 s).Holds s t) :
    t.RIP = 0x10293d := he.rip.trans (by rfl)
theorem effect023_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s) (he : (effect023 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have hfoot : ∀ c ∈ (effect023 s).components, c ∈ [.mem ((Operand.reg 4 : Operand 64).read s +
    BitVec.ofNat 64 88) 8, .mem ((Operand.reg 4 : Operand 64).read s + BitVec.ofNat 64 4) 4, .reg 0,
    .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg
    13, .reg 14, .reg 15, .flags, .rip] := by
    unfold effect023
    iterate 18 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [addR32Imm32Effect_components, addR32R32Effect_components, movM32R32Effect_components,
        movM64R64Effect_components, movR32R32Effect_components, movR64R64Effect_components,
        rolR32Effect_components, xorR32M32LowEffect_components, xorR32R32Effect_components,
       List.mem_cons, List.not_mem_nil, or_false, or_imp, forall_and, forall_eq, or_true]
    all_goals sha1_norm
  have ha := he.agrees.mono hfoot
  try rw [hs] at ha
  apply ha.widen
  · intro c hc hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all (config := {decide := true}) only [Component.isMem, scratchComponents,
      x86_compose]
  · intro address c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hCov.elim
      | exact scratchComponents_stack (Or.inl (by decide +kernel)) hCov

theorem effect023_rip {s t : RamState} (he : (effect023 s).Holds s t) :
    t.RIP = 0x1029ea := he.rip.trans (by rfl)
theorem effect024_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s) (he : (effect024 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have hfoot : ∀ c ∈ (effect024 s).components, c ∈ [.mem ((Operand.reg 4 : Operand 64).read s +
    BitVec.ofNat 64 40) 8, .reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9,
    .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] := by
    unfold effect024
    iterate 15 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [addR32Imm32Effect_components, addR32M32Effect_components, addR32R32Effect_components,
        leaR32Effect_components, movM64R64Effect_components, movR32R32Effect_components,
        movR64M64Effect_components, rolR32Effect_components, xorR32R32Effect_components,
       List.mem_cons, List.not_mem_nil, or_false, or_imp, forall_and, forall_eq, or_true]
    all_goals sha1_norm
  have ha := he.agrees.mono hfoot
  try rw [hs] at ha
  apply ha.widen
  · intro c hc hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl
    all_goals simp_all (config := {decide := true}) only [Component.isMem, scratchComponents,
      x86_compose]
  · intro address c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl
    all_goals first
      | exact hCov.elim
      | exact scratchComponents_stack (Or.inl (by decide +kernel)) hCov

theorem effect024_rip {s t : RamState} (he : (effect024 s).Holds s t) :
    t.RIP = 0x102a23 := he.rip.trans (by rfl)
theorem effect025_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s) (he : (effect025 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have hfoot : ∀ c ∈ (effect025 s).components, c ∈ [.mem ((Operand.reg 4 : Operand 64).read s +
    BitVec.ofNat 64 24) 8, .reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9,
    .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] := by
    unfold effect025
    iterate 16 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [addR32Imm32Effect_components, addR32R32Effect_components, movM64R64Effect_components,
        movR32R32Effect_components, movR64R64Effect_components, rolR32Effect_components,
        xorR32R32Effect_components,
       List.mem_cons, List.not_mem_nil, or_false, or_imp, forall_and, forall_eq, or_true]
    all_goals sha1_norm
  have ha := he.agrees.mono hfoot
  try rw [hs] at ha
  apply ha.widen
  · intro c hc hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl
    all_goals simp_all (config := {decide := true}) only [Component.isMem, scratchComponents,
      x86_compose]
  · intro address c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl
    all_goals first
      | exact hCov.elim
      | exact scratchComponents_stack (Or.inl (by decide +kernel)) hCov

theorem effect025_rip {s t : RamState} (he : (effect025 s).Holds s t) :
    t.RIP = 0x102a55 := he.rip.trans (by rfl)
theorem effect026_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s) (he : (effect026 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have hfoot : ∀ c ∈ (effect026 s).components, c ∈ [.mem ((Operand.reg 4 : Operand 64).read s +
    BitVec.ofNat 64 104) 8, .reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9,
    .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] := by
    unfold effect026
    iterate 15 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [addR32Imm32Effect_components, addR32R32Effect_components, leaR32Effect_components,
        movM64R64Effect_components, movR32M32LowEffect_components, movR32R32Effect_components,
        movR64M64Effect_components, rolR32Effect_components, xorR32R32Effect_components,
       List.mem_cons, List.not_mem_nil, or_false, or_imp, forall_and, forall_eq, or_true]
    all_goals sha1_norm
  have ha := he.agrees.mono hfoot
  try rw [hs] at ha
  apply ha.widen
  · intro c hc hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl
    all_goals simp_all (config := {decide := true}) only [Component.isMem, scratchComponents,
      x86_compose]
  · intro address c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl
    all_goals first
      | exact hCov.elim
      | exact scratchComponents_stack (Or.inl (by decide +kernel)) hCov

theorem effect026_rip {s t : RamState} (he : (effect026 s).Holds s t) :
    t.RIP = 0x102a8f := he.rip.trans (by rfl)

theorem effect018_words {stack input : BitVec 64}
    {H : Vector (BitVec 32) 5} {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s) (hw : Write.AllHold s (cut018 stack input H M))
    (he : (effect018 s).Holds s t) : Write.AllHold t (cut019 stack input H M) := by
  have hCh (x y z : BitVec 32) :
      Standards.NIST.SHA2.SHA256.Ch x y z = (y ^^^ z) &&& x ^^^ z := by
    rw [sha1Ch_eq, BitVec.and_comm x (y ^^^ z), BitVec.xor_comm]
  have hA17 := workingAfter_step_a_values M H 12 (by decide +kernel)
  rw [sha1_f_choice (t := ⟨16, by decide⟩) (by decide), hCh] at hA17
  simp only [Nat.reduceAdd] at hA17
  rw [show K (⟨16, by decide⟩ : Fin 80) = 0x5a827999 by decide +kernel] at hA17
  have hW16 := scheduleWord_recurrence M ⟨16, by decide⟩ (by decide +kernel)
  rw [sha1Rotl_eq_rotateLeft 1 _ (by decide)] at hW16
  have hW17 := scheduleWord_recurrence M ⟨17, by decide⟩ (by decide +kernel)
  rw [sha1Rotl_eq_rotateLeft 1 _ (by decide)] at hW17
  exact genericWords018 (fun k ↦ (workingAfter M H k).a) (scheduleWord M)
    hA17 hW16 hW17 hf.stackPointer hw he

theorem segment018 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x10289b 0x1028d4 cut018 cut019 := by
  have hout : ∀ d : Nat, d ≤ bytes018.length →
      0x10289b + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    apply outsideCompression_ne hOutside <;>
      simp only [bytes018, List.length_cons, List.length_nil] at hd <;>
      simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega
  apply Segment.of_block (fun _ _ _ _ ↦ effect018)
    (fun stack input H M ↦ block018 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64 0x289b) bytes018,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact effect018_rip he
  · intro stack input H M s t _ hf _ he
    exact effect018_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect018_words hf hw he

theorem effect019_words {stack input : BitVec 64}
    {H : Vector (BitVec 32) 5} {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s) (hw : Write.AllHold s (cut019 stack input H M))
    (he : (effect019 s).Holds s t) : Write.AllHold t (cut020 stack input H M) := by
  have hCh (x y z : BitVec 32) :
      Standards.NIST.SHA2.SHA256.Ch x y z = (y ^^^ z) &&& x ^^^ z := by
    rw [sha1Ch_eq, BitVec.and_comm x (y ^^^ z), BitVec.xor_comm]
  have hA18 := workingAfter_step_a_values M H 13 (by decide +kernel)
  rw [sha1_f_choice (t := ⟨17, by decide⟩) (by decide), hCh] at hA18
  simp only [Nat.reduceAdd] at hA18
  rw [show K (⟨17, by decide⟩ : Fin 80) = 0x5a827999 by decide +kernel] at hA18
  have hA19 := workingAfter_step_a_values M H 14 (by decide +kernel)
  rw [sha1_f_choice (t := ⟨18, by decide⟩) (by decide), hCh] at hA19
  simp only [Nat.reduceAdd] at hA19
  rw [show K (⟨18, by decide⟩ : Fin 80) = 0x5a827999 by decide +kernel] at hA19
  have hW18 := scheduleWord_recurrence M ⟨18, by decide⟩ (by decide +kernel)
  rw [sha1Rotl_eq_rotateLeft 1 _ (by decide)] at hW18
  exact genericWords019 (fun k ↦ (workingAfter M H k).a) (scheduleWord M)
    hA18 hA19 hW18 hf.stackPointer hw he

theorem segment019 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x1028d4 0x10290e cut019 cut020 := by
  have hout : ∀ d : Nat, d ≤ bytes019.length →
      0x1028d4 + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    apply outsideCompression_ne hOutside <;>
      simp only [bytes019, List.length_cons, List.length_nil] at hd <;>
      simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega
  apply Segment.of_block (fun _ _ _ _ ↦ effect019)
    (fun stack input H M ↦ block019 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64 0x28d4) bytes019,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact effect019_rip he
  · intro stack input H M s t _ hf _ he
    exact effect019_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect019_words hf hw he

theorem effect020_words {stack input : BitVec 64}
    {H : Vector (BitVec 32) 5} {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s) (hw : Write.AllHold s (cut020 stack input H M))
    (he : (effect020 s).Holds s t) : Write.AllHold t (cut021 stack input H M) := by
  have hW19 := scheduleWord_recurrence M ⟨19, by decide⟩ (by decide +kernel)
  rw [sha1Rotl_eq_rotateLeft 1 _ (by decide)] at hW19
  exact genericWords020 (fun k ↦ (workingAfter M H k).a) (scheduleWord M)
    hW19 hf.stackPointer hw he

theorem segment020 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x10290e 0x10293d cut020 cut021 := by
  have hout : ∀ d : Nat, d ≤ bytes020.length →
      0x10290e + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    apply outsideCompression_ne hOutside <;>
      simp only [bytes020, List.length_cons, List.length_nil] at hd <;>
      simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega
  apply Segment.of_block (fun _ _ _ _ ↦ effect020)
    (fun stack input H M ↦ block020 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64 0x290e) bytes020,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact effect020_rip he
  · intro stack input H M s t _ hf _ he
    exact effect020_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect020_words hf hw he

theorem effect023_words {stack input : BitVec 64}
    {H : Vector (BitVec 32) 5} {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s) (hw : Write.AllHold s (cut023 stack input H M))
    (he : (effect023 s).Holds s t) : Write.AllHold t (cut024 stack input H M) := by
  have hA22 := workingAfter_step_a_values M H 17 (by decide +kernel)
  rw [sha1_f_parity_first (t := ⟨21, by decide⟩) (by decide) (by decide)] at hA22
  simp only [Nat.reduceAdd, Parity] at hA22
  rw [show K (⟨21, by decide⟩ : Fin 80) = 0x6ed9eba1 by decide +kernel] at hA22
  have hW21 := scheduleWord_recurrence M ⟨21, by decide⟩ (by decide +kernel)
  rw [sha1Rotl_eq_rotateLeft 1 _ (by decide)] at hW21
  have hW23 := scheduleWord_recurrence M ⟨23, by decide⟩ (by decide +kernel)
  rw [sha1Rotl_eq_rotateLeft 1 _ (by decide)] at hW23
  exact genericWords023 (fun k ↦ (workingAfter M H k).a) (scheduleWord M)
    hA22 hW21 hW23 hf.stackPointer hw he

theorem segment023 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x1029ae 0x1029ea cut023 cut024 := by
  have hout : ∀ d : Nat, d ≤ bytes023.length →
      0x1029ae + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    apply outsideCompression_ne hOutside <;>
      simp only [bytes023, List.length_cons, List.length_nil] at hd <;>
      simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega
  apply Segment.of_block (fun _ _ _ _ ↦ effect023)
    (fun stack input H M ↦ block023 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64 0x29ae) bytes023,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact effect023_rip he
  · intro stack input H M s t _ hf _ he
    exact effect023_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect023_words hf hw he

theorem effect024_words {stack input : BitVec 64}
    {H : Vector (BitVec 32) 5} {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s) (hw : Write.AllHold s (cut024 stack input H M))
    (he : (effect024 s).Holds s t) : Write.AllHold t (cut025 stack input H M) := by
  have hA23 := workingAfter_step_a_values M H 18 (by decide +kernel)
  rw [sha1_f_parity_first (t := ⟨22, by decide⟩) (by decide) (by decide)] at hA23
  simp only [Nat.reduceAdd, Parity] at hA23
  rw [show K (⟨22, by decide⟩ : Fin 80) = 0x6ed9eba1 by decide +kernel] at hA23
  exact genericWords024 (fun k ↦ (workingAfter M H k).a) (scheduleWord M)
    hA23 hf.stackPointer hw he

theorem segment024 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x1029ea 0x102a23 cut024 cut025 := by
  have hout : ∀ d : Nat, d ≤ bytes024.length →
      0x1029ea + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    apply outsideCompression_ne hOutside <;>
      simp only [bytes024, List.length_cons, List.length_nil] at hd <;>
      simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega
  apply Segment.of_block (fun _ _ _ _ ↦ effect024)
    (fun stack input H M ↦ block024 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64 0x29ea) bytes024,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact effect024_rip he
  · intro stack input H M s t _ hf _ he
    exact effect024_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect024_words hf hw he

theorem effect025_words {stack input : BitVec 64}
    {H : Vector (BitVec 32) 5} {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s) (hw : Write.AllHold s (cut025 stack input H M))
    (he : (effect025 s).Holds s t) : Write.AllHold t (cut026 stack input H M) := by
  have hA24 := workingAfter_step_a_values M H 19 (by decide +kernel)
  rw [sha1_f_parity_first (t := ⟨23, by decide⟩) (by decide) (by decide)] at hA24
  simp only [Nat.reduceAdd, Parity] at hA24
  rw [show K (⟨23, by decide⟩ : Fin 80) = 0x6ed9eba1 by decide +kernel] at hA24
  have hW26 := scheduleWord_recurrence M ⟨26, by decide⟩ (by decide +kernel)
  rw [sha1Rotl_eq_rotateLeft 1 _ (by decide)] at hW26
  exact genericWords025 (fun k ↦ (workingAfter M H k).a) (scheduleWord M)
    hA24 hW26 hf.stackPointer hw he

theorem segment025 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x102a23 0x102a55 cut025 cut026 := by
  have hout : ∀ d : Nat, d ≤ bytes025.length →
      0x102a23 + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    apply outsideCompression_ne hOutside <;>
      simp only [bytes025, List.length_cons, List.length_nil] at hd <;>
      simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega
  apply Segment.of_block (fun _ _ _ _ ↦ effect025)
    (fun stack input H M ↦ block025 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64 0x2a23) bytes025,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact effect025_rip he
  · intro stack input H M s t _ hf _ he
    exact effect025_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect025_words hf hw he

theorem effect026_words {stack input : BitVec 64}
    {H : Vector (BitVec 32) 5} {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s) (hw : Write.AllHold s (cut026 stack input H M))
    (he : (effect026 s).Holds s t) : Write.AllHold t (cut027 stack input H M) := by
  have hA25 := workingAfter_step_a_values M H 20 (by decide +kernel)
  rw [sha1_f_parity_first (t := ⟨24, by decide⟩) (by decide) (by decide)] at hA25
  simp only [Nat.reduceAdd, Parity] at hA25
  rw [show K (⟨24, by decide⟩ : Fin 80) = 0x6ed9eba1 by decide +kernel] at hA25
  have hW24 := scheduleWord_recurrence M ⟨24, by decide⟩ (by decide +kernel)
  rw [sha1Rotl_eq_rotateLeft 1 _ (by decide)] at hW24
  exact genericWords026 (fun k ↦ (workingAfter M H k).a) (scheduleWord M)
    hA25 hW24 hf.stackPointer hw he

theorem segment026 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x102a55 0x102a8f cut026 cut027 := by
  have hout : ∀ d : Nat, d ≤ bytes026.length →
      0x102a55 + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    apply outsideCompression_ne hOutside <;>
      simp only [bytes026, List.length_cons, List.length_nil] at hd <;>
      simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega
  apply Segment.of_block (fun _ _ _ _ ↦ effect026)
    (fun stack input H M ↦ block026 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64 0x2a55) bytes026,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact effect026_rip he
  · intro stack input H M s t _ hf _ he
    exact effect026_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect026_words hf hw he

theorem segments015_026 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x1027f8 0x102a8f cut015 cut027 := by
  have h0 := segment015 boundary hOutside
  have h1 := h0.seq (segment016 boundary hOutside)
  have h2 := h1.seq (segment017 boundary hOutside)
  have h3 := h2.seq (segment018 boundary hOutside)
  have h4 := h3.seq (segment019 boundary hOutside)
  have h5 := h4.seq (segment020 boundary hOutside)
  have h6 := h5.seq (segment021 boundary hOutside)
  have h7 := h6.seq (segment022 boundary hOutside)
  have h8 := h7.seq (segment023 boundary hOutside)
  have h9 := h8.seq (segment024 boundary hOutside)
  have h10 := h9.seq (segment025 boundary hOutside)
  have h11 := h10.seq (segment026 boundary hOutside)
  exact h11

end Sha1.Proofs.Compress.Machine
