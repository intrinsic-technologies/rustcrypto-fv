import P256.Proofs.Program.Code
import X86Proofs.Program.ReadWrite.WriteFrame

namespace P256.Proofs.SignatureFromDer.Parser.ReadSlice

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure ReaderState (reader input : BitVec 64) (len pos : Nat)
    (status : BitVec 8) (s : RamState) : Prop where
  input : (Operand.mem reader : Operand 64).read s = input
  length : (Operand.mem (reader + 8) : Operand 64).read s = BitVec.ofNat 64 len
  limit : (Operand.mem (reader + 24) : Operand 32).read s = BitVec.ofNat 32 len
  position : (Operand.mem (reader + 28) : Operand 32).read s = BitVec.ofNat 32 pos
  status : (Operand.mem (reader + 32) : Operand 8).read s = status

structure ReadSliceSuccess (result input : BitVec 64) (position count : Nat)
    (s : RamState) : Prop where
  discriminant : (Operand.mem result : Operand 32).read s = 2
  input : (Operand.mem (result + 8) : Operand 64).read s = input + BitVec.ofNat 64 position
  length : (Operand.mem (result + 16) : Operand 64).read s = BitVec.ofNat 64 count

theorem ReaderState.of_external_eq {reader input : BitVec 64} {length position : Nat}
    {status : BitVec 8} {s t : RamState} (h : ReaderState reader input length position status s)
    (he : t.external = s.external) : ReaderState reader input length position status t := by
  rcases h with ⟨hi, hl, hm, hp, hs⟩
  constructor
  · change memLoad t.external reader 64 = input
    rw [he]
    exact hi
  · change memLoad t.external (reader + 8) 64 = BitVec.ofNat 64 length
    rw [he]
    exact hl
  · change memLoad t.external (reader + 24) 32 = BitVec.ofNat 32 length
    rw [he]
    exact hm
  · change memLoad t.external (reader + 28) 32 = BitVec.ofNat 32 position
    rw [he]
    exact hp
  · change memLoad t.external (reader + 32) 8 = status
    rw [he]
    exact hs

end P256.Proofs.SignatureFromDer.Parser.ReadSlice
