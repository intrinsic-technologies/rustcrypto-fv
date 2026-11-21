import P256.Proofs.SignatureFromDer.Parser.ReadSlice.State
import P256.Proofs.SignatureFromDer.Parser.ReadSlice.Memory

namespace P256.Proofs.SignatureFromDer.Parser.ReadSlice

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Instructions.CrossPageStore

structure SlicePre (reader input result : BitVec 64) (length position count : Nat)
    (s : RamState) : Prop where
  rip : s.RIP = 0x118fa0
  resultArg : s.regValue .rdi = result
  readerArg : s.regValue .rsi = reader
  countArg : s.regValue .rdx = BitVec.ofNat 64 count
  state : ReaderState reader input length position 0 s
  position_le : position ≤ length
  length_lt : length < 2 ^ 32
  count_lt : count < 2 ^ 32
  readable : MemReadable s reader 33
  writePosition : Writable s (reader + 28) 4
  writeStatus : Writable s (reader + 32) 1
  writeResult : Writable s result 24
  separate : RangeApart reader 33 result 24
  readerReturn : RangeApart reader 33 (stackPtr s) 8
  resultReturn : RangeApart result 24 (stackPtr s) 8
  readerCode : ∀ i < 33, ¬ InProgram (reader + BitVec.ofNat 64 i)
  resultCode : ∀ i < 24, ¬ InProgram (result + BitVec.ofNat 64 i)
  returnReadable : MemReadable s (stackPtr s) 8

abbrev sliceComponents (reader result : BitVec 64) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 4, .reg 7, .reg 8, .reg 9, .flags, .rip,
    .mem (reader + 28) 4, .mem (reader + 32) 1, .mem result 24]

structure SlicePost (reader input result : BitVec 64) (length position count : Nat)
    (s t : RamState) : Prop where
  rip : t.RIP = (returnBoundary s).rip
  rsp : stackPtr t = (returnBoundary s).rsp
  rax : t.regValue .rax = result
  agrees : AgreesExcept (sliceComponents reader result) s t
  decoded : if position + count ≤ length then
    ReaderState reader input length (position + count) 0 t ∧
      ReadSliceSuccess result input position count t
    else (Operand.mem result : Operand 32).read t ≠ 2

def ReadSliceContract (bindings : Bindings) : Prop :=
  letI := bindings
  ∀ (boundary : ReturnBoundary), ¬ InProgram boundary.rip →
    ∀ (s : RamState) (reader input result : BitVec 64) (length position count : Nat),
      ReadyToStep s → CodeIn Extracted.programSections.toCodeMap s →
      SlicePre reader input result length position count s →
      (returnBoundary s).rip.toNat < 2 ^ 32 → (returnBoundary s).rip ≠ boundary.rip →
      ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
        CodeIn Extracted.programSections.toCodeMap t ∧ SlicePost reader input result length position count s t

end P256.Proofs.SignatureFromDer.Parser.ReadSlice
