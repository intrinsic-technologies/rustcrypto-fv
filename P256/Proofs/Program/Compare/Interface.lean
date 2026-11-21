import P256.Proofs.Program.Call
import P256.Proofs.Program.State

namespace P256.Proofs.Program.Compare

open P256.Spec.Program

theorem inProgram_of_mem {a : BitVec 64} {b : UInt8}
    (h : (a,b) ∈ Extracted.programSections.toCodeMap) : Routines.InProgram a :=
  ⟨b, P256.Proofs.Program.programSections_fetchByte_of_mem h⟩


open Prelude X86 X86.Machine X86.UserProcess X86Proofs P256.Spec.Program P256.Spec.Program.Routines

structure CallFrame [Bindings] (s : RamState) (stackBytes : Nat) : Prop where
  ready : ReadyToStep s
  code : CodeIn Extracted.programSections.toCodeMap s
  stack : Stack.Valid s stackBytes
  stackTables : (Stack.region s stackBytes).Avoids PageTableReserved
  stackCode : (Stack.region s stackBytes).Avoids InProgram
  direction : DirectionFlagUnset s
  returnLow : (returnBoundary s).rip.toNat < 2^32

structure CallResult [Bindings] (s t : RamState) (changes : List Component) : Prop where
  ready : ReadyToStep t
  code : CodeIn Extracted.programSections.toCodeMap t
  rip : t.RIP = (returnBoundary s).rip
  rsp : stackPtr t = stackPtr s + 8
  agrees : AgreesExcept changes s t
  calleeSaved : CalleeSavedRegistersUnchanged s t

end P256.Proofs.Program.Compare
