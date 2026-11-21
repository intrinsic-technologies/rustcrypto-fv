import Base16ct.Proofs.Common.RoutineSummary
import Base16ct.Spec.Program

namespace Base16ct.Proofs.Common

open Base16ct.Spec Base16ct.Spec.Program Base16ct.Spec.Program.Extracted
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def decodedLenABI : RoutineABI :=
  { entry := decoded_lenAddress
    argumentRegisters := [⟨7, by decide⟩, ⟨6, by decide⟩, ⟨2, by decide⟩]
    resultRegisters := [⟨0, by decide⟩]
    stackBytes := base16ctDecodedLen.minStackBytes
    callbackTarget := none
    codeBytes := 0x15 }

def decodedLenValues (byteLength : Nat) (even : Bool) : RoutineValues :=
  { output := none
    decoded := none
    length := if even then some (byteLength / 2) else none
    status := if even then none else some (BitVec.setWidth 64 invalidLengthStatus)
    sinkCount := none }

theorem decoded_len_routine_summary_of_parts
    [bindings : Machine.Bindings]
    {initial phase : RamState} {fuel : Nat} {changes : List Component}
    {byteLength : Nat} {even : Bool}
    (hAdvances : Advances (returnBoundary initial) fuel initial phase)
    (hCode : RoutineCodeFacts decodedLenABI programImage (returnBoundary initial)
      initial phase)
    (hContinuation : RoutineContinuation (returnBoundary initial) phase)
    (hWrites : MemoryWriteFrame initial phase
      #v[lengthOutputRegion initial, Stack.region initial base16ctDecodedLen.minStackBytes])
    (hAgrees : AgreesExcept changes initial phase)
    (hCallee : CalleeSavedRegistersUnchanged initial phase)
    (hDirection : DirectionFlagUnset phase)
    (hValue : Prop) (hv : hValue) :
    RoutineSummary decodedLenABI programImage (returnBoundary initial)
      #v[lengthOutputRegion initial, Stack.region initial base16ctDecodedLen.minStackBytes]
      initial phase fuel changes (decodedLenValues byteLength even) hValue := by
  exact ⟨hAdvances, hCode, hContinuation, hWrites, hAgrees, hCallee, hDirection, hv⟩

end Base16ct.Proofs.Common
