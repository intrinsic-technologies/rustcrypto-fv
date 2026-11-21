import Base16ct.Proofs.Base16ctUpperDecodeCorrect.Model

namespace Base16ct.Proofs.Base16ctUpperDecodeCorrect

open Prelude X86 Base16ct.Spec.Program

open Base16ct.Spec.Base16 (Error)

abbrev ValidCall (routine : Routine) (s : Machine.RamState) (input : List UInt8)
    (capacity : Nat) (lengthWritten : Prop) : Prop :=
  Base16ct.Spec.Program.ValidCall routine s input.toByteArray capacity (input.length / 2) lengthWritten

def pairDecodeResult (alphabets : List RFC4648.Alphabet) (input : List UInt8)
    (outputCapacity : Nat) : Except Error (List UInt8) :=
  if input.length % 2 ≠ 0 ∨ outputCapacity < input.length / 2 then .error .invalidLength
  else match RFC4648.decode alphabets input with
    | some output => .ok output
    | none => .error .invalidEncoding

def readOutput (initial final : Machine.RamState) (length : Nat) :
    Except Machine.Fault (List UInt8) :=
  let region := outputRegion initial length
  (List.range length).mapM fun j =>
    let address := BitVec.ofNat 64 (region.start + j)
    match final.external[address]? with
    | some byte => .ok byte
    | none => .error (.unmappedMemory address)

theorem readOutput_eq (initial final : Machine.RamState) (length : Nat) :
    Base16ct.Spec.Program.readOutput initial final length =
      (readOutput initial final length).map List.toByteArray := by
  simp only [Base16ct.Spec.Program.readOutput, readOutput]
  cases (List.range length).mapM (fun j =>
    let address := BitVec.ofNat 64 ((outputRegion initial length).start + j)
    match final.external[address]? with
    | some byte => (Except.ok byte : Except Machine.Fault UInt8)
    | none => .error (.unmappedMemory address)) with
  | error error => rfl
  | ok bytes =>
    change (Except.ok (ByteArray.mk bytes.toArray) : Except Machine.Fault ByteArray) =
      Except.ok bytes.toByteArray
    congr 1
    apply ByteArray.ext
    simp only [List.data_toByteArray]

def CallComputes (routine : Routine)
    (resultOf : List UInt8 → Nat → Except Error (List UInt8)) : Prop :=
  ∀ [bindings : Machine.Bindings] {initial : Machine.RamState} {input : List UInt8}
    {outputCapacity : Nat}
    (_hBindings : MachineRamUnitStrideDecodable bindings initial)
    (_hMachine : SupportedIntegerMachineState bindings.processor initial)
    (_hCall : ValidCall routine initial input outputCapacity
      (∃ output, resultOf input outputCapacity = .ok output)),
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      match resultOf input outputCapacity with
      | .ok output =>
        SuccessfulStatus final ∧
        MemoryWriteFrame initial final
          #v[outputRegion initial output.length, lengthOutputRegion initial,
            Stack.region initial routine.minStackBytes] ∧
        Base16ct.Spec.Program.readOutput initial final output.length = .ok output.toByteArray ∧
        readLengthOutput initial final = .ok (BitVec.ofNat 64 output.length)
      | .error .invalidLength =>
        FailureStatus final invalidLengthStatus ∧
        MemoryWriteFrame initial final #v[Stack.region initial routine.minStackBytes]
      | .error .invalidEncoding =>
        FailureStatus final invalidEncodingStatus ∧
        MemoryWriteFrame initial final
          #v[outputRegion initial (input.length / 2),
            Stack.region initial routine.minStackBytes]

end Base16ct.Proofs.Base16ctUpperDecodeCorrect
