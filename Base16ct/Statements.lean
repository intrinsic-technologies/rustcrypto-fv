import Base16ct.Spec

set_option warn.sorry false

/-!
# base16ct 1.0.0

Theorems about the compiled machine code of base16ct 1.0.0, one per function. Each says that a
well-formed call returns and produces what the specification in `Base16ct/Spec/Base16.lean`
computes, or the crate's error status; the specification is built on RFC 4648 in
`Standards/RFC/BaseEncodings/`.

| Operation | Theorem | Specification | Standard |
| --- | --- | --- | --- |
| `lower::encode` | `base16ct_lower_encode_writes_lowercase_hex_or_rejects_short_buffer` | `Base16.lowerEncoder` | RFC 4648 §8 |
| `lower::encode_str` | `base16ct_lower_encode_str_writes_lowercase_hex_or_rejects_short_buffer` | `Base16.lowerEncoder` | RFC 4648 §8 |
| `upper::encode` | `base16ct_upper_encode_writes_uppercase_hex_or_rejects_short_buffer` | `Base16.upperEncoder` | RFC 4648 §8 |
| `upper::encode_str` | `base16ct_upper_encode_str_writes_uppercase_hex_or_rejects_short_buffer` | `Base16.upperEncoder` | RFC 4648 §8 |
| `lower::decode` | `base16ct_lower_decode_writes_decoded_bytes_or_rejects` | `Base16.decodeInto Base16.lowerDecoder` | RFC 4648 §8 |
| `upper::decode` | `base16ct_upper_decode_writes_decoded_bytes_or_rejects` | `Base16.decodeInto Base16.upperDecoder` | RFC 4648 §8 |
| `mixed::decode` | `base16ct_mixed_decode_writes_decoded_bytes_or_rejects` | `Base16.decodeInto Base16.mixedDecoder` | RFC 4648 §8, letters in either case |
| `decoded_len` | `base16ct_decoded_len_writes_half_length_or_rejects_odd_length` | `Base16.decodedLength` | RFC 4648 §8 |
| `encoded_len` | `base16ct_encoded_len_writes_twice_length` | `2 * byteLength` | RFC 4648 §8 |

How to read the theorem statements, the deliberate differences from the standards and how to build
the verified binary are in `Base16ct/README.md`.
-/

namespace Base16ct.Statements

open Base16ct.Spec Base16ct.Spec.Program Prelude X86

/--
`lower::encode` (base16ct 1.0.0, `src/lower.rs:22-31`): writes the lowercase hex text of `src`
into `dst`, two characters per byte, high half first.

If `2 * input.size ≤ outputCapacity`, the call returns status 0, the first `2 * input.size` output
bytes are `Base16.lowerEncoder input`, and the length word holds `2 * input.size`. Otherwise it
returns `invalidLengthStatus` and writes nothing outside the stack region.
-/
theorem base16ct_lower_encode_writes_lowercase_hex_or_rejects_short_buffer
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {input : ByteArray} {outputCapacity : Nat}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall base16ctLowerEncode initial input outputCapacity
      (2 * input.size) (2 * input.size ≤ outputCapacity)) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      if 2 * input.size ≤ outputCapacity then
        SuccessfulStatus final ∧
        MemoryWriteFrame initial final
          #v[outputRegion initial (2 * input.size), lengthOutputRegion initial,
            Stack.region initial base16ctLowerEncode.minStackBytes] ∧
        readOutput initial final (2 * input.size) = .ok (Base16.lowerEncoder input) ∧
        readLengthOutput initial final = .ok (BitVec.ofNat 64 (2 * input.size))
      else
        FailureStatus final invalidLengthStatus ∧
        MemoryWriteFrame initial final
          #v[Stack.region initial base16ctLowerEncode.minStackBytes] := by
  sorry

/--
`lower::encode_str` (base16ct 1.0.0, `src/lower.rs:34-36`): as `lower::encode`, but returns the
text as a `&str`.

If `2 * input.size ≤ outputCapacity`, the call returns status 0, the first `2 * input.size` output
bytes are `Base16.lowerEncoder input`, and the length word holds `2 * input.size`. Otherwise it
returns `invalidLengthStatus` and writes nothing outside the stack region.
-/
theorem base16ct_lower_encode_str_writes_lowercase_hex_or_rejects_short_buffer
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {input : ByteArray} {outputCapacity : Nat}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall base16ctLowerEncodeStr initial input outputCapacity
      (2 * input.size) (2 * input.size ≤ outputCapacity)) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      if 2 * input.size ≤ outputCapacity then
        SuccessfulStatus final ∧
        MemoryWriteFrame initial final
          #v[outputRegion initial (2 * input.size), lengthOutputRegion initial,
            Stack.region initial base16ctLowerEncodeStr.minStackBytes] ∧
        readOutput initial final (2 * input.size) = .ok (Base16.lowerEncoder input) ∧
        readLengthOutput initial final = .ok (BitVec.ofNat 64 (2 * input.size))
      else
        FailureStatus final invalidLengthStatus ∧
        MemoryWriteFrame initial final
          #v[Stack.region initial base16ctLowerEncodeStr.minStackBytes] := by
  sorry

/--
`upper::encode` (base16ct 1.0.0, `src/upper.rs:22-31`): writes the uppercase hex text of `src`
into `dst`, two characters per byte, high half first.

If `2 * input.size ≤ outputCapacity`, the call returns status 0, the first `2 * input.size` output
bytes are `Base16.upperEncoder input`, and the length word holds `2 * input.size`. Otherwise it
returns `invalidLengthStatus` and writes nothing outside the stack region.
-/
theorem base16ct_upper_encode_writes_uppercase_hex_or_rejects_short_buffer
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {input : ByteArray} {outputCapacity : Nat}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall base16ctUpperEncode initial input outputCapacity
      (2 * input.size) (2 * input.size ≤ outputCapacity)) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      if 2 * input.size ≤ outputCapacity then
        SuccessfulStatus final ∧
        MemoryWriteFrame initial final
          #v[outputRegion initial (2 * input.size), lengthOutputRegion initial,
            Stack.region initial base16ctUpperEncode.minStackBytes] ∧
        readOutput initial final (2 * input.size) = .ok (Base16.upperEncoder input) ∧
        readLengthOutput initial final = .ok (BitVec.ofNat 64 (2 * input.size))
      else
        FailureStatus final invalidLengthStatus ∧
        MemoryWriteFrame initial final
          #v[Stack.region initial base16ctUpperEncode.minStackBytes] := by
  sorry

/--
`upper::encode_str` (base16ct 1.0.0, `src/upper.rs:34-36`): as `upper::encode`, but returns the
text as a `&str`.

If `2 * input.size ≤ outputCapacity`, the call returns status 0, the first `2 * input.size` output
bytes are `Base16.upperEncoder input`, and the length word holds `2 * input.size`. Otherwise it
returns `invalidLengthStatus` and writes nothing outside the stack region.
-/
theorem base16ct_upper_encode_str_writes_uppercase_hex_or_rejects_short_buffer
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {input : ByteArray} {outputCapacity : Nat}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall base16ctUpperEncodeStr initial input outputCapacity
      (2 * input.size) (2 * input.size ≤ outputCapacity)) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      if 2 * input.size ≤ outputCapacity then
        SuccessfulStatus final ∧
        MemoryWriteFrame initial final
          #v[outputRegion initial (2 * input.size), lengthOutputRegion initial,
            Stack.region initial base16ctUpperEncodeStr.minStackBytes] ∧
        readOutput initial final (2 * input.size) = .ok (Base16.upperEncoder input) ∧
        readLengthOutput initial final = .ok (BitVec.ofNat 64 (2 * input.size))
      else
        FailureStatus final invalidLengthStatus ∧
        MemoryWriteFrame initial final
          #v[Stack.region initial base16ctUpperEncodeStr.minStackBytes] := by
  sorry

/--
`lower::decode` (base16ct 1.0.0, `src/lower.rs:6-8`): decodes hex text over `0`–`9` and `a`–`f`,
two characters per byte, high half first, into `dst`.

If `Base16.decodeInto Base16.lowerDecoder input outputCapacity` is `.ok output`, the call returns
status 0, the first `output.size` output bytes are `output`, and the length word holds
`output.size`. On `.error .invalidLength` it returns `invalidLengthStatus` and writes nothing
outside the stack region. On `.error .invalidEncoding` it returns `invalidEncodingStatus`, and the
first `input.size / 2` output bytes may change to values the theorem leaves unstated: the crate
writes them all before it checks its error flag (`src/lib.rs:112-121`), which its documentation
does not describe.
-/
theorem base16ct_lower_decode_writes_decoded_bytes_or_rejects
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {input : ByteArray} {outputCapacity : Nat}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall base16ctLowerDecode initial input outputCapacity
      (input.size / 2)
      (∃ output, Base16.decodeInto Base16.lowerDecoder input outputCapacity = .ok output)) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      match Base16.decodeInto Base16.lowerDecoder input outputCapacity with
      | .ok output =>
        SuccessfulStatus final ∧
        MemoryWriteFrame initial final
          #v[outputRegion initial output.size, lengthOutputRegion initial,
            Stack.region initial base16ctLowerDecode.minStackBytes] ∧
        readOutput initial final output.size = .ok output ∧
        readLengthOutput initial final = .ok (BitVec.ofNat 64 output.size)
      | .error .invalidLength =>
        FailureStatus final invalidLengthStatus ∧
        MemoryWriteFrame initial final #v[Stack.region initial base16ctLowerDecode.minStackBytes]
      | .error .invalidEncoding =>
        FailureStatus final invalidEncodingStatus ∧
        MemoryWriteFrame initial final
          #v[outputRegion initial (input.size / 2),
            Stack.region initial base16ctLowerDecode.minStackBytes] := by
  sorry

/--
`upper::decode` (base16ct 1.0.0, `src/upper.rs:6-8`): decodes hex text over `0`–`9` and `A`–`F`,
two characters per byte, high half first, into `dst`.

If `Base16.decodeInto Base16.upperDecoder input outputCapacity` is `.ok output`, the call returns
status 0, the first `output.size` output bytes are `output`, and the length word holds
`output.size`. On `.error .invalidLength` it returns `invalidLengthStatus` and writes nothing
outside the stack region. On `.error .invalidEncoding` it returns `invalidEncodingStatus`, and the
first `input.size / 2` output bytes may change to values the theorem leaves unstated: the crate
writes them all before it checks its error flag (`src/lib.rs:112-121`), which its documentation
does not describe.
-/
theorem base16ct_upper_decode_writes_decoded_bytes_or_rejects
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {input : ByteArray} {outputCapacity : Nat}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall base16ctUpperDecode initial input outputCapacity
      (input.size / 2)
      (∃ output, Base16.decodeInto Base16.upperDecoder input outputCapacity = .ok output)) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      match Base16.decodeInto Base16.upperDecoder input outputCapacity with
      | .ok output =>
        SuccessfulStatus final ∧
        MemoryWriteFrame initial final
          #v[outputRegion initial output.size, lengthOutputRegion initial,
            Stack.region initial base16ctUpperDecode.minStackBytes] ∧
        readOutput initial final output.size = .ok output ∧
        readLengthOutput initial final = .ok (BitVec.ofNat 64 output.size)
      | .error .invalidLength =>
        FailureStatus final invalidLengthStatus ∧
        MemoryWriteFrame initial final #v[Stack.region initial base16ctUpperDecode.minStackBytes]
      | .error .invalidEncoding =>
        FailureStatus final invalidEncodingStatus ∧
        MemoryWriteFrame initial final
          #v[outputRegion initial (input.size / 2),
            Stack.region initial base16ctUpperDecode.minStackBytes] := by
  sorry

/--
`mixed::decode` (base16ct 1.0.0, `src/mixed.rs:6-8`): decodes hex text over `0`–`9`, `a`–`f` and
`A`–`F`, mixed freely, two characters per byte, high half first, into `dst`.

If `Base16.decodeInto Base16.mixedDecoder input outputCapacity` is `.ok output`, the call returns
status 0, the first `output.size` output bytes are `output`, and the length word holds
`output.size`. On `.error .invalidLength` it returns `invalidLengthStatus` and writes nothing
outside the stack region. On `.error .invalidEncoding` it returns `invalidEncodingStatus`, and the
first `input.size / 2` output bytes may change to values the theorem leaves unstated: the crate
writes them all before it checks its error flag (`src/lib.rs:112-121`), which its documentation
does not describe.
-/
theorem base16ct_mixed_decode_writes_decoded_bytes_or_rejects
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {input : ByteArray} {outputCapacity : Nat}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall base16ctMixedDecode initial input outputCapacity
      (input.size / 2)
      (∃ output, Base16.decodeInto Base16.mixedDecoder input outputCapacity = .ok output)) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      match Base16.decodeInto Base16.mixedDecoder input outputCapacity with
      | .ok output =>
        SuccessfulStatus final ∧
        MemoryWriteFrame initial final
          #v[outputRegion initial output.size, lengthOutputRegion initial,
            Stack.region initial base16ctMixedDecode.minStackBytes] ∧
        readOutput initial final output.size = .ok output ∧
        readLengthOutput initial final = .ok (BitVec.ofNat 64 output.size)
      | .error .invalidLength =>
        FailureStatus final invalidLengthStatus ∧
        MemoryWriteFrame initial final #v[Stack.region initial base16ctMixedDecode.minStackBytes]
      | .error .invalidEncoding =>
        FailureStatus final invalidEncodingStatus ∧
        MemoryWriteFrame initial final
          #v[outputRegion initial (input.size / 2),
            Stack.region initial base16ctMixedDecode.minStackBytes] := by
  sorry

/--
`decoded_len` (base16ct 1.0.0, `src/lib.rs:88-94`): the number of bytes that hex text of
`byteLength` characters decodes to. It reads only the length of `src`.

If `Base16.decodedLength byteLength` is `some length` (an even `byteLength`), the call returns
status 0 and the length word holds `length`, which is `byteLength / 2`. Otherwise it returns
`invalidLengthStatus` and writes nothing outside the stack region.
-/
theorem base16ct_decoded_len_writes_half_length_or_rejects_odd_length
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {byteLength : Nat}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidLengthCall base16ctDecodedLen initial byteLength (byteLength % 2 = 0)) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      match Base16.decodedLength byteLength with
      | some length =>
        SuccessfulStatus final ∧
        MemoryWriteFrame initial final
          #v[lengthOutputRegion initial, Stack.region initial base16ctDecodedLen.minStackBytes] ∧
        readLengthOutput initial final = .ok (BitVec.ofNat 64 length)
      | none =>
        FailureStatus final invalidLengthStatus ∧
        MemoryWriteFrame initial final
          #v[Stack.region initial base16ctDecodedLen.minStackBytes] := by
  sorry

/--
`encoded_len` (base16ct 1.0.0, `src/lib.rs:98-100`): the length of the hex text for `byteLength`
bytes. It reads only the length of `src`, and the wrapper returns no status.

The length word holds `2 * byteLength`, two characters per byte (RFC 4648 §8).
-/
theorem base16ct_encoded_len_writes_twice_length
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {byteLength : Nat}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidLengthCall base16ctEncodedLen initial byteLength True) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[lengthOutputRegion initial, Stack.region initial base16ctEncodedLen.minStackBytes] ∧
      readLengthOutput initial final = .ok (BitVec.ofNat 64 (2 * byteLength)) := by
  sorry

end Base16ct.Statements
