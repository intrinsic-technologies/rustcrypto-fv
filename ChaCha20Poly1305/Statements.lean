import ChaCha20Poly1305.Spec

set_option warn.sorry false

/-!
# chacha20poly1305 0.11.0

Theorems about the compiled machine code of chacha20poly1305 0.11.0 at the `ChaCha20Poly1305`
type, one per operation, each after `KeyInit::new` on the caller's key. Each says that a
well-formed call returns and produces what the specification in `ChaCha20Poly1305/Spec/AEAD.lean`
computes; the specification is built on RFC 8439 in `Standards/RFC/ChaCha20Poly1305/`.

| Operation | Theorem | Specification | Standard |
| --- | --- | --- | --- |
| `Aead::encrypt` | `chacha20poly1305_encrypt_writes_ciphertext_with_tag` | `AEAD.encryptWithTag` | RFC 8439 §2.8 |
| `Aead::decrypt` | `chacha20poly1305_decrypt_writes_plaintext_or_rejects_tag` | `AEAD.decryptWithTag` | RFC 8439 §2.8 |
| `AeadInOut::encrypt_in_place` | `chacha20poly1305_encrypt_in_place_writes_ciphertext_with_tag_or_rejects_buffer_without_room` | `AEAD.encryptWithTag`, `AEAD.encryptWithoutTag` | RFC 8439 §2.8 |
| `AeadInOut::decrypt_in_place` | `chacha20poly1305_decrypt_in_place_writes_plaintext_or_rejects_tag` | `AEAD.decryptWithTag` | RFC 8439 §2.8 |

How to read the theorem statements and how to build the verified binary are in
`ChaCha20Poly1305/README.md`.
-/

namespace ChaCha20Poly1305.Statements

open ChaCha20Poly1305.Spec ChaCha20Poly1305.Spec.Program Standards.RFC.ChaCha20Poly1305 Prelude X86

/--
`Aead::encrypt` (aead 0.6.1, `src/lib.rs:195-205`), after `KeyInit::new` (chacha20poly1305
0.11.0, `src/lib.rs:240-246`): encrypts the message `plaintext` (Rust `plaintext.msg`) into a new
`Vec` and appends the 16-byte Poly1305 tag of `associatedData` (`plaintext.aad`) and the
ciphertext.

The call returns and the `plaintext.size + 16` bytes of the output, as `readOutput` reads them, are
`AEAD.encryptWithTag associatedData key nonce plaintext`. It has no failure branch: the crate's
length check (chacha20poly1305 0.11.0, `src/cipher.rs:58`) passes every message below 4 GiB, so no
status is stated, though the wrapper returns 0. The heap bytes it allocates (`heapRegion`) and the
allocator's state may change.
-/
theorem chacha20poly1305_encrypt_writes_ciphertext_with_tag
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {key : Vector UInt8 32} {nonce : Vector UInt8 12}
    {associatedData plaintext : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall encrypt initial [key, nonce, associatedData, plaintext]) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[outputRegion encrypt initial,
          heapRegion encrypt initial, allocatorStateRegion,
          Stack.region initial encrypt.minStackBytes] ∧
      readOutput encrypt initial final =
        .ok (AEAD.encryptWithTag associatedData key nonce plaintext) := by
  sorry

/--
`Aead::decrypt` (aead 0.6.1, `src/lib.rs:207-216`), after `KeyInit::new` (chacha20poly1305
0.11.0, `src/lib.rs:240-246`): takes the last 16 bytes of `ciphertextWithTag` (Rust
`ciphertext.msg`) as the tag and, only if it matches, decrypts the bytes before it into a new
`Vec`; `associatedData` is `ciphertext.aad`.

If `AEAD.decryptWithTag associatedData key nonce ciphertextWithTag` gives a plaintext, the call
returns status 0 and the `ciphertextWithTag.size - 16` bytes of the output, as `readOutput` reads
them, are that plaintext. Otherwise (an input shorter than 16 bytes, or a tag that does not match)
it returns `aeadErrorStatus` and leaves the output untouched. Either way the heap bytes
(`heapRegion`) and the allocator's state may change: a rejected call still copies its input to the
heap.
-/
theorem chacha20poly1305_decrypt_writes_plaintext_or_rejects_tag
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {key : Vector UInt8 32} {nonce : Vector UInt8 12}
    {associatedData ciphertextWithTag : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall decrypt initial [key, nonce, associatedData, ciphertextWithTag]) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      match AEAD.decryptWithTag associatedData key nonce ciphertextWithTag with
      | some plaintext =>
        SuccessfulStatus final ∧
        MemoryWriteFrame initial final
          #v[outputRegion decrypt initial,
            heapRegion decrypt initial, allocatorStateRegion,
            Stack.region initial decrypt.minStackBytes] ∧
        readOutput decrypt initial final = .ok plaintext
      | none =>
        FailureStatus final aeadErrorStatus ∧
        MemoryWriteFrame initial final
          #v[heapRegion decrypt initial, allocatorStateRegion,
            Stack.region initial decrypt.minStackBytes] := by
  sorry

/--
`AeadInOut::encrypt_in_place` (aead 0.6.1, `src/lib.rs:258-282`), after `KeyInit::new`
(chacha20poly1305 0.11.0, `src/lib.rs:240-246`): encrypts the message in the buffer where it lies,
then appends the 16-byte tag, or returns `Error` if the buffer cannot grow by 16 bytes.

If `hasRoom encryptInPlace initial` (`plaintext.size + 16` is at most the buffer's capacity), the
call returns status 0 and the buffer, as `readOutput` reads it, starts with
`AEAD.encryptWithTag associatedData key nonce plaintext`. Otherwise it returns `aeadErrorStatus`
and the buffer starts with the ciphertext alone, `AEAD.encryptWithoutTag associatedData key nonce
plaintext`: aead encrypts before it appends the tag (`src/lib.rs:276-278`), and its docs leave the
buffer's contents on this error unspecified. Below 4 GiB this is the only failure.
-/
theorem chacha20poly1305_encrypt_in_place_writes_ciphertext_with_tag_or_rejects_buffer_without_room
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {key : Vector UInt8 32} {nonce : Vector UInt8 12}
    {associatedData plaintext : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall encryptInPlace initial [key, nonce, associatedData, plaintext]) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      if hasRoom encryptInPlace initial then
        SuccessfulStatus final ∧
        MemoryWriteFrame initial final
          #v[outputRegion encryptInPlace initial,
            Stack.region initial encryptInPlace.minStackBytes] ∧
        readOutput encryptInPlace initial final =
          .ok (AEAD.encryptWithTag associatedData key nonce plaintext)
      else
        FailureStatus final aeadErrorStatus ∧
        MemoryWriteFrame initial final
          #v[outputRegion encryptInPlace initial,
            Stack.region initial encryptInPlace.minStackBytes] ∧
        readOutput encryptInPlace initial final =
          .ok (AEAD.encryptWithoutTag associatedData key nonce plaintext) := by
  sorry

/--
`AeadInOut::decrypt_in_place` (aead 0.6.1, `src/lib.rs:292-316`), after `KeyInit::new`
(chacha20poly1305 0.11.0, `src/lib.rs:240-246`): takes the last 16 bytes of the buffer as the tag
and, only if it matches, decrypts the bytes before it in place and shortens the buffer to them.

If `AEAD.decryptWithTag associatedData key nonce ciphertextWithTag` gives a plaintext, the call
returns status 0 and the first `ciphertextWithTag.size - 16` bytes of the buffer, as `readOutput`
reads them, are that plaintext; the tag bytes after them are unchanged. Otherwise (an input shorter
than 16 bytes, or a tag that does not match) it returns `aeadErrorStatus` and only the stack may
change.
-/
theorem chacha20poly1305_decrypt_in_place_writes_plaintext_or_rejects_tag
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {key : Vector UInt8 32} {nonce : Vector UInt8 12}
    {associatedData ciphertextWithTag : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall decryptInPlace initial [key, nonce, associatedData, ciphertextWithTag]) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      match AEAD.decryptWithTag associatedData key nonce ciphertextWithTag with
      | some plaintext =>
        SuccessfulStatus final ∧
        MemoryWriteFrame initial final
          #v[outputRegion decryptInPlace initial,
            Stack.region initial decryptInPlace.minStackBytes] ∧
        readOutput decryptInPlace initial final = .ok plaintext
      | none =>
        FailureStatus final aeadErrorStatus ∧
        MemoryWriteFrame initial final
          #v[Stack.region initial decryptInPlace.minStackBytes] := by
  sorry

end ChaCha20Poly1305.Statements
