import AesGcm.Spec

set_option warn.sorry false

/-!
# aes-gcm 0.11.1

Theorems about the compiled machine code of aes-gcm 0.11.1's `Aes128Gcm` and `Aes256Gcm`, one per
operation and type, each after `KeyInit::new` on the caller's key. Each says that a well-formed call
returns and produces what the specification in `AesGcm/Spec/GCM.lean` computes; the specification is
built on NIST SP 800-38D (GCM) and FIPS 197-upd1 (AES) in `Standards/NIST/`.

| Operation | Theorem | Specification | Standard |
| --- | --- | --- | --- |
| `Aes128Gcm`: `AeadInOut::encrypt_in_place` | `aes128gcm_encrypt_in_place_writes_ciphertext_and_tag_or_fails_without_room` | `GCM.ciphertextAndTag .aes128` | SP 800-38D §7.1 |
| `Aes128Gcm`: `AeadInOut::decrypt_in_place` | `aes128gcm_decrypt_in_place_writes_plaintext_or_rejects` | `GCM.authenticPlaintextOfCiphertextWithTag .aes128` | SP 800-38D §7.2 |
| `Aes256Gcm`: `AeadInOut::encrypt_in_place` | `aes256gcm_encrypt_in_place_writes_ciphertext_and_tag_or_fails_without_room` | `GCM.ciphertextAndTag .aes256` | SP 800-38D §7.1 |
| `Aes256Gcm`: `AeadInOut::decrypt_in_place` | `aes256gcm_decrypt_in_place_writes_plaintext_or_rejects` | `GCM.authenticPlaintextOfCiphertextWithTag .aes256` | SP 800-38D §7.2 |

How to read the theorem statements and how to build the verified binary are in
`AesGcm/README.md`.
-/

namespace AesGcm.Statements

open AesGcm.Spec AesGcm.Spec.Program Prelude X86

/--
`AeadInOut::encrypt_in_place` (aead 0.6.1, `src/lib.rs:258-282`) for `Aes128Gcm`, after
`KeyInit::new` (aes-gcm 0.11.1, `src/lib.rs:217-219`): encrypts the plaintext with AES-128-GCM
where it lies in the buffer, then appends the 16-byte tag.

When `GCM.ciphertextAndTag .aes128 key nonce associatedData plaintext` gives
`some (ciphertext, tag)` and `plaintext.size + 16 ≤ capacity`, the call returns status 0 and the
buffer, as `InPlace.readOutput` reads it, starts with the ciphertext then the tag. With less room it
returns status 1 and the buffer starts with the ciphertext alone: the crate encrypts first and then
fails to grow the buffer. When the specification gives `none` (a plaintext over `P_MAX` or
associated data over `A_MAX`, which no valid call reaches), it returns status 1 and only the stack
may change.
-/
theorem aes128gcm_encrypt_in_place_writes_ciphertext_and_tag_or_fails_without_room
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {key : Vector UInt8 16} {nonce : Vector UInt8 12}
    {associatedData plaintext : ByteArray} {capacity : Nat}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : InPlace.ValidCapacityCall aes128gcmEncryptInPlace initial key nonce
      associatedData plaintext capacity) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      match GCM.ciphertextAndTag .aes128 key nonce associatedData plaintext with
      | some (ciphertext, tag) =>
        if plaintext.size + 16 ≤ capacity then
          SuccessfulStatus final ∧
          MemoryWriteFrame initial final
            #v[InPlace.outputRegion initial (plaintext.size + 16),
              Stack.region initial aes128gcmEncryptInPlace.minStackBytes 16] ∧
          InPlace.readOutput initial final (plaintext.size + 16) =
            .ok (ciphertext ++ ⟨tag.toArray⟩)
        else
          FailureStatus final 1 ∧
          MemoryWriteFrame initial final
            #v[InPlace.outputRegion initial plaintext.size,
              Stack.region initial aes128gcmEncryptInPlace.minStackBytes 16] ∧
          InPlace.readOutput initial final plaintext.size = .ok ciphertext
      | none =>
        FailureStatus final 1 ∧
        MemoryWriteFrame initial final
          #v[Stack.region initial aes128gcmEncryptInPlace.minStackBytes 16] := by
  sorry

/--
`AeadInOut::decrypt_in_place` (aead 0.6.1, `src/lib.rs:292-316`) for `Aes128Gcm`, after
`KeyInit::new` (aes-gcm 0.11.1, `src/lib.rs:217-219`): checks the 16-byte tag at the end of the
buffer with AES-128-GCM and, only if it matches, decrypts the rest where it lies and cuts the
buffer to the plaintext.

When `GCM.authenticPlaintextOfCiphertextWithTag .aes128 key nonce associatedData sealed` gives
`some plaintext`, the call returns status 0 and the first `sealed.size - 16` bytes of the buffer, as
`InPlace.readOutput` reads them, are `plaintext`; the tag after them is unchanged. Otherwise,
including when the buffer holds fewer than 16 bytes, it returns status 1 and only the stack may
change.
-/
theorem aes128gcm_decrypt_in_place_writes_plaintext_or_rejects
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {key : Vector UInt8 16} {nonce : Vector UInt8 12}
    {associatedData sealed : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : InPlace.ValidCall aes128gcmDecryptInPlace initial key nonce
      associatedData sealed sealed.size sealed.size) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      match GCM.authenticPlaintextOfCiphertextWithTag .aes128 key nonce associatedData
          sealed with
      | some plaintext =>
        SuccessfulStatus final ∧
        MemoryWriteFrame initial final
          #v[InPlace.outputRegion initial (sealed.size - 16),
            Stack.region initial aes128gcmDecryptInPlace.minStackBytes] ∧
        InPlace.readOutput initial final (sealed.size - 16) = .ok plaintext
      | none =>
        FailureStatus final 1 ∧
        MemoryWriteFrame initial final
          #v[Stack.region initial aes128gcmDecryptInPlace.minStackBytes] := by
  sorry

/--
`AeadInOut::encrypt_in_place` (aead 0.6.1, `src/lib.rs:258-282`) for `Aes256Gcm`, after
`KeyInit::new` (aes-gcm 0.11.1, `src/lib.rs:217-219`): encrypts the plaintext with AES-256-GCM
where it lies in the buffer, then appends the 16-byte tag.

When `GCM.ciphertextAndTag .aes256 key nonce associatedData plaintext` gives
`some (ciphertext, tag)` and `plaintext.size + 16 ≤ capacity`, the call returns status 0 and the
buffer, as `InPlace.readOutput` reads it, starts with the ciphertext then the tag. With less room it
returns status 1 and the buffer starts with the ciphertext alone: the crate encrypts first and then
fails to grow the buffer. When the specification gives `none` (a plaintext over `P_MAX` or
associated data over `A_MAX`, which no valid call reaches), it returns status 1 and only the stack
may change.
-/
theorem aes256gcm_encrypt_in_place_writes_ciphertext_and_tag_or_fails_without_room
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {key : Vector UInt8 32} {nonce : Vector UInt8 12}
    {associatedData plaintext : ByteArray} {capacity : Nat}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : InPlace.ValidCapacityCall aes256gcmEncryptInPlace initial key nonce
      associatedData plaintext capacity) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      match GCM.ciphertextAndTag .aes256 key nonce associatedData plaintext with
      | some (ciphertext, tag) =>
        if plaintext.size + 16 ≤ capacity then
          SuccessfulStatus final ∧
          MemoryWriteFrame initial final
            #v[InPlace.outputRegion initial (plaintext.size + 16),
              Stack.region initial aes256gcmEncryptInPlace.minStackBytes 16] ∧
          InPlace.readOutput initial final (plaintext.size + 16) =
            .ok (ciphertext ++ ⟨tag.toArray⟩)
        else
          FailureStatus final 1 ∧
          MemoryWriteFrame initial final
            #v[InPlace.outputRegion initial plaintext.size,
              Stack.region initial aes256gcmEncryptInPlace.minStackBytes 16] ∧
          InPlace.readOutput initial final plaintext.size = .ok ciphertext
      | none =>
        FailureStatus final 1 ∧
        MemoryWriteFrame initial final
          #v[Stack.region initial aes256gcmEncryptInPlace.minStackBytes 16] := by
  sorry

/--
`AeadInOut::decrypt_in_place` (aead 0.6.1, `src/lib.rs:292-316`) for `Aes256Gcm`, after
`KeyInit::new` (aes-gcm 0.11.1, `src/lib.rs:217-219`): checks the 16-byte tag at the end of the
buffer with AES-256-GCM and, only if it matches, decrypts the rest where it lies and cuts the
buffer to the plaintext.

When `GCM.authenticPlaintextOfCiphertextWithTag .aes256 key nonce associatedData sealed` gives
`some plaintext`, the call returns status 0 and the first `sealed.size - 16` bytes of the buffer, as
`InPlace.readOutput` reads them, are `plaintext`; the tag after them is unchanged. Otherwise,
including when the buffer holds fewer than 16 bytes, it returns status 1 and only the stack may
change.
-/
theorem aes256gcm_decrypt_in_place_writes_plaintext_or_rejects
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {key : Vector UInt8 32} {nonce : Vector UInt8 12}
    {associatedData sealed : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : InPlace.ValidCall aes256gcmDecryptInPlace initial key nonce
      associatedData sealed sealed.size sealed.size) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      match GCM.authenticPlaintextOfCiphertextWithTag .aes256 key nonce associatedData
          sealed with
      | some plaintext =>
        SuccessfulStatus final ∧
        MemoryWriteFrame initial final
          #v[InPlace.outputRegion initial (sealed.size - 16),
            Stack.region initial aes256gcmDecryptInPlace.minStackBytes] ∧
        InPlace.readOutput initial final (sealed.size - 16) = .ok plaintext
      | none =>
        FailureStatus final 1 ∧
        MemoryWriteFrame initial final
          #v[Stack.region initial aes256gcmDecryptInPlace.minStackBytes] := by
  sorry

end AesGcm.Statements
