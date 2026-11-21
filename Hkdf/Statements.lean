import Hkdf.Spec

set_option warn.sorry false

/-!
# hkdf 0.13.0

Theorems about the compiled machine code of hkdf 0.13.0 at `Hmac<Sha256>`, one per wrapper. Each
says that a well-formed call returns and produces what the specification in `Hkdf/Spec/RFC5869.lean`
computes; the specification is built on RFC 5869's HKDF in `Standards/RFC/HKDF.lean`.

| Operation | Theorem | Specification | Standard |
| --- | --- | --- | --- |
| `HkdfExtract::<Sha256>`: `new`, `input_ikm`, `finalize` | `hkdf_sha256_extract_writes_prk_of_salt_and_ikm` | `RFC5869.extract` | RFC 5869 §2.2; HMAC: RFC 2104 |
| `Hkdf::<Sha256>`: `new`, then `expand` | `hkdf_sha256_new_expand_writes_okm_or_rejects_length` | `RFC5869.expandFromPrk` of `RFC5869.extract` | RFC 5869 §2.2–2.3; HMAC: RFC 2104 |

How to read the theorem statements and how to build the verified binary are in
`Hkdf/README.md`.
-/

namespace Hkdf.Statements

open Hkdf.Spec Hkdf.Spec.Program Prelude X86

/--
`GenericHkdfExtract::new` (hkdf 0.13.0, `src/lib.rs:46-51`), `input_ikm` once per part
(`src/lib.rs:54-56`) and `finalize` (`src/lib.rs:61-65`), at `Hmac<Sha256>`: hashes the input
keying material, fed in parts, into the 32-byte PRK, keyed with the salt (`None` means 32 zero
bytes).

The 32-byte PRK buffer holds `RFC5869.extract .sha256 salt (concatenation ikm)` (RFC 5869, §2.2),
and memory changes only there and in the stack region. The call returns no status.
-/
theorem hkdf_sha256_extract_writes_prk_of_salt_and_ikm
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {salt : Option ByteArray} {ikm : Array Input}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidExtractCall hkdfSha256Extract initial salt ikm) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[outputRegion initial hkdfSha256Extract,
          Stack.region initial hkdfSha256Extract.minStackBytes] ∧
      readOutput (outputRegion initial hkdfSha256Extract) final.external =
        .ok (RFC5869.extract .sha256 salt (concatenation ikm)) := by
  sorry

/--
`GenericHkdf::new` (hkdf 0.13.0, `src/lib.rs:94-97`), then `GenericHkdf::expand`
(`src/lib.rs:174-176`), at `Hmac<Sha256>`: HKDF of the salt (`None` means 32 zero bytes), the IKM
and the info into `okmLength` bytes.

If `RFC5869.expandFromPrk .sha256 (RFC5869.extract .sha256 salt ikm) info okmLength` (RFC 5869,
§2.2–2.3) is `.ok okm`, the call returns status 0 and the output buffer holds `okm`. If it is
`.invalidLength` (above 8160 bytes), the call returns `invalidLengthStatus` and writes only the
stack region. The `.invalidPrkLength` arm is `False`: a proof must show that `expandFromPrk`
accepts the 32-byte PRK that `extract` returns. The call predicate is `ValidDeriveKeyCall`:
`hkdf_sha256_new_expand` takes its arguments in the same registers and stack slots as `derive_key`,
with the IKM in place of `secret`.
-/
theorem hkdf_sha256_new_expand_writes_okm_or_rejects_length
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {salt : Option ByteArray} {ikm info : ByteArray}
    {okmLength : Nat}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall :
      ValidDeriveKeyCall Extracted.hkdfSha256NewExpandAddress
        hkdfSha256NewExpandMinStackBytes initial salt ikm info okmLength) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      match RFC5869.expandFromPrk .sha256 (RFC5869.extract .sha256 salt ikm) info okmLength with
      | .ok okm =>
        SuccessfulStatus final ∧
        MemoryWriteFrame initial final
          #v[deriveKeyOutputRegion initial okmLength,
            Stack.region initial hkdfSha256NewExpandMinStackBytes] ∧
        readOutput (deriveKeyOutputRegion initial okmLength) final.external = .ok okm
      | .error .invalidPrkLength => False
      | .error .invalidLength =>
        FailureStatus final invalidLengthStatus ∧
        MemoryWriteFrame initial final
          #v[Stack.region initial hkdfSha256NewExpandMinStackBytes] := by
  sorry

end Hkdf.Statements
