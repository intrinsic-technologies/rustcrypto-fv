import Sha2.Proofs.Digest.Initialized
import Sha2.Proofs.Digest.Absorb.Correctness
import Sha2.Proofs.Wrapper512.Finish.Run
import Sha2.Proofs.Common.SHA512.Compression.Correctness

set_option autoImplicit false

namespace Sha2.Proofs.Digest

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine
  X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Wrapper512 Sha2.Proofs.Common.SHA512

theorem correct [bindings : Bindings] (v : Variant)
    {initial : RamState} {data : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : OneShot.ValidCall (v.routine .digest) initial data) :
    ∃ (fuel : Nat) (final : RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final (v.writeRegions initial .digest) ∧
      v.readOutput initial final .digest = .ok (v.digest data) := by
  have ctx := Context.of_digest v hBindings hMachine hCall
  obtain ⟨s,preserved,length,source,rip⟩ := entered512_state v ctx.machine hCall
  obtain ⟨b,buffered,ripB,sourceB,lengthB⟩ := initialized512 ctx preserved rip
  obtain ⟨t,absorbed,ripT⟩ := Absorb.correct Compression.block_correct ctx buffered ripB
    (sourceB.trans source) (lengthB.trans length)
  obtain ⟨final,result⟩ := Finish.run Compression.block_correct ctx
    (by simpa [message] using absorbed) ripT
  simpa [message] using result.toExists

end Sha2.Proofs.Digest

namespace Sha2.Statements

open Sha2.Spec Sha2.Spec.Program Standards.NIST.SHA2 Prelude X86

theorem sha384_digest_writes_sha384_of_data
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {data : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : OneShot.ValidCall sha384Digest initial data) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[OneShot.outputRegion sha384Digest initial,
          Stack.region initial sha384Digest.minStackBytes] ∧
      OneShot.readOutput sha384Digest initial final = .ok (SHA384 (bytesToBits data)).bytes := by
  exact Sha2.Proofs.Digest.correct .sha384 hBindings hMachine hCall

theorem sha512_digest_writes_sha512_of_data
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {data : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : OneShot.ValidCall sha512Digest initial data) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[OneShot.outputRegion sha512Digest initial,
          Stack.region initial sha512Digest.minStackBytes] ∧
      OneShot.readOutput sha512Digest initial final = .ok (SHA512 (bytesToBits data)).bytes := by
  exact Sha2.Proofs.Digest.correct .sha512 hBindings hMachine hCall

theorem sha512_224_digest_writes_sha512_224_of_data
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {data : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : OneShot.ValidCall sha512_224Digest initial data) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[OneShot.outputRegion sha512_224Digest initial,
          Stack.region initial sha512_224Digest.minStackBytes] ∧
      OneShot.readOutput sha512_224Digest initial final =
        .ok (SHA512_224 (bytesToBits data)).bytes := by
  exact Sha2.Proofs.Digest.correct .sha512_224 hBindings hMachine hCall

theorem sha512_256_digest_writes_sha512_256_of_data
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {data : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : OneShot.ValidCall sha512_256Digest initial data) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[OneShot.outputRegion sha512_256Digest initial,
          Stack.region initial sha512_256Digest.minStackBytes] ∧
      OneShot.readOutput sha512_256Digest initial final =
        .ok (SHA512_256 (bytesToBits data)).bytes := by
  exact Sha2.Proofs.Digest.correct .sha512_256 hBindings hMachine hCall

end Sha2.Statements
