import Hkdf.Proofs.NewExpand.Wrapper.Prologue
import Hkdf.Proofs.NewExpand.Wrapper.Copy
import Hkdf.Proofs.NewExpand.Wrapper.Return
import Hkdf.Proofs.NewExpand.Wrapper.CalleeFrame
import Hkdf.Proofs.Common.Model
import Hkdf.Proofs.Common.Memory.Output
import Hkdf.Proofs.NewExpand.ExpandCases

namespace Hkdf.Proofs.NewExpand

open Hkdf.Spec Hkdf.Spec.Program Hkdf.Proofs.Program Hkdf.Proofs.Common
open Prelude X86 X86Proofs

attribute [local irreducible] RFC5869.expandFromPrk

theorem wrapper_correct
    [bindings : Machine.Bindings]
    (extract : ExtractContract) (expand : ExpandContract)
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
      Hkdf.Statements.hkdf_sha256_new_expand_writes_okm_or_rejects_length.match_1 (fun _ => Prop)
        (RFC5869.expandFromPrk .sha256 (RFC5869.extract .sha256 salt ikm) info okmLength)
        (fun okm =>
        SuccessfulStatus final ∧
        MemoryWriteFrame initial final
          #v[deriveKeyOutputRegion initial okmLength,
            Stack.region initial hkdfSha256NewExpandMinStackBytes] ∧
        readOutput (deriveKeyOutputRegion initial okmLength) final.external = .ok okm)
        (fun _ => False)
        (fun _ =>
        FailureStatus final invalidLengthStatus ∧
        MemoryWriteFrame initial final
          #v[Stack.region initial hkdfSha256NewExpandMinStackBytes]) := by
  have machine := SupportedMachine.of_root bindings initial hMachine hBindings
  obtain ⟨a, constructor⟩ := Wrapper.prologue hCall machine hBindings.stringStride
  obtain ⟨b, constructorResult, context⟩ := extract constructor.pre
  have afterConstructor := Wrapper.extractReturn hCall.stack constructor constructorResult context
  obtain ⟨c, core⟩ := Wrapper.copyToExpand hCall afterConstructor hBindings.stringStride
  obtain ⟨d, result⟩ := expand core.pre
  obtain ⟨saved, frame⟩ := Wrapper.expandFrame hCall core result
  have rsp : stackPtr d = stackPtr initial - 360 := by rw [show stackPtr d = _ from result.rsp, core.boundary]
  have rip : d.RIP = 0x102044 := by rw [result.rip, core.boundary]
  obtain ⟨_, final, returned, supported, registers, direction, memory, status⟩ :=
    Wrapper.finishReturn hCall.stack hCall.returnAddress saved rsp rip result.machine result.loaded
      result.abi.2.1 (fun addr existsByte => result.allocated addr (core.run.allocated addr existsByte))
  obtain ⟨_, toCore⟩ := core.run.execution
  obtain ⟨_, body⟩ := result.execution
  have ready := Hkdf.Proofs.Common.Machine.supportedMachine_readyToStep machine
  have readable : MemReadable initial (stackPtr initial) 8 := by
    simpa using CallFrame.stack_readable hCall.stack (fun _ h => h)
      (offset := 0) (len := 8) (by omega) (by omega)
  obtain ⟨fuel, unique⟩ := Returns.unique_of_boundary
    (nearReturn64Boundary_eq initial ready.dataReady ready.cpu.ss readable)
    ((toCore.trans body).returns returned)
  refine ⟨fuel, final, unique, supported.supported, supported.to_environment hBindings.stringStride,
    registers, direction, ?_⟩
  by_cases large : 8160 < okmLength
  · have reject := (expandFromPrk_sha256_invalidLength_iff (RFC5869.extract .sha256 salt ikm)
        info okmLength).2 ⟨by rw [extract_sha256_size]; decide, large⟩
    rw [reject]
    refine ⟨?_, ?_⟩
    · change (final.regValue .rax).setWidth 32 = invalidLengthStatus
      simp only [status, result.status, large, ↓reduceIte]
      rfl
    · intro addr outside
      rw [memory]
      apply frame addr
      intro region member contains
      rcases (show region = deriveKeyOutputRegion initial (writtenLength okmLength) ∨
          region = Stack.region initial hkdfSha256NewExpandMinStackBytes by simpa using member) with rfl | rfl
      · simp [writtenLength, Nat.not_le.mpr large, deriveKeyOutputRegion, MemoryRegion.Contains] at contains
        omega
      · exact outside _ (Vector.mem_singleton_self _) contains
  · have small := Nat.le_of_not_gt large
    obtain ⟨bytes, model, stored⟩ := result.output small
    rw [model]
    refine ⟨?_, ?_, ?_⟩
    · change (final.regValue .rax).setWidth 32 = 0
      simp only [status, result.status, large, ↓reduceIte]
      rfl
    · intro addr outside
      rw [memory]
      exact frame addr (by simpa only [writtenLength, small, ↓reduceIte] using outside)
    · rw [memory]
      have same : registerRegion c .rcx okmLength = deriveKeyOutputRegion initial okmLength := by
        unfold registerRegion deriveKeyOutputRegion
        rw [core.output]
      rw [same] at stored
      exact Hkdf.Proofs.Common.Memory.readOutput_of_hasBytes stored

end Hkdf.Proofs.NewExpand
