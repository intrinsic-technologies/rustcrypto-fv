import K256.Proofs.Sec1.Post
import K256.Proofs.Common.Output
import K256.Proofs.Common.SignatureRun
import K256.Proofs.Sec1.LIR

namespace K256.Proofs.Sec1

open K256.Spec K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common K256.Proofs.Sec1.LIR

theorem run [bindings : Bindings] {initial : RamState} {bytes : ByteArray}
    {n : Nat} {regions : Vector MemoryRegion n} {output : Output Value Ram Reg.count}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall publicKeyFromSec1Bytes initial [bytes])
    (hexec : lifted.program.Exec (dialect Extracted.programImage)
      ⟨lifted.locationOf .l101dd0 initial, []⟩ output)
    (hpost : Returned initial regions output) :
    ∃ fuel final, UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      MemoryWriteFrame initial final regions ∧
      CalleeSavedRegistersUnchanged initial final ∧ DirectionFlagUnset final ∧
      final.external = output.store ∧ (Reg.ofIndex 0).read final = output.values[0] := by
  have he := entryReady bindings hBindings hMachine hCall.programLoaded
  obtain ⟨ret, slot, _, outside⟩ := hCall.returnAddress
  have hret : (returnBoundary initial).rip = ret := memLoad_returnSlot slot
  have hboundary : ReturnOutside (returnBoundary initial) Extracted.programImage := by
    intro x hx
    rw [hret]
    rintro rfl
    exact outside ⟨x.2, programSections_fetchByte_of_mem hx⟩
  apply run_of_lifted_execution hBindings
    (nearReturn64Boundary_eq initial he.ready.dataReady hMachine.integer.ss
      (stack_return_readable hCall.stackAvailable))
    (LIR.simulation hBindings.stringStride _ Common.fnCode_subset_programImage hboundary)
    (Rel.locationOf (P := lifted) (l := .l101dd0) he hCall.atEntryPoint) hexec hpost
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem ofExecution
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {bytes : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall publicKeyFromSec1Bytes initial [bytes])
    {out : Output Value Ram Reg.count}
    (exec : lifted.program.Exec (dialect Extracted.programImage)
      ⟨lifted.locationOf .l101dd0 initial, []⟩ out)
    (post : Post initial bytes out) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      match Secp256k1.decodePublicKey bytes with
      | some point =>
        SuccessfulStatus final ∧
        MemoryWriteFrame initial final
          #v[outputRegion publicKeyFromSec1Bytes initial,
            Stack.region initial publicKeyFromSec1Bytes.minStackBytes] ∧
        readOutput publicKeyFromSec1Bytes initial final =
          .ok (Standards.SECG.ECC.Points.encodePoint Standards.SECG.DomainParameters.Secp256k1.domain false point)
      | none =>
        FailureStatus final ellipticCurveErrorStatus ∧
        MemoryWriteFrame initial final
          #v[Stack.region initial publicKeyFromSec1Bytes.minStackBytes] := by
  cases h : Secp256k1.decodePublicKey bytes with
  | none =>
    simp only [Post, h] at post
    obtain ⟨returned, tag⟩ := post
    obtain ⟨fuel, final, hu, hs, hd, frame, saved, df, _, eax⟩ :=
      run hBindings hMachine hCall exec returned
    have hv : final.regValue .rax = 1 := Value.eq_bits (eax.trans tag)
    exact ⟨fuel, final, hu, hs, hd, saved, df, by simp only [FailureStatus, hv, ellipticCurveErrorStatus]; rfl, frame⟩
  | some point =>
    simp only [Post, h] at post
    obtain ⟨returned, tag, output⟩ := post
    obtain ⟨fuel, final, hu, hs, hd, frame, saved, df, mem, eax⟩ :=
      run hBindings hMachine hCall exec returned
    have hv : final.regValue .rax = 0 := Value.eq_bits (eax.trans tag)
    exact ⟨fuel, final, hu, hs, hd, saved, df, by simp only [SuccessfulStatus, hv]; rfl,
      frame, readRegion_of_hasBytes (mem ▸ output)⟩

end K256.Proofs.Sec1
