import Sha2.Proofs.Wrapper512.Model

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess
  X86Proofs
open Sha2.Proofs.Common.Machine
open Sha2.Proofs.Wrapper

def Variant.readOutput (v : Variant) (initial final : RamState) (form : Form := .slices) :
    Except Fault (Vector UInt8 v.outputBytes) :=
  match form with
  | .slices => Program.readOutput (v.routine form) initial final
  | .digest => OneShot.readOutput (v.routine form) initial final
  | _ => if form.secondOutput then TwoOutputs.readSecondOutput (v.routine form) initial final
      else TwoOutputs.readOutput (v.routine form) initial final

structure DispatchResult [Bindings] (v : Variant)
    (initial s : RamState) (inputs : Array Input) (form : Form := .slices) : Prop where
  state : State v initial s form
  buffered : Buffered v initial s (message inputs) form
  rip : s.RIP = v.pc (v.dispatchOffset form inputs.isEmpty) form

structure FinishResult [bindings : Bindings] (v : Variant)
    (initial final : RamState) (inputs : Array Input) (form : Form := .slices) : Prop where
  execution : ∃ fuel, UniqueExecution initial fuel final
  machine : SupportedIntegerMachineState bindings.processor final
  environment : MachineRamUnitStrideDecodable bindings final
  frame : MemoryWriteFrame initial final (v.writeRegions initial form)
  output : v.readOutput initial final form = .ok (v.digest (message inputs))
  calleeSaved : CalleeSavedRegistersUnchanged initial final
  directionFlag : DirectionFlagUnset final

structure DispatchContract [bindings : Bindings] (v : Variant) (form : Form := .slices) : Prop where
  run : ∀ {initial : RamState} {inputs : Array Input},
    Context v initial inputs form → ∃ s, DispatchResult v initial s inputs form

structure FinishContract [bindings : Bindings] (v : Variant) (form : Form := .slices) : Prop where
  run : ∀ {initial s : RamState} {inputs : Array Input},
    Context v initial inputs form → Buffered v initial s (message inputs) form →
      s.RIP = v.pc (v.dispatchOffset form inputs.isEmpty) form →
      ∃ final, FinishResult v initial final inputs form

structure WrapperContract [bindings : Bindings] (v : Variant) (form : Form := .slices) : Prop where
  dispatch : DispatchContract v form
  finish : FinishContract v form

theorem WrapperContract.of_parts [bindings : Bindings] {v : Variant} {form : Form}
    (dispatch : DispatchContract v form) (finish : FinishContract v form) :
    WrapperContract v form :=
  ⟨dispatch, finish⟩

theorem FinishResult.output_sha384 [Bindings] {initial final : RamState}
    {inputs : Array Input} (result : FinishResult .sha384 initial final inputs) :
    readOutput Variant.sha384.routine initial final =
      .ok (Standards.NIST.SHA2.SHA384
        (Standards.NIST.SHA2.bytesToBits (message inputs))).bytes := by
  exact result.output

theorem FinishResult.output_sha512 [Bindings] {initial final : RamState}
    {inputs : Array Input} (result : FinishResult .sha512 initial final inputs) :
    readOutput Variant.sha512.routine initial final =
      .ok (Standards.NIST.SHA2.SHA512
        (Standards.NIST.SHA2.bytesToBits (message inputs))).bytes := by
  exact result.output

theorem FinishResult.toExists [bindings : Bindings] {v : Variant} {form : Form} {initial final : RamState}
    {inputs : Array Input} (result : FinishResult v initial final inputs form) :
    ∃ fuel : Nat, ∃ final : RamState,
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        (v.writeRegions initial form) ∧
      v.readOutput initial final form = .ok (v.digest (message inputs)) := by
  obtain ⟨fuel, execution⟩ := result.execution
  exact ⟨fuel, final, execution, result.machine, result.environment, result.calleeSaved,
    result.directionFlag, result.frame, result.output⟩

theorem WrapperContract.run [Bindings] {v : Variant} {form : Form} (contract : WrapperContract v form)
    {initial : RamState} {inputs : Array Input} (ctx : Context v initial inputs form) :
    ∃ final, FinishResult v initial final inputs form := by
  obtain ⟨s, dispatch⟩ := contract.dispatch.run ctx
  exact contract.finish.run ctx dispatch.buffered dispatch.rip

theorem WrapperContract.toExists [bindings : Bindings] {v : Variant} {form : Form}
    (contract : WrapperContract v form) {initial : RamState} {inputs : Array Input}
    (ctx : Context v initial inputs form) :
    ∃ fuel : Nat, ∃ final : RamState,
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        (v.writeRegions initial form) ∧
      v.readOutput initial final form = .ok (v.digest (message inputs)) := by
  obtain ⟨final, result⟩ := contract.run ctx
  exact result.toExists

theorem sha384_of_wrapper_contract [bindings : Bindings]
    (contract : WrapperContract .sha384) {initial : RamState} {inputs : Array Input}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall sha384DigestSlices initial inputs) :
    ∃ (fuel : Nat) (final : RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[outputRegion sha384DigestSlices initial, Stack.region initial sha384DigestSlices.minStackBytes] ∧
      readOutput sha384DigestSlices initial final =
        .ok (Standards.NIST.SHA2.SHA384
          (Standards.NIST.SHA2.bytesToBits (message inputs))).bytes := by
  have ctx := Context.of_sha384 hBindings hMachine hCall
  obtain ⟨final, result⟩ := contract.run ctx
  obtain ⟨fuel, execution⟩ := result.execution
  refine ⟨fuel, final, execution, result.machine, result.environment, result.calleeSaved,
    result.directionFlag, ?_, ?_⟩
  · exact result.frame
  · simpa only [Variant.routine_sha384] using result.output_sha384

theorem sha512_of_wrapper_contract [bindings : Bindings]
    (contract : WrapperContract .sha512) {initial : RamState} {inputs : Array Input}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall sha512DigestSlices initial inputs) :
    ∃ (fuel : Nat) (final : RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[outputRegion sha512DigestSlices initial, Stack.region initial sha512DigestSlices.minStackBytes] ∧
      readOutput sha512DigestSlices initial final =
        .ok (Standards.NIST.SHA2.SHA512
          (Standards.NIST.SHA2.bytesToBits (message inputs))).bytes := by
  have ctx := Context.of_sha512 hBindings hMachine hCall
  obtain ⟨final, result⟩ := contract.run ctx
  obtain ⟨fuel, execution⟩ := result.execution
  refine ⟨fuel, final, execution, result.machine, result.environment, result.calleeSaved,
    result.directionFlag, ?_, ?_⟩
  · exact result.frame
  · simpa only [Variant.routine_sha512] using result.output_sha512

end Sha2.Proofs.Wrapper512
