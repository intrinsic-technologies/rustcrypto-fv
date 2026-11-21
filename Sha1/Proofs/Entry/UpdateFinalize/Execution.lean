import Sha1.Spec
import X86Proofs.Program.Execution
import Sha1.Proofs.Common.Call
import Sha1.Proofs.Compress.Blocks
import Sha1.Proofs.Compress.Routine.Main
import Sha1.Proofs.Entry.UpdateFinalize.Initialize
import Sha1.Proofs.Entry.UpdateFinalize.Iteration
import Sha1.Proofs.Entry.UpdateFinalize.Finish

open Sha1.Spec Sha1.Spec.Program Standards.NIST Prelude X86 X86.Machine X86.UserProcess X86Proofs Sha1.Proofs.Refine
open Sha1.Proofs.Common

namespace Sha1.Proofs.Entry.UpdateFinalize

private theorem return_readable {initial : Machine.RamState} {stackBytes : Nat}
    (hstack : Stack.Valid initial stackBytes) :
    MemReadable initial (stackPtr initial) 8 := by
  have hb := hstack.1
  have hs := hstack.2.2.1
  change stackBytes ≤ (initial.regValue .rsp).toNat at hs
  change (initial.regValue .rsp).toNat - stackBytes +
    ((initial.regValue .rsp).toNat + 8 - ((initial.regValue .rsp).toNat - stackBytes)) <
      2 ^ 32 at hb
  refine ⟨by change (initial.regValue .rsp).toNat + 8 ≤ 2 ^ 32; omega, fun i hi ↦ ?_⟩
  apply Option.isSome_iff_exists.mpr
  apply hstack.2.1
  change (initial.regValue .rsp).toNat - stackBytes ≤
      (initial.regValue .rsp + BitVec.ofNat 64 i).toNat ∧
    (initial.regValue .rsp + BitVec.ofNat 64 i).toNat <
      (initial.regValue .rsp).toNat - stackBytes +
        ((initial.regValue .rsp).toNat + 8 - ((initial.regValue .rsp).toNat - stackBytes))
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := i) (by omega),
    Nat.mod_eq_of_lt (by omega)]
  constructor <;> omega

private theorem return_boundary_eq {initial : Machine.RamState} {stackBytes : Nat}
    (bindings : Machine.Bindings)
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hLoaded : ProgramLoaded initial) (hstack : Stack.Valid initial stackBytes) :
    @nearReturn64Boundary _ _ bindings initial = .ok (returnBoundary initial) := by
  letI := bindings
  have he : EntryReady Extracted.programImage initial :=
    EntryReady.of_sections hMachine hBindings.smrr hBindings.memoryType
      hBindings.leadingZeroCount hLoaded (by decide +kernel)
  exact nearReturn64Boundary_eq initial he.ready.dataReady he.ready.cpu.ss
    (return_readable hstack)

theorem update_finalize_site
    {initial : Machine.RamState} {inputs : Array Slices.Input}
    (bindings : Machine.Bindings)
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : SliceHash.ValidCall SliceHash.updateFinalize bindings initial inputs) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      @Returns bindings (returnBoundary initial) fuel initial final ∧
      @ReadyToStep bindings final ∧
      CodeIn Extracted.programImage final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[SliceHash.outputRegion SliceHash.updateFinalize initial,
          Stack.region initial SliceHash.updateFinalize.minStackBytes] ∧
      fixedPart final = fixedPart initial ∧
      SliceHash.readOutput SliceHash.updateFinalize initial final =
        .ok (SHA1.SHA1 (SHA2.bytesToBits (Slices.message inputs))).bytes := by
  letI := bindings
  have he : EntryReady Extracted.programImage initial :=
    EntryReady.of_sections hMachine hBindings.smrr hBindings.memoryType
      hBindings.leadingZeroCount hCall.programLoaded (by decide +kernel)
  obtain ⟨b, hb, hLow, hOutside⟩ := hCall.returnAddress
  have hEq : b = returnBoundary initial :=
    Except.ok.inj (hb.symm.trans (return_boundary_eq bindings hBindings hMachine
      hCall.programLoaded hCall.stackAvailable))
  subst b
  obtain ⟨nf, s, hStart, hs⟩ := initialize_header he.ready he.code hCall hOutside
  obtain ⟨nl, t, hLoop, ht⟩ := Sha1.Proofs.Streaming.advances_loop
    (invariant := Sha1.Proofs.Streaming.UpdateFinalize.Header initial inputs)
    (Nat.zero_le inputs.size)
    (fun _ _ hi _ hh ↦ iteration hCall hBindings.stringStride hOutside hi hh) hs
  obtain ⟨nr, final, hReturn, hFinal⟩ := finish hCall hBindings.stringStride hOutside hLow ht
  exact ⟨_, final, (hStart.trans hLoop).returns hReturn, hFinal⟩

theorem update_finalize_execution
    {initial : Machine.RamState} {inputs : Array Slices.Input}
    (bindings : Machine.Bindings)
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : SliceHash.ValidCall SliceHash.updateFinalize bindings initial inputs) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution (bindings := bindings) initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[SliceHash.outputRegion SliceHash.updateFinalize initial,
          Stack.region initial SliceHash.updateFinalize.minStackBytes] ∧
      SliceHash.readOutput SliceHash.updateFinalize initial final =
        .ok (SHA1.SHA1 (SHA2.bytesToBits (Slices.message inputs))).bytes := by
  letI := bindings
  obtain ⟨fuel, final, hReturns, hReady, hCode, hCallee, hDirection, hFrame, hFixed, hOutput⟩ :=
    update_finalize_site bindings hBindings hMachine hCall
  have hBoundary := return_boundary_eq bindings hBindings hMachine
    hCall.programLoaded hCall.stackAvailable
  obtain ⟨least, hUnique⟩ := Returns.unique_of_boundary hBoundary hReturns
  refine ⟨least, final, hUnique,
    hReady.supported (SupportedSSE.of_sameControls (SameControls.of_fixedPart hFixed)
      hMachine.sse),
    ⟨hReady.smrr, hReady.memoryType, hBindings.stringStride, hReady.features.lzcnt⟩,
    hCallee, hDirection, hFrame, hOutput⟩

end Sha1.Proofs.Entry.UpdateFinalize
