import AesGcm.Spec.Program
import X86Proofs.Program.Entry
import X86Proofs.Program.Execution
import X86Proofs.Program.ReadWrite.Bytes
import X86Proofs.Step.Sse

namespace AesGcm.Proofs.Machine.Runtime

open AesGcm.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem memReadable_of_allocated {s : Machine.RamState} {region : MemoryRegion}
    {addr : BitVec 64} {len : Nat} (h : region.Allocated s.external)
    (hlow : addr.toNat + len ≤ userAddressLimit)
    (hstart : region.start ≤ addr.toNat)
    (hend : addr.toNat + len ≤ region.start + region.size) :
    MemReadable s addr len := by
  refine ⟨hlow, ?_⟩
  intro i hi
  apply Option.isSome_iff_exists.mpr
  apply h
  have hi64 : i < 2^64 := by unfold userAddressLimit at hlow; omega
  have hsum : addr.toNat + i < 2^64 := by unfold userAddressLimit at hlow; omega
  simp only [MemoryRegion.Contains, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hi64, Nat.mod_eq_of_lt hsum]
  omega

theorem stack_return_readable {s : Machine.RamState} {bytes : Nat}
    (h : Stack.Valid s bytes) : MemReadable s (stackPtr s) 8 := by
  rcases h with ⟨hb, ha, hn, _⟩
  have hstart : (Stack.region s bytes).start ≤ (stackPtr s).toNat := by
    change (s.regValue .rsp).toNat - bytes ≤ (s.regValue .rsp).toNat
    omega
  have hend : (Stack.region s bytes).start + (Stack.region s bytes).size =
      (stackPtr s).toNat + 8 := by
    change ((s.regValue .rsp).toNat - bytes) +
      ((s.regValue .rsp).toNat + 8 - ((s.regValue .rsp).toNat - bytes)) =
      (s.regValue .rsp).toNat + 8
    omega
  apply memReadable_of_allocated ha
  · change (Stack.region s bytes).start + (Stack.region s bytes).size < userAddressLimit at hb
    omega
  · exact hstart
  · omega

theorem programSections_low : SectionsLow Extracted.programSections := by
  decide +kernel

theorem entryReady [bindings : Bindings] {initial : RamState}
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hLoaded : ProgramLoaded initial) : EntryReady Extracted.programImage initial :=
  EntryReady.of_sections hMachine hBindings.smrr hBindings.memoryType
    hBindings.leadingZeroCount hLoaded programSections_low

theorem final_environment {bindings : Bindings} {initial final : RamState}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hReady : @ReadyToStep bindings final) :
    MachineRamUnitStrideDecodable bindings final :=
  ⟨hReady.smrr, hReady.memoryType, hBindings.stringStride, hReady.features.lzcnt⟩

theorem final_supported {bindings : Bindings} {initial final : RamState}
    {cs : List Component}
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hReady : @ReadyToStep bindings final) (hFrame : AgreesExcept cs initial final) :
    SupportedIntegerMachineState bindings.processor final :=
  ⟨hReady.cpu, X86Proofs.SupportedSSE.of_agreesExcept hFrame hMachine.sse,
    hReady.memory, hReady.ready⟩

end AesGcm.Proofs.Machine.Runtime
