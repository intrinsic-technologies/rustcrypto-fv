import Sha1.Spec
import Sha1.Proofs.Buffered.DigestPrepare
import Sha1.Proofs.Buffered.DigestFinish
import Sha1.Proofs.Common.Call
import Sha1.Proofs.Compress.Blocks
import Sha1.Proofs.Compress.Routine.Main
import X86Proofs.Program.Entry
import X86Proofs.Program.ReadWrite.WriteFrame

open Sha1.Spec Sha1.Spec.Program Standards.NIST Prelude X86 X86Proofs
open Sha1.Proofs.Common

namespace Sha1.Proofs.Entry.Digest

private theorem memReadable_of_allocated {s : Machine.RamState} {region : MemoryRegion}
    {addr : BitVec 64} {len : Nat} (h : region.Allocated s.external)
    (hlow : addr.toNat + len ≤ userAddressLimit)
    (hstart : region.start ≤ addr.toNat)
    (hend : addr.toNat + len ≤ region.start + region.size) :
    MemReadable s addr len := by
  refine ⟨hlow, ?_⟩
  intro i hi
  apply Option.isSome_iff_exists.mpr
  apply h
  have hi64 : i < 2 ^ 64 := by
    unfold userAddressLimit at hlow
    omega
  have hsum : addr.toNat + i < 2 ^ 64 := by
    unfold userAddressLimit at hlow
    omega
  simp only [MemoryRegion.Contains, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hi64, Nat.mod_eq_of_lt hsum]
  omega

private theorem stack_return_readable {s : Machine.RamState} {bytes : Nat}
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

private theorem entry_ready (bindings : Machine.Bindings) {s : Machine.RamState}
    (hBindings : MachineRamUnitStrideDecodable bindings s)
    (hMachine : SupportedIntegerMachineState bindings.processor s)
    (hLoaded : ProgramLoaded s) :
    @EntryReady bindings Sha1.Spec.Program.Extracted.programImage s := by
  letI := bindings
  exact EntryReady.of_sections hMachine hBindings.smrr hBindings.memoryType
    hBindings.leadingZeroCount hLoaded (by decide +kernel)

theorem digest_site
    {initial : Machine.RamState} {input : ByteArray}
    (bindings : Machine.Bindings)
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : Digest.ValidCall bindings initial input) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      @Returns bindings (returnBoundary initial) fuel initial final ∧
      @ReadyToStep bindings final ∧
      CodeIn Sha1.Spec.Program.Extracted.programImage final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[Digest.outputRegion initial, Stack.region initial Digest.minStackBytes] ∧
      Digest.readOutput initial final = .ok (SHA1.SHA1 (SHA2.bytesToBits input)).bytes ∧
      fixedPart final = fixedPart initial := by
  letI := bindings
  have hEntry := entry_ready bindings hBindings hMachine hCall.programLoaded
  have hReadable := stack_return_readable hCall.stackAvailable
  have hBoundary := nearReturn64Boundary_eq initial hEntry.ready.dataReady
    hMachine.integer.ss hReadable
  obtain ⟨boundary, hBoundary', hLow, _⟩ := hCall.returnAddress
  have hEq : boundary = returnBoundary initial := Except.ok.inj (hBoundary'.symm.trans hBoundary)
  subst boundary
  obtain ⟨_, prepared, hPrepare, hp⟩ :=
    Sha1.Proofs.Buffered.digest_prepare hEntry.ready hEntry.code hBindings.stringStride hCall
  obtain ⟨finalized, hq⟩ := Sha1.Proofs.Buffered.Finalize.digest_finalize hp
  obtain ⟨_, final, cs, hReturn, hReady, hCode, hAgrees, hFrame, hOutput, hCallee, hDf, hControls⟩ :=
    Sha1.Proofs.Buffered.digest_finish hCall hp hq rfl hLow
  exact ⟨_, final, hPrepare.returns hReturn, hReady, hCode, hCallee, hDf, hFrame, hOutput, hControls⟩

theorem digest_execution
    {initial : Machine.RamState} {input : ByteArray}
    (bindings : Machine.Bindings)
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : Digest.ValidCall bindings initial input) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution (bindings := bindings) initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[Digest.outputRegion initial, Stack.region initial Digest.minStackBytes] ∧
      Digest.readOutput initial final = .ok (SHA1.SHA1 (SHA2.bytesToBits input)).bytes := by
  letI := bindings
  have hEntry := entry_ready bindings hBindings hMachine hCall.programLoaded
  have hReadable := stack_return_readable hCall.stackAvailable
  have hBoundary := nearReturn64Boundary_eq initial hEntry.ready.dataReady
    hMachine.integer.ss hReadable
  obtain ⟨fuel, final, hReturns, hReady, hCode, hCallee, hDf, hFrame, hOutput, hControls⟩ :=
    digest_site bindings hBindings hMachine hCall
  obtain ⟨least, hUnique⟩ := Returns.unique_of_boundary hBoundary hReturns
  exact ⟨least, final, hUnique,
    hReady.supported (SupportedSSE.of_sameControls (SameControls.of_fixedPart hControls)
      hMachine.sse),
    ⟨hReady.smrr, hReady.memoryType, hBindings.stringStride, hReady.features.lzcnt⟩,
    hCallee, hDf, hFrame, hOutput⟩

end Sha1.Proofs.Entry.Digest
