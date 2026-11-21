import Sha1.Proofs.Compress.Routine.Main
import X86Proofs.Program.Entry
import X86Proofs.Program.Execution
import X86Proofs.Program.ReadWrite.WriteFrame
import Sha1.Proofs.Wrapper.Hash.Serialize
import Sha1.Proofs.Wrapper.Absorb.Mathematics

namespace Sha1.Proofs.Common.CompressCall

open Sha1.Spec Sha1.Spec.Program Standards.NIST Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha1.Proofs.Compress
open Sha1.Proofs.Compress.Routine

def CompressionCall : Prop :=
  ∀ [bindings : Bindings] (boundary : ReturnBoundary) {u : RamState}
    {H : Vector (BitVec 32) 5} {blocks : ByteArray},
    UnitStringStride bindings → ReadyToStep u →
    CodeIn Extracted.programImage u → u.RIP = 0x1024e0 →
    Routine.CallData ⟨u, H, blocks⟩ →
    (returnBoundary u).rip.toNat < userAddressLimit →
    Sha1.Proofs.Compress.Machine.OutsideCompression (returnBoundary u).rip →
    Sha1.Proofs.Compress.Machine.OutsideCompression boundary.rip →
    boundary.rip ≠ (returnBoundary u).rip →
    ∃ fuel t, Advances boundary fuel u t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧
      t.RIP = (returnBoundary u).rip ∧ stackPtr t = (returnBoundary u).rsp ∧
      AgreesExcept (Routine.compressionChanges ⟨u, H, blocks⟩) u t ∧
      CalleeSavedRegistersUnchanged u t ∧
      (Compress.outputRegion u).HasBytes t.external
        (Wrapper.Hash.Serialize.stateBytes (Wrapper.Absorb.compressBlocks H blocks))

private theorem program_sections_low : SectionsLow Extracted.programSections := by
  decide +kernel

private theorem code_avoids {c : Routine.Context}
    (h : c.Valid bindings) :
    ∀ r ∈ #v[Compress.outputRegion c.initial, Stack.region c.initial Compress.minStackBytes],
      r.Avoids InProgram := by
  intro r hr
  have hs := h.call.separation.2 r (by simpa using hr)
  intro address ha hprogram
  exact hs.2 address ha (.inl hprogram)

private theorem code_after {c : Routine.Context} {s : RamState}
    (h : c.Valid bindings)
    (hmemory : MemoryWriteFrame c.initial s
      #v[Compress.outputRegion c.initial, Stack.region c.initial Compress.minStackBytes]) :
    CodeIn Extracted.programImage s := by
  apply CodeIn.of_loaded (hlow := program_sections_low.codeLow)
  intro address byte hmem
  have hnot : ∀ r ∈ #v[Compress.outputRegion c.initial,
      Stack.region c.initial Compress.minStackBytes], ¬ r.Contains address.toNat := by
    intro r hr hcontains
    have havoid := code_avoids h r hr address hcontains
    exact havoid ⟨byte, hmem⟩
  rw [hmemory address hnot]
  exact h.call.programLoaded address byte hmem



set_option maxHeartbeats 20000000 in
theorem compression_call (hBlock : Machine.BlockCorrect) : CompressionCall := by
  intro bindings boundary u H blocks hStride hReady hCode hEntry hCall hReturnLow
    hReturnOutside hBoundaryOutside hDifferent
  let c : Routine.Context := ⟨u, H, blocks⟩
  have henv : MachineRamUnitStrideDecodable bindings u :=
    ⟨hReady.smrr, hReady.memoryType, hStride, hReady.features.lzcnt⟩
  have hv : c.Valid bindings :=
    { environment := henv
      machine := hReady.cpu
      ready := hReady
      code := hCode
      call := hCall
      entry := Or.inr hEntry
      returnLow := hReturnLow
      outside := hReturnOutside }
  obtain ⟨fuel, t, hadv, ht, hresult⟩ :=
    Routine.execution_advance hBlock boundary bindings c hv hBoundaryOutside hDifferent
  rcases hresult with ⟨hsaved, hdf, hmem, hout, hfixed, hag, hrip, hrsp, hbytes⟩
  have hct : CodeIn Extracted.programImage t :=
    code_after hv hmem
  have hbytes' : (Compress.outputRegion u).HasBytes t.external
      (Wrapper.Hash.Serialize.stateBytes (Wrapper.Absorb.compressBlocks H blocks)) := by
    simpa [Wrapper.Hash.Serialize.stateBytes, Wrapper.Absorb.compressBlocks,
      Routine.Context.state_count, c] using hbytes
  exact ⟨fuel, t, hadv, ht, hct, hrip, hrsp, hag, hsaved, hbytes'⟩


structure CallPre (bindings : Machine.Bindings) (initial : Machine.RamState)
    (H : Vector (BitVec 32) 5) (blocks : ByteArray) : Prop where
  context : Routine.Context.Valid (⟨initial, H, blocks⟩ : Routine.Context) bindings


structure CallResult [bindings : Machine.Bindings]
    (pre : CallPre bindings initial H blocks) (final : Machine.RamState) : Prop where
  returns : ∃ fuel, @Returns bindings (returnBoundary initial) fuel initial final
  ready : @ReadyToStep bindings final
  result : Routine.Result (⟨initial, H, blocks⟩ : Routine.Context) final
  code : CodeIn Extracted.programImage final

theorem run (hBlock : Machine.BlockCorrect)
    {bindings : Machine.Bindings} {initial : Machine.RamState}
    {H : Vector (BitVec 32) 5} {blocks : ByteArray}
    (h : CallPre bindings initial H blocks) :
    ∃ final, CallResult h final := by
  let c : Routine.Context := ⟨initial, H, blocks⟩
  obtain ⟨fuel, final, hReturns, hReady, hResult⟩ :=
    Routine.execution hBlock bindings c h.context
  refine ⟨final, ⟨⟨fuel, hReturns⟩, hReady, hResult, ?_⟩⟩
  exact code_after h.context hResult.2.2.1

abbrev compressionChanges := Routine.compressionChanges

theorem result_agrees {c : Routine.Context} {t : RamState} (h : Routine.Result c t) :
    AgreesExcept (compressionChanges c) c.initial t := by
  exact h.2.2.2.2.2.1

end Sha1.Proofs.Common.CompressCall
