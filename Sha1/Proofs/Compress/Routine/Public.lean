import Sha1.Proofs.Compress.Routine.Execution
import Sha1.Proofs.Compress.Empty

namespace Sha1.Proofs.Compress.Routine

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Sha1.Proofs.Refine
open Sha1.Spec Sha1.Spec.Program Standards.NIST

theorem outsideCompression_of_notInProgram {address : BitVec 64} (h : ¬ InProgram address) :
    Machine.OutsideCompression address := by
  by_cases hl : address.toNat < 0x1024e0
  · exact Or.inl hl
  · right
    apply Nat.le_of_not_lt
    intro hh
    have hs : 0x36df ≤ Extracted.textBytes.size := by decide +kernel
    have hx := Machine.text_address_in_program (address.toNat - 0x100000) (by omega)
    apply h
    have he : Extracted.textAddress + BitVec.ofNat 64 (address.toNat - 0x100000) = address := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (a := address.toNat - 0x100000) (by have := address.isLt; omega)]
      change (0x100000 + (address.toNat - 0x100000)) % 2 ^ 64 = address.toNat
      rw [Nat.add_sub_of_le (by omega), Nat.mod_eq_of_lt address.isLt]
    rwa [he] at hx

theorem valid_of_call {initial : RamState} {H : Vector (BitVec 32) 5} {blocks : ByteArray}
    (bindings : Bindings) (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : Compress.ValidCall bindings initial H blocks) :
    (Context.mk initial H blocks).Valid bindings := by
  let c : Context := ⟨initial, H, blocks⟩
  have hd : CallData c := ⟨hCall.directionFlagUnset, hCall.programLoaded,
    hCall.blockCountArgumentMatchesBlocks, hCall.inputInMemory, hCall.outputInMemory,
    hCall.stackAvailable, hCall.separation⟩
  have hb := CallData.boundary bindings hBindings hMachine hd
  have hentry := EntryReady.of_sections hMachine hBindings.smrr hBindings.memoryType
    hBindings.leadingZeroCount hCall.programLoaded (by decide +kernel)
  obtain ⟨boundary, he, hlo, hout⟩ := hCall.returnAddress
  rw [hb] at he
  obtain rfl := Except.ok.inj he
  exact ⟨hBindings, hMachine.integer, hentry.ready, hentry.code, hd, Or.inl hCall.atEntryPoint, hlo,
    outsideCompression_of_notInProgram hout⟩

theorem correct_of_parts (hBlock : Machine.BlockCorrect) (hPrologue : PrologueCorrect)
    (hNext : NextCorrect) (hFinish : FinishCorrect)
    {initial : RamState} {H : Vector (BitVec 32) 5} {blocks : ByteArray}
    (bindings : Bindings)
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : Compress.ValidCall bindings initial H blocks) :
    ∃ (fuel : Nat) (final : RamState),
      UniqueExecution (bindings := bindings) initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[Compress.outputRegion initial, Stack.region initial Compress.minStackBytes] ∧
      Compress.readOutput initial final =
        .ok (Hasher.stateBytes
          ((SHA2.SHA256.parse (SHA2.bytesToBits blocks)).foldl SHA1.compress H)) := by
  by_cases hz : blocks.size = 0
  · exact sha1_compress_writes_state_after_blocks_of_size_eq_zero bindings hBindings hMachine hCall hz
  · letI := bindings
    let c : Context := ⟨initial, H, blocks⟩
    have hv : c.Valid bindings := valid_of_call bindings hBindings hMachine hCall
    have hn : 0 < c.count := by
      have he := hCall.blockCountArgumentMatchesBlocks
      change 0 < blocks.size / 64
      omega
    obtain ⟨n, final, hReturns, hReady, hResult⟩ :=
      execution_of_parts hBlock hPrologue hNext hFinish bindings c hv hn
    obtain ⟨fuel, hu⟩ := Returns.unique_of_boundary hv.boundary hReturns
    obtain ⟨hp, hdf, hf, ho, hc, _, _⟩ := hResult
    refine ⟨fuel, final, hu,
      hReady.supported (SupportedSSE.of_sameControls (SameControls.of_fixedPart hc) hMachine.sse),
      ⟨hReady.smrr, hReady.memoryType, hBindings.stringStride, hReady.features.lzcnt⟩,
      hp, hdf, hf, ?_⟩
    rw [c.state_count] at ho
    exact ho

end Sha1.Proofs.Compress.Routine
