import K256.Proofs.Common.Image
import X86Proofs.Program.Entry
import X86Proofs.Program.Execution
import X86Proofs.Program.ReadWrite.WriteFrame
import X86Proofs.Step.Sse

namespace K256.Proofs.Common

open K256.Spec.Program Prelude X86 X86Proofs

theorem entryReady (bindings : Machine.Bindings) {s : Machine.RamState}
    (hBindings : MachineRamUnitStrideDecodable bindings s)
    (hMachine : SupportedIntegerMachineState bindings.processor s)
    (hLoaded : ProgramLoaded s) :
    @EntryReady bindings Extracted.programImage s := by
  letI := bindings
  exact EntryReady.of_sections hMachine hBindings.smrr hBindings.memoryType
    hBindings.leadingZeroCount
    (fun _ _ hm ↦ hLoaded _ _ (programSections_fetchByte_of_mem hm)) programSections_low

theorem supportedIntegerMachineState_of_ready [bindings : Machine.Bindings]
    {s t : Machine.RamState} {cs : List Component}
    (h : ReadyToStep t) (he : AgreesExcept cs s t)
    (hs : Prelude.SupportedSSE bindings.processor s) :
    SupportedIntegerMachineState bindings.processor t :=
  ⟨h.cpu, X86Proofs.SupportedSSE.of_agreesExcept he hs, h.memory, h.ready⟩

theorem machineRamUnitStrideDecodable_of_ready [bindings : Machine.Bindings]
    {s : Machine.RamState} (h : ReadyToStep s) (hstride : UnitStringStride bindings) :
    MachineRamUnitStrideDecodable bindings s :=
  ⟨h.smrr, h.memoryType, hstride, h.features.lzcnt⟩

theorem programLoaded_of_memoryWriteFrame {s t : Machine.RamState}
    {regions : Vector MemoryRegion n}
    (h : MemoryWriteFrame s t regions) (hLoaded : ProgramLoaded s)
    (havoid : ∀ r ∈ regions, r.Avoids InProgram) : ProgramLoaded t := by
  intro address byte hmem
  rw [h address (by
    intro r hr hin
    exact havoid r hr address hin ⟨byte, hmem⟩)]
  exact hLoaded address byte hmem

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

theorem readVector_of_hasBytes {s : Machine.RamState} {region : MemoryRegion}
    {bytes : Vector UInt8 n} (h : region.HasBytes s.external ⟨bytes.toArray⟩) :
    (Vector.ofFnM fun i : Fin n ↦
      match s.external[BitVec.ofNat 64 (region.start + i.val)]? with
      | some byte => Except.ok byte
      | none => Except.error (Machine.Fault.unmappedMemory
          (BitVec.ofNat 64 (region.start + i.val)))) = .ok bytes := by
  have hByte (i : Fin n) :
      s.external[BitVec.ofNat 64 (region.start + i.val)]? = some bytes[i.val] := by
    exact h.2 ⟨i.val, by simpa only [ByteArray.size, Vector.size_toArray] using i.isLt⟩
  simp only [hByte]
  change Vector.ofFnM (fun i : Fin n ↦ pure (bytes[i.val])) = _
  rw [Vector.ofFnM_pure]
  congr 1
  exact Vector.ofFn_getElem

theorem hasBytes_of_memoryWriteFrame {s t : Machine.RamState}
    {regions : Vector MemoryRegion n} {region : MemoryRegion} {bytes : ByteArray}
    (h : MemoryWriteFrame s t regions) (hb : region.HasBytes s.external bytes)
    (hbound : region.Bounded) (hsep : ∀ r ∈ regions, region.Disjoint r) :
    region.HasBytes t.external bytes := by
  refine ⟨hb.1, ?_⟩
  intro i
  rw [h _ (by
    intro r hr
    apply hsep r hr
    have hsize : bytes.size = region.size := hb.1
    have hlt : region.start + i.val < 2^64 := by
      unfold MemoryRegion.Bounded userAddressLimit at hbound
      omega
    simp only [MemoryRegion.Contains, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    omega)]
  exact hb.2 i

end K256.Proofs.Common
