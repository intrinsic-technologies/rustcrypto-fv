import Hkdf.Proofs.Common.Machine
import Hkdf.Proofs.Common.Memory.LoadBytes
import X86Proofs.Program.Entry
import X86Proofs.Program.Execution
import X86Proofs.Program.ReadWrite.WriteFrame
import X86Proofs.Step.Sse
import Hkdf.Proofs.Common.Refine

set_option autoImplicit false

namespace Hkdf.Proofs.Common.Machine

open Hkdf.Spec.Program Hkdf.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

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

theorem allocated_of_hasBytes {m : Ram} {region : MemoryRegion} {bytes : ByteArray}
    (h : region.HasBytes m bytes) : region.Allocated m := by
  intro address hContains
  have hi : address.toNat - region.start < bytes.size := by
    have hs := h.1
    unfold MemoryRegion.HasLength at hs
    obtain ⟨hl, hh⟩ := hContains
    omega
  have hb := h.2 ⟨address.toNat - region.start, hi⟩
  have he : region.start + (address.toNat - region.start) = address.toNat := by
    have hl := hContains.1
    omega
  refine ⟨bytes[address.toNat - region.start], ?_⟩
  simpa only [he, BitVec.ofNat_toNat, BitVec.setWidth_eq] using hb

theorem contains_of_mem_covers {region : MemoryRegion} (hBounded : region.Bounded)
    {address : BitVec 64}
    (hCovers : Component.Covers (.mem (BitVec.ofNat 64 region.start) region.size) address) :
    region.Contains address.toNat := by
  obtain ⟨i, hi, rfl⟩ := hCovers
  have hStart : region.start < 2^64 := by
    unfold MemoryRegion.Bounded userAddressLimit at hBounded
    omega
  have hIndex : i < 2^64 := by
    unfold MemoryRegion.Bounded userAddressLimit at hBounded
    omega
  have hSum : region.start + i < 2^64 := by
    unfold MemoryRegion.Bounded userAddressLimit at hBounded
    omega
  simp only [MemoryRegion.Contains, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hStart, Nat.mod_eq_of_lt hIndex, Nat.mod_eq_of_lt hSum]
  omega

theorem mem_covers_of_contains {region : MemoryRegion} {address : BitVec 64}
    (h : region.Contains address.toNat) :
    (Component.mem (BitVec.ofNat 64 region.start) region.size).Covers address := by
  refine ⟨address.toNat - region.start, by have := h.2; have := h.1; omega, ?_⟩
  rw [← BitVec.ofNat_add, Nat.add_sub_of_le h.1, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem stack_subrange_bounds {s : RamState} {budget used : Nat}
    (h : Stack.Valid s budget) (hused : used ≤ budget) :
    (Stack.region s budget).start ≤ (stackPtr s - BitVec.ofNat 64 used).toNat ∧
      (stackPtr s - BitVec.ofNat 64 used).toNat + (used + 8) ≤
        (Stack.region s budget).start + (Stack.region s budget).size := by
  have hs : budget ≤ (stackPtr s).toNat := h.2.2.1
  have hu : used < 2^64 := by have := (stackPtr s).isLt; omega
  have hstart : (stackPtr s - BitVec.ofNat 64 used).toNat = (stackPtr s).toNat - used := by
    rw [BitVec.toNat_sub_of_le (by
      simp only [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hu]
      omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt hu]
  rw [hstart]
  change (stackPtr s).toNat - budget ≤ (stackPtr s).toNat - used ∧
    (stackPtr s).toNat - used + (used + 8) ≤
      ((stackPtr s).toNat - budget) +
        ((stackPtr s).toNat + 8 - ((stackPtr s).toNat - budget))
  omega

theorem contains_offset_of_subrange {region : MemoryRegion} {addr : BitVec 64} {len : Nat}
    (hb : region.Bounded) (hs : region.start ≤ addr.toNat)
    (he : addr.toNat + len ≤ region.start + region.size) (i : Nat) (hi : i < len) :
    region.Contains (addr + BitVec.ofNat 64 i).toNat := by
  have hlow : region.start + region.size < 2^32 := hb
  have hi64 : i < 2^64 := by omega
  have hsum : addr.toNat + i < 2^64 := by omega
  simp only [MemoryRegion.Contains, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hi64, Nat.mod_eq_of_lt hsum]
  omega

theorem entryReady (bindings : Bindings) {s : RamState}
    (hBindings : MachineRamUnitStrideDecodable bindings s)
    (hMachine : SupportedIntegerMachineState bindings.processor s)
    (hLoaded : ProgramLoaded s) : @EntryReady bindings Extracted.programImage s := by
  letI := bindings
  exact EntryReady.of_sections hMachine hBindings.smrr hBindings.memoryType
    hBindings.leadingZeroCount hLoaded programSections_low

theorem programLoaded_of_separation {s t : RamState} {n : Nat}
    {regions : Vector MemoryRegion n} {reads : List MemoryRegion}
    (frame : MemoryWriteFrame s t regions) (loaded : ProgramLoaded s)
    (apart : MemorySeparation regions reads) : ProgramLoaded t := by
  intro address byte hmem
  rw [frame address (by
    intro r hr hin
    exact (apart.2 r hr).2 address hin (.inl ⟨byte, hmem⟩))]
  exact loaded address byte hmem

theorem stack_writable {s : RamState} {budget used : Nat}
    (hStack : Stack.Valid s budget) (hUsed : used ≤ budget)
    (hAvoid : (Stack.region s budget).Avoids fun a ↦ InProgram a ∨ InPageTables a) :
    Hkdf.Proofs.Refine.Writable Extracted.programImage s.external
      (stackPtr s - BitVec.ofNat 64 used) (used + 8) := by
  obtain ⟨hStart, hEnd⟩ := stack_subrange_bounds hStack hUsed
  have hBound : (Stack.region s budget).start + (Stack.region s budget).size < 2^32 :=
    hStack.1
  have hLow : (stackPtr s - BitVec.ofNat 64 used).toNat + (used + 8) ≤ 2^32 := by omega
  have hRead := memReadable_of_allocated hStack.2.1 hLow hStart hEnd
  refine ⟨⟨hRead.low, hRead.mem⟩, tables_of_not_reserved (by omega) hLow ?_, ?_⟩
  · intro i hi hTable
    exact hAvoid _ (contains_offset_of_subrange hStack.1 hStart hEnd i hi) (.inr hTable)
  · intro x hx i hi he
    apply hAvoid _ (contains_offset_of_subrange hStack.1 hStart hEnd i hi)
    exact .inl ⟨x.2, he ▸ hx⟩

theorem returnBoundary_valid [bindings : Bindings] {s : RamState} {budget : Nat}
    (hReady : ReadyToStep s) (hStack : Stack.Valid s budget)
    (hReturn : ValidReturnAddress s) :
    nearReturn64Boundary s = .ok (returnBoundary s) ∧
      (returnBoundary s).rip.toNat < userAddressLimit ∧
      ¬ InProgram (returnBoundary s).rip := by
  have hNear := nearReturn64Boundary_eq s hReady.dataReady hReady.cpu.ss
    (stack_return_readable hStack)
  obtain ⟨address, loaded, low, outside⟩ := hReturn
  have value : memLoad s.external (stackPtr s) 64 = address := by
    change memLoad s.external (s.regValue .rsp) 64 = address
    apply Hkdf.Proofs.Common.Memory.memLoad_of_loadBytes64
    simpa only [Stack.returnSlot, BitVec.ofNat_toNat, BitVec.setWidth_eq] using loaded.2
  refine ⟨hNear, ?_, ?_⟩
  · change (memLoad s.external (stackPtr s) 64).toNat < userAddressLimit
    rwa [value]
  · change ¬ InProgram (memLoad s.external (stackPtr s) 64)
    rwa [value]

theorem preservesABI_refl (s : RamState) (directionFlag : DirectionFlagUnset s) :
    PreservesABI s s := ⟨fun _ _ ↦ rfl, directionFlag, rfl, rfl⟩

theorem inProgram_low {a : BitVec 64} (h : InProgram a) : a.toNat < 2^32 := by
  obtain ⟨byte, hb⟩ := h
  exact programSections_low.codeLow _ hb

end Hkdf.Proofs.Common.Machine
