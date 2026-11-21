import Base16ct.Proofs.Base16ctUpperDecodeCorrect.Compatibility
import X86Proofs

namespace Base16ct.Proofs.Base16ctUpperDecodeCorrect

variable {lengthWritten : Prop}

open Base16ct.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem sectionsLow : SectionsLow Extracted.programSections := by
  decide +kernel

theorem entryReady [bindings : Bindings] {s : RamState} {routine : Routine}
    {input : List UInt8} {capacity : Nat}
    (hsmrr : SMRRUnblocked bindings s) (hmt : WriteBackMemoryType bindings s 0)
    (hs : SupportedIntegerMachineState bindings.processor s)
    (hlzcnt : LeadingZeroCountReported bindings s)
    (hc : ValidCall routine s input capacity lengthWritten) : EntryReady Extracted.programImage s :=
  EntryReady.of_sections hs hsmrr hmt hlzcnt hc.programLoaded sectionsLow

theorem codeSlice {s : RamState} (h : CodeIn Extracted.programImage s)
    (offset length : Nat) (hsize : offset + length ≤ Extracted.textBytes.size) :
    CodeIn (codeRange (Extracted.textAddress + BitVec.ofNat 64 offset)
      (Extracted.textBytes.toListFrom offset length)) s :=
  h.slice_of_section (sec := ⟨Extracted.textAddress, Extracted.textBytes⟩)
    (by simp [Extracted.programSections]) offset length hsize

theorem inputLength {s : RamState} {routine : Routine} {input : List UInt8} {capacity : Nat}
    (h : ValidCall routine s input capacity lengthWritten) :
    (s.regValue .rsi).toNat = input.length := by
  simpa only [List.size_toByteArray] using h.lengthArgumentMatchesInput

theorem outputCapacity {s : RamState} {routine : Routine} {input : List UInt8} {capacity : Nat}
    (h : ValidCall routine s input capacity lengthWritten) :
    (s.regValue .r8).toNat = capacity :=
  h.capacityArgumentMatchesOutput

theorem inputLengthBound {s : RamState} {routine : Routine} {input : List UInt8} {capacity : Nat}
    (h : ValidCall routine s input capacity lengthWritten) : input.length < 2 ^ 32 := by
  have hb := h.inputInMemory.2.1
  change (s.regValue .rdi).toNat + input.toByteArray.size < 2 ^ 32 at hb
  rw [List.size_toByteArray] at hb
  omega

theorem outputCapacityBound {s : RamState} {routine : Routine} {input : List UInt8} {capacity : Nat}
    (h : ValidCall routine s input capacity lengthWritten) : capacity < 2 ^ 32 := by
  have hb := h.outputInMemory.2.1
  change (s.regValue .rcx).toNat + capacity < 2 ^ 32 at hb
  omega

theorem regionReadable {s : RamState} {region : MemoryRegion} {addr : BitVec 64} {len : Nat}
    (hb : region.Bounded) (ha : region.Allocated s.external)
    (hlo : region.start ≤ addr.toNat) (hhi : addr.toNat + len ≤ region.start + region.size) :
    MemReadable s addr len := by
  change region.start + region.size < 2 ^ 32 at hb
  refine ⟨by omega, ?_⟩
  intro i hi
  apply Option.isSome_iff_exists.mpr
  apply ha
  change region.start ≤ (addr + BitVec.ofNat 64 i).toNat ∧
    (addr + BitVec.ofNat 64 i).toNat < region.start + region.size
  rw [BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show addr.toNat + i < 2 ^ 64 by omega)]
  omega

theorem regionWritable {s : RamState} {region : MemoryRegion} {addr : BitVec 64} {len : Nat}
    (hb : region.Bounded) (ha : region.Allocated s.external)
    (ht : region.Avoids fun a => pageTables.Contains a.toNat)
    (hlo : region.start ≤ addr.toNat) (hhi : addr.toNat + len ≤ region.start + region.size)
    (hpos : 0 < len) (_hpage : addr.toNat % 4096 + len ≤ 4096) :
    MemWritable s addr len := by
  have hr := regionReadable hb ha hlo hhi
  refine MemWritable.of_not_reserved hpos hr.low hr.mem ?_
  intro i hi
  apply ht
  change region.start + region.size < 2 ^ 32 at hb
  change region.start ≤ (addr + BitVec.ofNat 64 i).toNat ∧
    (addr + BitVec.ofNat 64 i).toNat < region.start + region.size
  rw [BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show addr.toNat + i < 2 ^ 64 by omega)]
  omega

theorem returnSlotReadable {s : RamState} {routine : Routine} {input : List UInt8} {capacity : Nat}
    (h : ValidCall routine s input capacity lengthWritten) : MemReadable s (stackPtr s) 8 := by
  apply regionReadable h.stack.1 h.stack.2.1
  · change (s.regValue .rsp).toNat - routine.minStackBytes ≤ (s.regValue .rsp).toNat
    omega
  · change (s.regValue .rsp).toNat + 8 ≤
      (s.regValue .rsp).toNat - routine.minStackBytes +
        ((s.regValue .rsp).toNat + 8 - ((s.regValue .rsp).toNat - routine.minStackBytes))
    omega

theorem returnedUnique [bindings : Bindings] {s t : RamState} {routine : Routine}
    {input : List UInt8} {capacity fuel : Nat} (h : ValidCall routine s input capacity lengthWritten)
    (hr : ReadyToStep s) (hexec : Returns (returnBoundary s) fuel s t) :
    ∃ least, UniqueExecution s least t :=
  hexec.unique hr.dataReady hr.cpu.ss (returnSlotReadable h)

theorem advanceInProgram [bindings : Bindings] {s : RamState} {boundary : ReturnBoundary}
    {pre : RamState → Prop} {code : CodeMap} {effect : RamState → Effect}
    (hstep : StepEffect pre code effect) (hr : ReadyToStep s)
    (hcode : CodeIn Extracted.programImage s) (hsub : ∀ x ∈ code, x ∈ Extracted.programImage)
    (hp : pre s) (hret : ¬ InProgram boundary.rip)
    (hnext : InProgram (effect s).rip) (havoid : (effect s).Avoids Extracted.programImage) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ (effect s).Holds s t := by
  obtain ⟨t, he, hr', hf⟩ := hstep.advances hr (hcode.mono hsub) hp
    (fun heq => hret (heq ▸ hnext))
  exact ⟨t, he, hr', hf.codeIn havoid hcode, hf⟩

theorem supportedAfter [bindings : Bindings] {s t : RamState} {components : List Component}
    (hs : SupportedIntegerMachineState bindings.processor s) (hr : ReadyToStep t)
    (hf : AgreesExcept components s t) : SupportedIntegerMachineState bindings.processor t :=
  ⟨hr.cpu, SupportedSSE.of_agreesExcept hf hs.sse, hr.memory, hr.ready⟩

theorem entryReadyAfter [bindings : Bindings] {s t : RamState}
    {components : List Component} (hentry : EntryReady Extracted.programImage s)
    (hr : ReadyToStep t) (hc : CodeIn Extracted.programImage t)
    (hf : AgreesExcept components s t) : EntryReady Extracted.programImage t :=
  ⟨hr, SupportedSSE.of_agreesExcept hf hentry.sse, hc⟩

theorem returnBoundaryValid {s : RamState} {routine : Routine}
    {input : List UInt8} {capacity : Nat} (h : ValidCall routine s input capacity lengthWritten) :
    (returnBoundary s).rip.toNat < userAddressLimit ∧ ¬ InProgram (returnBoundary s).rip := by
  obtain ⟨address, hword, hlow, hout⟩ := h.returnAddress
  have hread := (Bytes.of_memLoad (n := 64) (returnSlotReadable h).mem).loadBytes64
  have hword' := hword.2
  change Machine.loadBytes s.external (BitVec.ofNat 64 (s.regValue .rsp).toNat) 8 = .ok address at hword'
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at hword'
  have he : (returnBoundary s).rip = address := by
    have hload : Machine.loadBytes s.external (stackPtr s) 8 =
        .ok (returnBoundary s).rip := hread
    change Machine.loadBytes s.external (stackPtr s) 8 = .ok address at hword'
    rw [hload] at hword'
    exact Except.ok.inj hword'
  rw [he]
  exact ⟨hlow, hout⟩

end Base16ct.Proofs.Base16ctUpperDecodeCorrect
