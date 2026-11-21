import Sha3.Spec.Program
import Sha3.Proofs.Frame
import X86Proofs.Program.ReadWrite.Stack
import X86Proofs.Program.Entry

namespace Sha3.Proofs

open X86 Prelude Sha3.Spec.Program X86Proofs X86.Machine X86.UserProcess X86.Helpers

theorem readable_slice {s : RamState} {base : BitVec 64} {total : Nat}
    (h : MemReadable s base total) (off count : Nat) (hc : off + count ≤ total) :
    MemReadable s (base + .ofNat 64 off) count := by
  refine ⟨?_, ?_⟩
  · have := h.low
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  · intro j hj
    simpa only [BitVec.add_assoc, ← BitVec.ofNat_add] using h.mem (off + j) (by omega)

theorem stack_sub_toNat {s : Machine.RamState} {budget offset : Nat}
    (h : Stack.NoUnderflow s budget) (hoffset : offset ≤ budget) :
    (s.regValue .rsp - BitVec.ofNat 64 offset).toNat = (s.regValue .rsp).toNat - offset := by
  have hptr := (s.regValue .rsp).isLt
  have hoffset64 : offset < 2 ^ 64 := by
    change budget ≤ (s.regValue .rsp).toNat at h
    omega
  rw [BitVec.toNat_sub_of_le, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoffset64]
  rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoffset64]
  exact Nat.le_trans hoffset h

theorem stack_sub_contains {s : Machine.RamState} {budget offset i : Nat}
    (h : Stack.Valid s budget) (hoffset : offset ≤ budget) (hi : i < offset) :
    (Stack.region s budget).Contains
      (s.regValue .rsp - BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat := by
  have hptr := (s.regValue .rsp).isLt
  have hunder := h.2.2.1
  change budget ≤ (s.regValue .rsp).toNat at hunder
  have hi64 : i < 2 ^ 64 := by omega
  rw [BitVec.toNat_add, stack_sub_toNat hunder hoffset, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hi64, Nat.mod_eq_of_lt (by omega)]
  simp only [Stack.region, Stack.returnAddressBytes, MemoryRegion.Contains]
  constructor <;> omega

theorem stack_sub_allocated {s : Machine.RamState} {budget offset i : Nat}
    (h : Stack.Valid s budget) (hoffset : offset ≤ budget) (hi : i < offset) :
    ∃ byte, s.external[s.regValue .rsp - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      some byte :=
  h.2.1 _ (stack_sub_contains h hoffset hi)

theorem stack_sub_low {s : Machine.RamState} {budget offset : Nat}
    (h : Stack.Valid s budget) (hoffset : offset ≤ budget) :
    (s.regValue .rsp - BitVec.ofNat 64 offset).toNat + offset < userAddressLimit := by
  rw [stack_sub_toNat h.2.2.1 hoffset]
  have hlow := h.1
  have hunder := h.2.2.1
  simp only [Stack.region, MemoryRegion.Bounded, Stack.returnAddressBytes] at hlow
  change budget ≤ (s.regValue .rsp).toNat at hunder
  omega

theorem stack_push_page {s : Machine.RamState} {budget : Nat}
    (h : Stack.Valid s budget) (hbudget : 8 ≤ budget) :
    (s.regValue .rsp - 8).toNat % 4096 + 8 ≤ 4096 := by
  rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, stack_sub_toNat h.2.2.1 hbudget]
  have halign := h.2.2.2
  change (s.regValue .rsp).toNat % 16 = 8 at halign
  have hunder := h.2.2.1
  change budget ≤ (s.regValue .rsp).toNat at hunder
  omega

theorem machineRamUnitStrideDecodable_readyToStep [bindings : Bindings] {s : RamState}
    (hMachine : SupportedIntegerMachineState bindings.processor s)
    (hEnvironment : MachineRamUnitStrideDecodable bindings s) : ReadyToStep s :=
  ReadyToStep.of_supported hMachine hEnvironment.smrr hEnvironment.memoryType
    (DecoderFeatures.of_supported hMachine hEnvironment.leadingZeroCount)

theorem machineRamUnitStrideDecodable_fetchReady [bindings : Bindings] {s : RamState}
    (hMachine : SupportedIntegerMachineState bindings.processor s)
    (hEnvironment : MachineRamUnitStrideDecodable bindings s) : FetchReady s :=
  ⟨hMachine.integer.cs, hMachine.integer.cr0, hMachine.memory.cr3, hMachine.integer.cr4,
    hMachine.integer.efer, hMachine.integer.maxPhysical, hMachine.integer.early,
    hMachine.integer.lam, hMachine.integer.lass,
    reportsCETSS_of_reportsLAM hMachine.integer.lam, hEnvironment.smrr,
    hEnvironment.memoryType, hMachine.memory.tables⟩

theorem machineRamUnitStrideDecodable_dataReady [bindings : Bindings] {s : RamState}
    (hMachine : SupportedIntegerMachineState bindings.processor s)
    (hEnvironment : MachineRamUnitStrideDecodable bindings s) : DataReady s :=
  ⟨machineRamUnitStrideDecodable_fetchReady hMachine hEnvironment, hMachine.integer.cpl,
    hMachine.integer.debug⟩

theorem memReadable_of_region {s : RamState} {region : MemoryRegion}
    {address : BitVec 64} {count : Nat} (hBounded : region.Bounded)
    (hAllocated : region.Allocated s.external)
    (hStart : region.start ≤ address.toNat)
    (hEnd : address.toNat + count ≤ region.start + region.size) :
    MemReadable s address count := by
  have hBound : region.start + region.size < 2 ^ 32 := hBounded
  constructor
  · omega
  · intro i hi
    have hi64 : i < 2 ^ 64 := by omega
    have haddr : (address + BitVec.ofNat 64 i).toNat = address.toNat + i := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64,
        Nat.mod_eq_of_lt (by omega)]
    obtain ⟨byte, hbyte⟩ := hAllocated (address + BitVec.ofNat 64 i) (by
      rw [haddr]
      exact ⟨by omega, by omega⟩)
    rw [hbyte]
    rfl

theorem output_memReadable {s : RamState} {address : BitVec 64} {count : Nat}
    (h : ValidOutput s ⟨address.toNat, count⟩) : MemReadable s address count :=
  memReadable_of_region h.2.1 h.2.2 (Nat.le_refl _) (Nat.le_refl _)

theorem allocated_of_hasBytes {region : MemoryRegion} {memory : Ram} {bytes : ByteArray}
    (h : region.HasBytes memory bytes) : region.Allocated memory := by
  intro address hcontains
  have hstart : region.start ≤ address.toNat := hcontains.1
  have hend : address.toNat < region.start + bytes.size := by
    rw [h.1]
    exact hcontains.2
  let i : Fin bytes.size := ⟨address.toNat - region.start, by omega⟩
  have he : BitVec.ofNat 64 (region.start + i.val) = address := by
    rw [show region.start + i.val = address.toNat from by dsimp [i]; omega]
    exact BitVec.ofNat_toNat 64 address
  refine ⟨bytes[i.val], ?_⟩
  have hb := h.2 i
  rwa [he] at hb

theorem input_memReadable {s : RamState} {inputs : Array Input} {i : Fin inputs.size}
    (h : ValidInputSlice s inputs i) : MemReadable s inputs[i].address inputs[i].bytes.size :=
  memReadable_of_region h.2.2.2.1 (allocated_of_hasBytes h.2.2.2.2)
    (Nat.le_refl _) (Nat.le_refl _)

theorem stack_push_readable {s : RamState} {budget : Nat}
    (h : Stack.Valid s budget) (hbudget : 8 ≤ budget) : MemReadable s (pushAddr s) 8 := by
  have hptr : stackPtr s = s.regValue .rsp := rfl
  constructor
  · change (stackPtr s - 8).toNat + 8 ≤ 2 ^ 32
    rw [hptr]
    exact Nat.le_of_lt (stack_sub_low h hbudget)
  · intro i hi
    obtain ⟨byte, hbyte⟩ := stack_sub_allocated h hbudget hi
    change (s.external[stackPtr s - 8 + BitVec.ofNat 64 i]?).isSome
    rw [hptr]
    change (s.external[s.regValue .rsp - BitVec.ofNat 64 8 + BitVec.ofNat 64 i]?).isSome
    rw [hbyte]
    rfl

theorem pushStack_run_of_readable [Bindings] (s : RamState) (h : DataReady s)
    (hss : s.SS = userStackSegment)
    (rsp v : BitVec 64) (hw : MemReadable s (rsp - 8) 8)
    (_hpage : (rsp - 8).toNat % 4096 + 8 ≤ 4096) :
    (Push_Stack s.SS rsp s.CS 64 64 v).run s =
      (.ok (rsp - 8 : BitVec 64),
        (Operand.mem (rsp - 8) : Operand 64).write (stackAccess s) v) := by
  let t : RamState := { s with oracle := oracleSkip s.oracle 336 }
  have ht : DataReady t := h.oracle _
  have hcan := isCanonicalWrtPagingMode_run s (rsp - 8) 8 h.cr0 h.cr4 h.efer.lme h.lam
    (by have := hw.low; omega) hw.low
  let linear : Address_Translation :=
    { (linearAddressFromOracle s.oracle s.DS s.CPL (rsp - 8)).1 with
      translation_cpl := X86.Runtime.Unsigned (Segment_Selector.RPL userCodeSegment.selector) }
  have htr := translateLinearToPhysical_run_of_dataReady t ht linear .Memory_Write 8 rfl
    (by decide) rfl hw.low
  have hcpl : 0 ≤ X86.Runtime.Unsigned (Segment_Selector.RPL userCodeSegment.selector) ∧
      X86.Runtime.Unsigned (Segment_Selector.RPL userCodeSegment.selector) ≤ 3 := by decide
  have hphys := physicalMemWrite_dataPhysical_run linear (rsp - 8) rfl 64 (by decide) rfl v t ht.smrr
    hcpl hw.mem
  unfold Push_Stack
  rw [hss, h.cs]
  spec_run [MonadState.get => get_run _,
    Is_64Bit_Code_Segment => is64BitCodeSegment_userCodeSegment_run _ h.efer.lma,
    Is_Canonical_Wrt_Paging_Mode => hcan,
    Create_Linear_Address => createLinearAddress64_run _ _ h.efer.lma,
    Is_Alignment_Checking_Enabled => isAlignmentCheckingEnabled_run _ ht.cr0,
    Check_Write_Permission => checkWritePermission_run _ _ ht.cs ht.efer.lma,
    Check_Data_Write_Breakpoint => checkDataWriteBreakpoint_run _ _ _ ht.debug,
    Translate_Linear_To_Physical.interpreted => htr,
    Physical_Mem_Write => hphys]

theorem push_operation_of_readable [Bindings] (t : RamState) (h : DataReady t)
    (hss : t.SS = userStackSegment)
    (v : BitVec 64) (hw : MemReadable t (pushAddr t) 8)
    (hpage : (pushAddr t).toNat % 4096 + 8 ≤ 4096) :
    (X86.Instructions.Operations.PUSH 64 v).run t = (.ok (), pushState t v) := by
  unfold X86.Instructions.Operations.PUSH
  spec_run [MonadState.get => get_run _, RSP => rsp_run _,
    Push_Stack => pushStack_run_of_readable t h hss (stackPtr t) v hw hpage,
    RSP_write => rspWrite_run _ _]

open X86.Machine.Bindings.PhysicalAccess

theorem physicalMemWrite_dataPhysical_run [instBindings : Bindings]
    (linear : Address_Translation) (addr : BitVec 64) (hla : linear.linear_address = addr)
    (n : Nat) (hn : n % 8 = 0) (hnum : linear.num_bytes = (n / 8 : Nat))
    (value : BitVec n) (s : RamState) (hsmrr : Prelude.SMRRUnblocked instBindings s)
    (hcpl : 0 ≤ linear.translation_cpl ∧ linear.translation_cpl ≤ 3)
    (h : ∀ i, i < n / 8 → (s.external[addr + BitVec.ofNat 64 i]?).isSome) :
    (Physical_Mem_Write (σ := Ram) (dataPhysical linear) n value).run s =
      (.ok (), { s with
        external := memStore s.external addr value
        traceEventsRev := ("isa.memory", "store") :: s.traceEventsRev }) := by
  have hc : X86.Runtime.inRange (dataPhysical linear).translation_cpl 0 3 = true := by
    simp only [dataPhysical_cpl, x86_runtime, hcpl.1, decide_true, hcpl.2, Bool.and_self]
  have haddr : physicalByteAddress (dataPhysical linear) =
      fun i ↦ addr + BitVec.ofNat 64 i :=
    funext (physicalByteAddress_dataPhysical linear addr hla)
  have hwrite := writeBytes_run (exception := Empty) n hn
    (physicalByteAddress (dataPhysical linear)) value s hsmrr (fun i hi ↦ by
      rw [haddr]
      exact h i hi)
  unfold Physical_Mem_Write
  simp only [x86_runtime, pure_bind, hc]
  apply specM_liftNoSourceException_run
  change (do
    checkTranslation (dataPhysical linear) n
    writeBytes n (physicalByteAddress (dataPhysical linear)) value
    X86.Runtime.traceEvent "isa.memory" "store").run s = _
  rw [specM_bind_run _ _ (checkTranslation_dataPhysical_run linear n hn hnum s),
    specM_bind_run _ _ hwrite, traceEvent_run]
  simp only [memStore, PhysicalMemory.write, haddr]

theorem logicalMemWrite_run_align_any [Bindings] (s : RamState) (h : DataReady s)
    (isStack : Bool) (addr : BitVec 64) (n : Nat)
    (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64 ∨ n = 128) (v : BitVec n)
    (align : Memory_Alignment_Type) (halign : AlignmentOk align addr (n / 8))
    (hlow : addr.toNat + n / 8 ≤ 2^32)
    (hmem : ∀ i, i < n / 8 → (s.external[addr + BitVec.ofNat 64 i]?).isSome) :
    (Logical_Mem_Write (size := n) (flatData isStack) addr v align false false
      .Memory_Type_Unknown false).run s =
      (.ok (), (Operand.mem addr : Operand n).write (dataAccess s "store") v) := by
  let t : RamState := { s with oracle := oracleSkip s.oracle 464 }
  have ht : DataReady t := h.oracle _
  have hcount : 0 < n / 8 := by omega
  have hcan := isCanonicalWrtPagingMode_run t addr (n / 8) ht.cr0 ht.cr4 ht.efer.lme
    ht.lam (by omega) hlow
  have hlin := translateLogicalToLinear_run_of_flatData t
    { (logicalAddressFromOracle s.oracle (flatData isStack) s.CPL addr).1 with
      num_bytes := (n / 8 : Nat) } isStack rfl ht.cr0 ht.efer.lma ht.lass hcan align
    (by simp only; omega)
    (by
      show AlignmentOk align addr ((n / 8 : Nat) : Int).toNat
      rw [Int.toNat_natCast]
      exact halign)
  have htr := translateLinearToPhysical_run_of_dataReady t ht
    (dataLinear s isStack addr n) .Memory_Write (n / 8) rfl hcount rfl hlow
  have hphys := physicalMemWrite_dataPhysical_run (dataLinear s isStack addr n) addr rfl n
    (by omega) rfl v t ht.smrr ht.cpl hmem
  unfold Logical_Mem_Write
  rcases hn with rfl | rfl | rfl | rfl | rfl <;>
  · simp (config := { decide := true }) only [assert_of_true, ↓reduceIte, pure_bind]
    rw [specM_bind_run _ _ (checkWritePermission_run _ _ h.cs h.efer.lma),
      specM_bind_run _ _ (createLogicalAddress_run _ _ _ _ (by decide)),
      specM_bind_run _ _ (show (get : X86.Runtime.SpecM X86.Exception RamState RamState).run t =
        (.ok t, t) from rfl), show t.CS = userCodeSegment from h.cs]
    refine (specM_bind_run _ _ hlin).trans ?_
    refine (specM_bind_run _ _ rfl).trans ?_
    refine (specM_bind_run _ _ (checkDataWriteBreakpoint_run _ _ _ ht.debug)).trans ?_
    refine (specM_bind_run _ _ htr).trans ?_
    exact hphys

theorem logicalMemWrite_run_any [Bindings] (s : RamState) (h : DataReady s)
    (isStack : Bool) (addr : BitVec 64) (n : Nat)
    (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (v : BitVec n)
    (hlow : addr.toNat + n / 8 ≤ 2^32)
    (hmem : ∀ i, i < n / 8 → (s.external[addr + BitVec.ofNat 64 i]?).isSome) :
    (Logical_Mem_Write (size := n) (flatData isStack) addr v .Normal_Alignment false false
      .Memory_Type_Unknown false).run s =
      (.ok (), (Operand.mem addr : Operand n).write (dataAccess s "store") v) :=
  logicalMemWrite_run_align_any s h isStack addr n (by omega) v _
    (AlignmentOk.normal _ _) hlow hmem


theorem allocated_memStore {region : MemoryRegion} {memory : Ram}
    (h : region.Allocated memory) (address : BitVec 64) {n : Nat} (value : BitVec n) :
    region.Allocated (memStore memory address value) := by
  intro target htarget
  apply Option.isSome_iff_exists.mp
  exact memStore_isSome memory address value target (Option.isSome_iff_exists.mpr (h target htarget))

theorem memReadable_memStore {s : RamState} {address : BitVec 64} {count : Nat}
    (h : MemReadable s address count) (storeAddress : BitVec 64) {n : Nat} (value : BitVec n) :
    MemReadable { s with external := memStore s.external storeAddress value } address count :=
  ⟨h.low, fun i hi ↦ memStore_isSome s.external storeAddress value _ (h.mem i hi)⟩

theorem memoryWriteFrame_memStore {n k : Nat} (s : RamState) (addr : BitVec 64)
    (value : BitVec n) (regions : Vector MemoryRegion k)
    (hwrite : ∀ i, i < n / 8 →
      ∃ region ∈ regions, region.Contains (addr + BitVec.ofNat 64 i).toNat) :
    MemoryWriteFrame s { s with external := memStore s.external addr value } regions := by
  intro address hout
  apply memStore_getElem?_of_ne
  intro i hi he
  obtain ⟨region, hregion, hcontains⟩ := hwrite i hi
  exact hout region hregion (he ▸ hcontains)

theorem identityPageTableMemory_memStore_of_avoids {n k : Nat} (s : RamState)
    (addr : BitVec 64) (value : BitVec n) (regions : Vector MemoryRegion k)
    (htables : IdentityPageTableMemory s.external)
    (hwrite : ∀ i, i < n / 8 →
      ∃ region ∈ regions, region.Contains (addr + BitVec.ofNat 64 i).toNat)
    (havoid : ∀ region ∈ regions, region.Avoids InPageTables) :
    IdentityPageTableMemory (memStore s.external addr value) := by
  have hframe := memoryWriteFrame_memStore s addr value regions hwrite
  refine ⟨fun i ↦ ?_, fun page i ↦ ?_⟩
  · rw [memoryWriteFrame_eq_of_avoids hframe havoid (inPageTables_root i)]
    exact htables.1 i
  · rw [memoryWriteFrame_eq_of_avoids hframe havoid (inPageTables_leaf page i)]
    exact htables.2 page i

theorem dataReady_memStore_of_avoids [Bindings] {n k : Nat} (s : RamState)
    (addr : BitVec 64) (value : BitVec n) (regions : Vector MemoryRegion k)
    (h : DataReady s)
    (hwrite : ∀ i, i < n / 8 →
      ∃ region ∈ regions, region.Contains (addr + BitVec.ofNat 64 i).toNat)
    (havoid : ∀ region ∈ regions, region.Avoids InPageTables) :
    DataReady { s with external := memStore s.external addr value } :=
  h.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl rfl rfl rfl rfl
    (identityPageTableMemory_memStore_of_avoids s addr value regions h.tables hwrite havoid)

theorem readyToStep_memStore_of_avoids [Bindings] {n k : Nat} (s : RamState)
    (addr : BitVec 64) (value : BitVec n) (regions : Vector MemoryRegion k)
    (h : ReadyToStep s)
    (hwrite : ∀ i, i < n / 8 →
      ∃ region ∈ regions, region.Contains (addr + BitVec.ofNat 64 i).toNat)
    (havoid : ∀ region ∈ regions, region.Avoids InPageTables) :
    ReadyToStep { s with external := memStore s.external addr value } := by
  have ha : AgreesExcept [.mem addr (n / 8)] s
      { s with external := memStore s.external addr value } := by
    refine ⟨?_, ?_, rfl, ?_⟩
    · intro c _ hmem
      cases c with
      | mem _ _ => exact Bool.noConfusion hmem
      | _ => rfl
    · intro address hout
      apply memStore_getElem?_of_ne
      intro i hi he
      exact hout (.mem addr (n / 8)) (List.mem_cons_self)
        ⟨i, hi, he.symm⟩
    · intro address hsome
      exact memStore_isSome s.external addr value address hsome
  exact h.of_agreesExcept ha
    (identityPageTableMemory_memStore_of_avoids s addr value regions h.memory.tables hwrite havoid)

end Sha3.Proofs
