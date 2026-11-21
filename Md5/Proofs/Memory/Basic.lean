import Md5.Spec.Program
import X86Proofs.Program.ReadWrite.Store

namespace Md5.Proofs.Memory

open X86 X86.Machine X86Proofs X86.UserProcess X86.Helpers
open X86.Machine.Bindings.PhysicalAccess

structure MemWritable (s : RamState) (addr : BitVec 64) (len : Nat) : Prop where
  low : addr.toNat + len ≤ 2^32
  bytes : ∀ i < len, (s.external[addr + BitVec.ofNat 64 i]?).isSome
  tables : ∀ i < len, ¬ Md5.Spec.Program.InPageTables (addr + BitVec.ofNat 64 i)

theorem MemWritable.readable {s : RamState} {addr : BitVec 64} {len : Nat}
    (h : MemWritable s addr len) : MemReadable s addr len :=
  ⟨h.low, h.bytes⟩

theorem MemWritable.of_external_eq {s t : RamState} {addr : BitVec 64} {len : Nat}
    (h : MemWritable s addr len) (he : t.external = s.external) : MemWritable t addr len :=
  ⟨h.low, fun i hi ↦ he ▸ h.bytes i hi, h.tables⟩

theorem MemWritable.of_region {s : RamState} {addr : BitVec 64} {len : Nat}
    {region : Prelude.MemoryRegion} (hbounded : region.Bounded)
    (hallocated : region.Allocated s.external)
    (htables : region.Avoids Md5.Spec.Program.InPageTables)
    (hstart : region.start ≤ addr.toNat) (hend : addr.toNat + len ≤ region.start + region.size) :
    MemWritable s addr len := by
  have hlow : addr.toNat + len ≤ 2^32 := by
    have : region.start + region.size < 2^32 := hbounded
    omega
  have hcontains (i : Nat) (hi : i < len) :
      region.Contains (addr + BitVec.ofNat 64 i).toNat := by
    change region.start ≤ (addr + BitVec.ofNat 64 i).toNat ∧
      (addr + BitVec.ofNat 64 i).toNat < region.start + region.size
    rw [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show i < 2^64 by omega),
      Nat.mod_eq_of_lt (show addr.toNat + i < 2^64 by omega)]
    omega
  exact ⟨hlow, fun i hi ↦ Option.isSome_iff_exists.mpr (hallocated _ (hcontains i hi)),
    fun i hi ↦ htables _ (hcontains i hi)⟩

theorem MemWritable.memStore {s : RamState} {addr : BitVec 64} {len : Nat}
    (h : MemWritable s addr len) (a : BitVec 64) {n : Nat} (v : BitVec n) :
    MemWritable { s with external := memStore s.external a v } addr len :=
  ⟨h.low, fun i hi ↦ memStore_isSome _ _ _ _ (h.bytes i hi), h.tables⟩

theorem identityPageTableMemory_memStore {m : Ram} (h : IdentityPageTableMemory m)
    (addr : BitVec 64) {n : Nat} (v : BitVec n)
    (htables : ∀ i < n / 8, ¬ Md5.Spec.Program.InPageTables (addr + BitVec.ofNat 64 i)) :
    IdentityPageTableMemory (memStore m addr v) := by
  have hf (x : BitVec 64) (hx : Md5.Spec.Program.InPageTables x) :
      (memStore m addr v)[x]? = m[x]? := by
    apply memStore_getElem?_of_ne
    intro i hi he
    exact htables i hi (he ▸ hx)
  refine ⟨fun i ↦ ?_, fun page i ↦ ?_⟩
  · rw [hf]
    · exact h.1 i
    · refine ⟨⟨0x1000, 8⟩, by simp, ?_⟩
      change 0x1000 ≤ (BitVec.ofNat 64 (0x1000 + i.val)).toNat ∧
        (BitVec.ofNat 64 (0x1000 + i.val)).toNat < 0x1000 + 8
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := i.isLt; omega)]
      have := i.isLt
      omega
  · rw [hf]
    · exact h.2 page i
    · refine ⟨⟨0x2000, 32⟩, by simp, ?_⟩
      change 0x2000 ≤ (BitVec.ofNat 64 (0x2000 + 8 * page.val + i.val)).toNat ∧
        (BitVec.ofNat 64 (0x2000 + 8 * page.val + i.val)).toNat < 0x2000 + 32
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := page.isLt; have := i.isLt; omega)]
      have := page.isLt
      have := i.isLt
      omega

theorem physicalMemWrite_dataPhysical_run [instBindings : Bindings] (linear : Address_Translation)
    (addr : BitVec 64) (hla : linear.linear_address = addr)
    (n : Nat) (hn : n % 8 = 0) (hnum : linear.num_bytes = (n / 8 : Nat)) (value : BitVec n) (s : RamState)
    (hsmrr : Prelude.SMRRUnblocked instBindings s)
    (hcpl : 0 ≤ linear.translation_cpl ∧ linear.translation_cpl ≤ 3)
    (h : ∀ i, i < n / 8 → (s.external[addr + BitVec.ofNat 64 i]?).isSome) :
    (Physical_Mem_Write (σ := Ram) (dataPhysical linear) n value).run s =
      (.ok (), { s with
        external := memStore s.external addr value
        traceEventsRev := ("isa.memory", "store") :: s.traceEventsRev }) := by
  have hc : X86.Runtime.inRange (dataPhysical linear).translation_cpl 0 3 = true := by
    simp only [dataPhysical_cpl, x86_runtime, hcpl.1, decide_true, hcpl.2, Bool.and_self]
  have hwrite := writeBytes_run (exception := Empty) n hn
    (physicalByteAddress (dataPhysical linear)) value s hsmrr (fun i hi => by
      rw [physicalByteAddress_dataPhysical linear addr hla]
      exact h i hi)
  unfold Physical_Mem_Write
  simp only [x86_runtime, pure_bind, hc]
  apply specM_liftNoSourceException_run
  change (do
    checkTranslation (dataPhysical linear) n
    writeBytes n (physicalByteAddress (dataPhysical linear)) value
    X86.Runtime.traceEvent "isa.memory" "store").run s = _
  rw [specM_bind_run _ _ (checkTranslation_dataPhysical_run linear n hn hnum s), specM_bind_run _ _ hwrite,
    traceEvent_run]
  simp only [memStore, PhysicalMemory.write, physicalByteAddress_dataPhysical linear addr hla]

theorem logicalMemWrite_run_align [Bindings] (s : RamState) (h : DataReady s) (isStack : Bool)
    (addr : BitVec 64) (n : Nat) (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64 ∨ n = 128) (v : BitVec n)
    (align : Memory_Alignment_Type) (halign : AlignmentOk align addr (n / 8))
    (hlow : addr.toNat + n / 8 ≤ 2^32)
    (hmem : ∀ i, i < n / 8 → (s.external[addr + BitVec.ofNat 64 i]?).isSome) :
    (Logical_Mem_Write (size := n) (flatData isStack) addr v align false false
      .Memory_Type_Unknown false).run s =
      (.ok (), (Operand.mem addr : Operand n).write (dataAccess s "store") v) := by
  let t : RamState := { s with oracle := oracleSkip s.oracle 464 }
  have ht : DataReady t := h.oracle _
  have hcount : 0 < n / 8 := by omega
  have hcan := isCanonicalWrtPagingMode_run t addr (n / 8) ht.cr0 ht.cr4 ht.efer.lme ht.lam (by omega) hlow
  have hlin := translateLogicalToLinear_run_of_flatData t
    { (logicalAddressFromOracle s.oracle (flatData isStack) s.CPL addr).1 with
      num_bytes := (n / 8 : Nat) } isStack rfl ht.cr0 ht.efer.lma ht.lass hcan align
    (by simp only; omega)
    (by
      show AlignmentOk align addr ((n / 8 : Nat) : Int).toNat
      rw [Int.toNat_natCast]; exact halign)
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

theorem logicalMemWrite_run [Bindings] (s : RamState) (h : DataReady s) (isStack : Bool)
    (addr : BitVec 64) (n : Nat) (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (v : BitVec n)
    (hlow : addr.toNat + n / 8 ≤ 2^32)
    (hmem : ∀ i, i < n / 8 → (s.external[addr + BitVec.ofNat 64 i]?).isSome) :
    (Logical_Mem_Write (size := n) (flatData isStack) addr v .Normal_Alignment false false
      .Memory_Type_Unknown false).run s =
      (.ok (), (Operand.mem addr : Operand n).write (dataAccess s "store") v) :=
  logicalMemWrite_run_align s h isStack addr n (by omega) v _ (AlignmentOk.normal _ _) hlow hmem

structure StorePre (p : BitVec 64) (codeLen : Nat) (addr : RamState → BitVec 64) (len : Nat)
    (s : RamState) : Prop where
  rip : s.RIP = p
  write : MemWritable s (addr s) len
  code : RangeApart (addr s) len p codeLen

theorem afterStep_store_ready [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat) {n : Nat}
    (a : BitVec 64) (v : BitVec n) (nextIP : BitVec 64)
    (htables : ∀ i < n / 8, ¬ Md5.Spec.Program.InPageTables (a + BitVec.ofNat 64 i)) :
    ReadyToStep (afterStep s length fun t =>
      writeResult (dataAccess t "store") (.mem a : Operand n) v nextIP) := by
  have hst : SameControls s (afterStep s length fun t =>
      writeResult (dataAccess t "store") (.mem a : Operand n) v nextIP) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hc := h.cpu
  have hr := h.ready
  have hmem : Prelude.IdentityMappedMemory (afterStep s length fun t =>
      writeResult (dataAccess t "store") (.mem a : Operand n) v nextIP) := by
    refine ⟨h.memory.cr3, ?_⟩
    rw [afterStep_store_external]
    exact identityPageTableMemory_memStore h.memory.tables _ _ htables
  exact ⟨⟨hc.cs, hc.ss, hc.ds, hc.es, hc.cpl, hc.cr0, hc.cr4, hc.efer, hc.maxPhysical, hc.early,
      reportsCPUFeature_of_sameControls hst hc.lam, reportsCPUFeature_of_sameControls hst hc.lass, hc.debug,
      hc.aet⟩,
    hmem,
    ⟨hr.event, hr.active, hr.sti, hr.movss, hr.singleStep, hr.taskSwitch, hr.breakpoint,
      hr.busLock, hr.tf, hr.rf, hr.repeatClear, hr.msr⟩,
    smrrUnblocked_of_sameControls hst h.smrr, writeBackMemoryType_of_sameControls hst h.memoryType,
    h.features.of_sameControls hst⟩

theorem storeEffect_avoids {p : BitVec 64} {bytes : List UInt8} {len : Nat}
    (hlen : bytes.length = len) {n : Nat} (addr : RamState → BitVec 64) (v : RamState → BitVec n)
    {s : RamState} (h : StorePre p len addr (n / 8) s) :
    (storeEffect p len addr v s).Avoids (codeRange p bytes) := by
  subst hlen
  exact Effect.avoids_of_components_mem_rip (storeEffect_components p _ addr v s) h.code

theorem stepEffect_of_store_pre [Bindings] {P : RamState → Prop} {p : BitVec 64}
    {bytes : List UInt8} {len : Nat} {n : Nat} (hn : n % 8 = 0) (h64 : n ≤ 128)
    (addr : RamState → BitVec 64) (v : RamState → BitVec n)
    (hpre : ∀ s, P s → StorePre p len addr (n / 8) s)
    (hstep : ∀ s, ReadyToStep s → CodeIn (codeRange p bytes) s → P s →
      X86.Machine.step s = some (.next (afterStep s len fun t =>
        writeResult (dataAccess t "store") (.mem (addr s) : Operand n) (v s)
          (BitVec.add p (BitVec.ofNat 64 len))))) :
    StepEffect P (codeRange p bytes) (storeEffect p len addr v) := by
  intro s h hcode hs
  have hp := hpre s hs
  exact ⟨_, hstep s h hcode hs,
    afterStep_store_ready h _ _ _ _ hp.write.tables,
    ⟨afterStep_store_rip h _ _ _ _, Operand.read_afterStep_store s _ hn h64 _ _ _, trivial,
      AgreesExcept.afterStep_store s _ _ _ _⟩⟩

theorem stepEffect_of_store [Bindings] {p : BitVec 64} {bytes : List UInt8} {len : Nat}
    {n : Nat} (hn : n % 8 = 0) (h64 : n ≤ 128)
    (addr : RamState → BitVec 64) (v : RamState → BitVec n)
    (hstep : ∀ s, ReadyToStep s → CodeIn (codeRange p bytes) s →
      StorePre p len addr (n / 8) s →
      X86.Machine.step s = some (.next (afterStep s len fun t =>
        writeResult (dataAccess t "store") (.mem (addr s) : Operand n) (v s)
          (BitVec.add p (BitVec.ofNat 64 len))))) :
    StepEffect (StorePre p len addr (n / 8)) (codeRange p bytes) (storeEffect p len addr v) :=
  stepEffect_of_store_pre hn h64 addr v (fun _ h => h) hstep

theorem triple_of_store_pre [Bindings] {P : RamState → Prop} {p : BitVec 64} {bytes : List UInt8}
    {len : Nat} (hlen : bytes.length = len) {n : Nat} (hn : n % 8 = 0) (h64 : n ≤ 128)
    (addr : RamState → BitVec 64) (v : RamState → BitVec n)
    (hpre : ∀ s, P s → StorePre p len addr (n / 8) s)
    (hstep : ∀ s, ReadyToStep s → CodeIn (codeRange p bytes) s → P s →
      X86.Machine.step s = some (.next (afterStep s len fun t =>
        writeResult (dataAccess t "store") (.mem (addr s) : Operand n) (v s)
          (BitVec.add p (BitVec.ofNat 64 len))))) :
    Triple P (codeRange p bytes) (Effect.post (storeEffect p len addr v)) :=
  Triple.of_effect (fun s hs => storeEffect_avoids hlen addr v (hpre s hs))
    (stepEffect_of_store_pre hn h64 addr v hpre hstep)

theorem triple_of_store [Bindings] {p : BitVec 64} {bytes : List UInt8} {len : Nat}
    (hlen : bytes.length = len) {n : Nat} (hn : n % 8 = 0) (h64 : n ≤ 128)
    (addr : RamState → BitVec 64) (v : RamState → BitVec n)
    (hstep : ∀ s, ReadyToStep s → CodeIn (codeRange p bytes) s →
      StorePre p len addr (n / 8) s →
      X86.Machine.step s = some (.next (afterStep s len fun t =>
        writeResult (dataAccess t "store") (.mem (addr s) : Operand n) (v s)
          (BitVec.add p (BitVec.ofNat 64 len))))) :
    Triple (StorePre p len addr (n / 8)) (codeRange p bytes)
      (Effect.post (storeEffect p len addr v)) :=
  triple_of_store_pre hlen hn h64 addr v (fun _ h => h) hstep

end Md5.Proofs.Memory
