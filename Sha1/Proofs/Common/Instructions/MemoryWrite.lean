import X86Proofs.Step.Memory

namespace Sha1.Proofs.Common.Instructions.MemoryWrite

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs
open X86.Machine.Bindings.PhysicalAccess

theorem physicalMemWrite_run [instBindings : Bindings] (linear : Address_Translation)
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
  rw [specM_bind_run _ _ (checkTranslation_dataPhysical_run linear n hn hnum s),
    specM_bind_run _ _ hwrite, traceEvent_run]
  simp only [physicalByteAddress_dataPhysical linear addr hla, memStore, PhysicalMemory.write]

theorem logicalMemWrite_run_seg_align [Bindings] (s : RamState) (h : DataReady s) (seg : Segment)
    (off lin : BitVec 64) (hseg : SegAccess seg off lin) (n : Nat)
    (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64 ∨ n = 128) (v : BitVec n)
    (align : Memory_Alignment_Type) (halign : AlignmentOk align lin (n / 8))
    (hlow : lin.toNat + n / 8 ≤ 2^32)
    (hmem : ∀ i, i < n / 8 → (s.external[lin + BitVec.ofNat 64 i]?).isSome)
    (nt : Bool := false) :
    (Logical_Mem_Write (size := n) seg off v align false false .Memory_Type_Unknown nt).run s =
      (.ok (), (Operand.mem lin : Operand n).write (dataAccess s "store") v) := by
  let t : RamState := { s with oracle := oracleSkip s.oracle 464 }
  have ht : DataReady t := h.oracle _
  have hcount : 0 < n / 8 := by omega
  have hcan := isCanonicalWrtPagingMode_run t lin (n / 8) ht.cr0 ht.cr4 ht.efer.lme ht.lam (by omega) hlow
  obtain ⟨b, hnull⟩ := hseg.null
  have hlin := translateLogicalToLinear_run_of_linear t
    { (logicalAddressFromOracle s.oracle seg s.CPL off).1 with
      num_bytes := (n / 8 : Nat) } lin (hseg.linear t ht.efer.lma) hseg.system hseg.code b hnull
    ht.cr0 ht.efer.lma ht.lass hcan align
    (by simp only; omega)
    (by
      show AlignmentOk align lin ((n / 8 : Nat) : Int).toNat
      rw [Int.toNat_natCast]; exact halign)
  have htr := translateLinearToPhysical_run_of_dataReady t ht (accessLinear s seg off lin n)
    .Memory_Write (n / 8) rfl hcount rfl hlow
  have hphys := physicalMemWrite_run (accessLinear s seg off lin n) lin rfl n
    (by omega) rfl v t ht.smrr ht.cpl hmem
  unfold Logical_Mem_Write
  rcases hn with rfl | rfl | rfl | rfl | rfl <;> cases nt <;>
  · simp (config := { decide := true }) only [assert_of_true, ↓reduceIte, pure_bind]
    rw [specM_bind_run _ _ (checkWritePermission_run _ _ h.cs h.efer.lma),
      specM_bind_run _ _ (createLogicalAddress_run _ _ _ _ (by decide)),
      specM_bind_run _ _ (show (get : X86.Runtime.SpecM X86.Exception RamState RamState).run t =
        (.ok t, t) from rfl), show t.CS = userCodeSegment from h.cs]
    refine (specM_bind_run _ _ hlin).trans ?_
    refine (specM_bind_run _ _ rfl).trans ?_
    refine (specM_bind_run _ _ (checkDataWriteBreakpoint_run _ _ _ ht.debug)).trans ?_
    refine (specM_bind_run _ _ htr).trans ?_
    try rw [(dataPhysical_translation1 (accessLinear s seg off lin _)).2]
    try simp (config := { decide := true }) only [↓reduceIte]
    exact hphys

theorem logicalMemWrite_run_align [Bindings] (s : RamState) (h : DataReady s) (isStack : Bool)
    (addr : BitVec 64) (n : Nat) (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64 ∨ n = 128) (v : BitVec n)
    (align : Memory_Alignment_Type) (halign : AlignmentOk align addr (n / 8))
    (hlow : addr.toNat + n / 8 ≤ 2^32)
    (hmem : ∀ i, i < n / 8 → (s.external[addr + BitVec.ofNat 64 i]?).isSome)
    (nt : Bool := false) :
    (Logical_Mem_Write (size := n) (flatData isStack) addr v align false false
      .Memory_Type_Unknown nt).run s =
      (.ok (), (Operand.mem addr : Operand n).write (dataAccess s "store") v) :=
  logicalMemWrite_run_seg_align s h _ addr addr (SegAccess.flat isStack addr) n hn v align halign
    hlow hmem nt

theorem logicalMemWrite_run_seg [Bindings] (s : RamState) (h : DataReady s) (seg : Segment)
    (off lin : BitVec 64) (hseg : SegAccess seg off lin) (n : Nat)
    (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (v : BitVec n)
    (hlow : lin.toNat + n / 8 ≤ 2^32)
    (hmem : ∀ i, i < n / 8 → (s.external[lin + BitVec.ofNat 64 i]?).isSome)
    (nt : Bool := false) :
    (Logical_Mem_Write (size := n) seg off v .Normal_Alignment false false
      .Memory_Type_Unknown nt).run s =
      (.ok (), (Operand.mem lin : Operand n).write (dataAccess s "store") v) :=
  logicalMemWrite_run_seg_align s h seg off lin hseg n (by omega) v _ (AlignmentOk.normal _ _)
    hlow hmem nt

theorem logicalMemWrite_run [Bindings] (s : RamState) (h : DataReady s) (isStack : Bool)
    (addr : BitVec 64) (n : Nat) (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (v : BitVec n)
    (hlow : addr.toNat + n / 8 ≤ 2^32)
    (hmem : ∀ i, i < n / 8 → (s.external[addr + BitVec.ofNat 64 i]?).isSome)
    (nt : Bool := false) :
    (Logical_Mem_Write (size := n) (flatData isStack) addr v .Normal_Alignment false false
      .Memory_Type_Unknown nt).run s =
      (.ok (), (Operand.mem addr : Operand n).write (dataAccess s "store") v) :=
  logicalMemWrite_run_align s h isStack addr n (by omega) v _ (AlignmentOk.normal _ _) hlow
    hmem nt

end Sha1.Proofs.Common.Instructions.MemoryWrite
