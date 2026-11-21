import X86Proofs.Step.Memory

set_option autoImplicit false

namespace Sha2.Proofs.Common.Instructions.CrossPageStore

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs
open X86.Machine.Bindings.PhysicalAccess

theorem physicalMemWrite_dataPhysical_run [instBindings : Bindings] (linear : Address_Translation)
    (addr : BitVec 64) (hla : linear.linear_address = addr)
    (n : Nat) (hn : n % 8 = 0) (hnum : linear.num_bytes = (n / 8 : Nat))
    (value : BitVec n) (s : RamState)
    (hsmrr : Prelude.SMRRUnblocked instBindings s)
    (hcpl : 0 ≤ linear.translation_cpl ∧ linear.translation_cpl ≤ 3)
    (h : ∀ i, i < n / 8 → (s.external[addr + BitVec.ofNat 64 i]?).isSome) :
    (Physical_Mem_Write (σ := Ram) (dataPhysical linear) n value).run s =
      (.ok (), { s with
        external := memStore s.external addr value
        traceEventsRev := ("isa.memory", "store") :: s.traceEventsRev }) := by
  have hc : X86.Runtime.inRange (dataPhysical linear).translation_cpl 0 3 = true := by
    simp only [dataPhysical_cpl, x86_runtime, hcpl.1, decide_true, hcpl.2, Bool.and_self]
  have haddress : physicalByteAddress (dataPhysical linear) =
      fun i => addr + BitVec.ofNat 64 i :=
    funext (physicalByteAddress_dataPhysical linear addr hla)
  have hwrite := writeBytes_run (exception := Empty) n hn
    (physicalByteAddress (dataPhysical linear)) value s hsmrr (fun i hi => by
      rw [haddress]
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
  simp only [haddress, memStore, PhysicalMemory.write]

theorem logicalMemWrite_run_align_any [Bindings] (s : RamState) (h : DataReady s) (isStack : Bool)
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
  have htr := translateLinearToPhysical_run_of_dataReady t ht (dataLinear s isStack addr n) .Memory_Write (n / 8) rfl
    hcount rfl hlow
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

theorem logicalMemWrite_run_any [Bindings] (s : RamState) (h : DataReady s) (isStack : Bool)
    (addr : BitVec 64) (n : Nat) (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (v : BitVec n)
    (hlow : addr.toNat + n / 8 ≤ 2^32)
    (hmem : ∀ i, i < n / 8 → (s.external[addr + BitVec.ofNat 64 i]?).isSome) :
    (Logical_Mem_Write (size := n) (flatData isStack) addr v .Normal_Alignment false false
      .Memory_Type_Unknown false).run s =
      (.ok (), (Operand.mem addr : Operand n).write (dataAccess s "store") v) :=
  logicalMemWrite_run_align_any s h isStack addr n (by omega) v _ (AlignmentOk.normal _ _) hlow
    hmem

end Sha2.Proofs.Common.Instructions.CrossPageStore
