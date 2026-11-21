import P256.Proofs.Nonce.Update.Seeded.Absorb.State
import P256.Proofs.Nonce.Update.Absorb.Seeded.Memory

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Seeded.Absorb

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

variable [Bindings] {initial s t : RamState} {boundary : ReturnBoundary} {original state : State}

theorem Context.after (current : Context initial s state) (frame : FrameState initial t)
    (drbg : DrbgAt t (initial.regValue .rdi) state)
    (bufferPointer : t.regValue .r12 = scratch initial + 320)
    (copied : ∀ i < 24, t.external[scratch initial + 64 + BitVec.ofNat 64 i]? =
      s.external[scratch initial + 64 + BitVec.ofNat 64 i]?) : Context initial t state := by
  have word (offset : Nat) (bound : offset + 8 ≤ 24) :
      memLoad t.external (scratch initial + 64 + BitVec.ofNat 64 offset) 64 =
        memLoad s.external (scratch initial + 64 + BitVec.ofNat 64 offset) 64 := by
    apply memLoad_congr
    intro i hi
    exact congrArg (fun x : Option UInt8 => x.getD 0) (P256.Proofs.Program.copied_sub copied bound i hi)
  refine ⟨frame, drbg, bufferPointer, ?_, ?_, ?_⟩
  · exact (show memLoad t.external (scratch initial + 72) 64 =
        memLoad s.external (scratch initial + 72) 64 from by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using word 8 (by decide)).trans current.savedPointer
  · exact (show memLoad t.external (scratch initial + 64) 64 =
        memLoad s.external (scratch initial + 64) 64 from by
      simpa only [BitVec.add_zero] using word 0 (by decide)).trans current.savedValue
  · exact (show memLoad t.external (scratch initial + 80) 64 =
        memLoad s.external (scratch initial + 80) 64 from by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using word 16 (by decide)).trans current.savedEnd

theorem Context.after_agrees {components : List Component}
    (pre : DrbgCalleePre initial boundary 0x109f30 1856 original)
    (current : Context initial s state) (ready : ReadyToStep t)
    (agrees : AgreesExcept components s t) (rsp : .reg 4 ∉ components)
    (buffer : .reg 12 ∉ components)
    (writes : ∀ c ∈ components, ∀ a, c.Covers a →
      (ScalarFrame.workRegion initial 1856).Contains a.toNat)
    (copied : ∀ i < 24, t.external[scratch initial + 64 + BitVec.ofNat 64 i]? =
      s.external[scratch initial + 64 + BitVec.ofNat 64 i]?)
    (hdf : Component.df ∉ components := by component_not_mem)
    (hmxcsr : Component.mxcsr ∉ components := by component_not_mem)
    (hfcw : Component.fcw ∉ components := by component_not_mem) : Context initial t state := by
  exact current.after (Update.Absorb.frame_after pre current.toFrameState ready agrees rsp writes)
    (Update.Absorb.drbg_after pre current.drbg agrees writes)
    ((agrees.read (n := 64) (r := 12) buffer).trans current.bufferPointer) copied

theorem Context.after_nomem {components : List Component}
    (pre : DrbgCalleePre initial boundary 0x109f30 1856 original)
    (current : Context initial s state) (ready : ReadyToStep t)
    (agrees : AgreesExcept components s t) (rsp : .reg 4 ∉ components)
    (buffer : .reg 12 ∉ components) (noMem : ∀ c ∈ components, ∀ a, ¬ c.Covers a)
    (hdf : Component.df ∉ components := by component_not_mem)
    (hmxcsr : Component.mxcsr ∉ components := by component_not_mem)
    (hfcw : Component.fcw ∉ components := by component_not_mem) :
    Context initial t state :=
  current.after_agrees pre ready agrees rsp buffer
    (fun c hc a ha => (noMem c hc a ha).elim)
    (fun _ _ => by rw [agrees.external noMem])

theorem Context.after_copy {count destinationOffset : Nat} {ret address : BitVec 64}
    (pre : DrbgCalleePre initial boundary 0x109f30 1856 original)
    (current : Context initial s state)
    (result : Update.Absorb.SeedCopyResult initial s t boundary count destinationOffset ret address)
    (bound : destinationOffset ≤ 528) : Context initial t state := by
  refine current.after result.toFrameState ?_
    ((result.calleeSaved .r12 (by simp)).trans current.bufferPointer) ?_
  · apply current.drbg.copy
    intro i hi
    apply result.writes
    intro region member inside
    have eq : region = ScalarFrame.workRegion initial 1856 := by simpa using member
    subst region
    exact pre.separation _
      (memoryRegion_contains_add pre.stateBounded (Nat.le_refl _) (Nat.le_refl _) hi)
      (Update.Prepare.work_substack pre inside)
  · intro i hi
    have addressEq : scratch initial + 64 = stackPtr initial - 616 := by
      simp only [scratch]; bv_omega
    rw [addressEq]
    exact result.stack_byte (offset := 616) (len := 24) pre (by omega) (by decide) (by decide) (.inl (by omega)) hi

def InnerWrites (initial : RamState) (components : List Component) : Prop :=
  ∀ c ∈ components, ∀ a, c.Covers a →
    (.mem (scratch initial + 320) 104 : Component).Covers a

omit [Bindings] in
theorem inner_bytes {components : List Component}
    (agrees : AgreesExcept components s t) (writes : InnerWrites initial components)
    {offset len : Nat} (bound : offset + len < 2^64) (apart : offset + len ≤ 320 ∨ 424 ≤ offset) :
    ∀ i < len, t.external[scratch initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      s.external[scratch initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  intro i hi
  apply agrees.byte
  intro c hc cover
  obtain ⟨j, hj, eq⟩ := writes c hc _ cover
  bv_omega

theorem Context.after_inner {components : List Component}
    (pre : DrbgCalleePre initial boundary 0x109f30 1856 original)
    (current : Context initial s state) (ready : ReadyToStep t)
    (agrees : AgreesExcept components s t) (rsp : .reg 4 ∉ components)
    (buffer : .reg 12 ∉ components) (writes : InnerWrites initial components)
    (hdf : Component.df ∉ components := by component_not_mem)
    (hmxcsr : Component.mxcsr ∉ components := by component_not_mem)
    (hfcw : Component.fcw ∉ components := by component_not_mem) : Context initial t state := by
  apply current.after_agrees pre ready agrees rsp buffer
  · intro c hc a cover
    exact Update.Prepare.work_contains_scratch pre (by decide : 320 + 104 ≤ 632) (writes c hc a cover)
  · exact inner_bytes agrees writes (by decide) (.inl (by decide))

end P256.Proofs.Nonce.Update.Seeded.Absorb
