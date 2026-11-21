import P256.Proofs.Nonce.Update.Seeded.Prepare.Stack
import P256.Proofs.Nonce.Update.Seeded.Prepare.State
import P256.Proofs.Nonce.Update.Prepare.Memory

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Seeded.Prepare

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem Context.of_copied [Bindings] {initial s t : RamState} {state : State}
    (current : Context initial s state) (frame : FrameState initial t)
    (drbg : DrbgAt t (initial.regValue .rdi) state)
    (drbgPointer : t.regValue .rbx = initial.regValue .rdi)
    (descriptors : t.regValue .rbp = initial.regValue .rsi)
    (copied : ∀ i < 24,
      t.external[scratch initial + 64 + BitVec.ofNat 64 i]? =
        s.external[scratch initial + 64 + BitVec.ofNat 64 i]?) :
    Context initial t state := by
  have word (offset : Nat) (bound : offset + 8 ≤ 24) :
      memLoad t.external (scratch initial + 64 + BitVec.ofNat 64 offset) 64 =
        memLoad s.external (scratch initial + 64 + BitVec.ofNat 64 offset) 64 := by
    apply memLoad_congr
    intro i hi
    exact congrArg (fun x : Option UInt8 => x.getD 0) (copied_sub copied bound i hi)
  refine ⟨frame, drbg, drbgPointer, ?_, ?_, descriptors, ?_⟩
  · exact (show memLoad t.external (scratch initial + 72) 64 =
        memLoad s.external (scratch initial + 72) 64 from by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using word 8 (by decide)).trans current.savedPointer
  · exact (show memLoad t.external (scratch initial + 64) 64 =
        memLoad s.external (scratch initial + 64) 64 from by
      simpa only [BitVec.add_zero] using word 0 (by decide)).trans current.savedValue
  · exact (show memLoad t.external (scratch initial + 80) 64 =
        memLoad s.external (scratch initial + 80) 64 from by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using word 16 (by decide)).trans current.savedEnd

theorem Context.after_agrees [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
    {original state : State} {components : List Component}
    (pre : DrbgCalleePre initial boundary 0x109f30 1856 original)
    (current : Context initial s state) (ready : ReadyToStep t)
    (agrees : AgreesExcept components s t)
    (registers : ∀ r ∈ ([3,4,5] : List (BitVec 5)), .reg r ∉ components)
    (writes : ∀ c ∈ components, ∀ a, c.Covers a →
      (ScalarFrame.workRegion initial 1856).Contains a.toNat)
    (copied : ∀ i < 24,
      t.external[scratch initial + 64 + BitVec.ofNat 64 i]? =
        s.external[scratch initial + 64 + BitVec.ofNat 64 i]?)
    (hdf : Component.df ∉ components := by component_not_mem)
    (hmxcsr : Component.mxcsr ∉ components := by component_not_mem)
    (hfcw : Component.fcw ∉ components := by component_not_mem) : Context initial t state := by
  have frame := current.toFrameState.after_effect pre.callee (by decide) ready agrees
    (fun c hc a ha => ⟨ScalarFrame.workRegion initial 1856, by simp, writes c hc a ha⟩)
    (registers 4 (by simp)) hdf hmxcsr hfcw
  apply current.of_copied frame _
    ((agrees.read (n := 64) (r := 3) (registers 3 (by simp))).trans current.drbgPointer)
    ((agrees.read (n := 64) (r := 5) (registers 5 (by simp))).trans current.descriptors) copied
  apply current.drbg.copy
  intro i hi
  apply agrees.byte
  intro c hc ha
  exact pre.separation _
    (memoryRegion_contains_add pre.stateBounded (Nat.le_refl _) (Nat.le_refl _) hi)
    ((Update.Prepare.work_substack pre) (writes c hc _ ha))

end P256.Proofs.Nonce.Update.Seeded.Prepare
