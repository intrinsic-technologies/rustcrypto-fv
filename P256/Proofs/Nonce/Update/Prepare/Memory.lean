import P256.Proofs.Nonce.Update.Prepare.State
import P256.Proofs.Nonce.Update.Frame

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Prepare

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem work_substack [Bindings] {initial : RamState} {boundary : ReturnBoundary}
    {state : State} (pre : DrbgCalleePre initial boundary 0x109f30 1856 state) {a : Nat}
    (inside : (ScalarFrame.workRegion initial 1856).Contains a) :
    (Stack.region initial 1856).Contains a := by
  change (stackPtr initial).toNat - 1856 ≤ a ∧
    a < (stackPtr initial).toNat - 1856 + 1808 at inside
  have bounds := stack_bounds pre.stack
  change (stackPtr initial).toNat - 1856 ≤ a ∧
    a < (Stack.region initial 1856).start + (Stack.region initial 1856).size
  rw [stack_region_end]
  constructor <;> omega

theorem Context.after_agrees [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
    {state : State} {components : List Component}
    (pre : DrbgCalleePre initial boundary 0x109f30 1856 state)
    (current : Context initial s state) (ready : ReadyToStep t)
    (agrees : AgreesExcept components s t)
    (registers : ∀ r ∈ ([3,4,5,13] : List (BitVec 5)), .reg r ∉ components)
    (writes : ∀ c ∈ components, ∀ a, c.Covers a →
      (ScalarFrame.workRegion initial 1856).Contains a.toNat)
    (hdf : Component.df ∉ components := by component_not_mem)
    (hmxcsr : Component.mxcsr ∉ components := by component_not_mem)
    (hfcw : Component.fcw ∉ components := by component_not_mem) : Context initial t state := by
  have frame := current.toFrameState.after_effect pre.callee (by decide) ready agrees
    (fun c hc a ha => ⟨ScalarFrame.workRegion initial 1856, by simp, writes c hc a ha⟩)
    (registers 4 (by simp)) hdf hmxcsr hfcw
  refine ⟨frame,
    (agrees.read (n := 64) (r := 3) (registers 3 (by simp))).trans current.drbgPointer,
    (agrees.read (n := 64) (r := 5) (registers 5 (by simp))).trans current.descriptors,
    (agrees.read (n := 64) (r := 13) (registers 13 (by simp))).trans current.inputCount, ?_⟩
  apply current.drbg.copy
  intro i hi
  apply agrees.byte
  intro c hc ha
  apply pre.separation _ _ (work_substack pre (writes c hc _ ha))
  exact memoryRegion_contains_add pre.stateBounded (Nat.le_refl _) (Nat.le_refl _) hi

theorem work_contains_scratch [Bindings] {initial : RamState} {boundary : ReturnBoundary}
    {state : State} (pre : DrbgCalleePre initial boundary 0x109f30 1856 state)
    {offset len : Nat} {a : BitVec 64} (span : offset + len ≤ 632)
    (covered : (Component.mem (scratch initial + BitVec.ofNat 64 offset) len).Covers a) :
    (ScalarFrame.workRegion initial 1856).Contains a.toNat := by
  have address : scratch initial + BitVec.ofNat 64 offset =
      stackPtr initial - BitVec.ofNat 64 (680 - offset) := by
    have bound : offset ≤ 680 := by omega
    change stackPtr initial - BitVec.ofNat 64 680 + BitVec.ofNat 64 offset = _
    conv => lhs; rw [show 680 = (680 - offset) + offset by omega]
    rw [BitVec.ofNat_add, ← BitVec.sub_sub, BitVec.sub_add_cancel]
  rw [address] at covered
  exact ScalarFrame.work_contains pre.callee (by omega) (by omega) covered

end P256.Proofs.Nonce.Update.Prepare
