import P256.Proofs.Nonce.UpdateValue.Absorb.Mathematics
import P256.Proofs.Nonce.UpdateValue.Absorb.State
import P256.Proofs.Nonce.UpdateValue.Prepare.Memory

set_option autoImplicit false

namespace P256.Proofs.Nonce.UpdateValue.Absorb.Buffer

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

variable [Bindings] {initial s t : RamState} {boundary : ReturnBoundary} {state : State}

def region (initial : RamState) : MemoryRegion :=
  .mk (stackPtr initial - 320).toNat 64

theorem region_bounded (pre : UpdateValuePre initial boundary state) :
    (region initial).Bounded := by
  change (stackPtr initial - BitVec.ofNat 64 320).toNat + 64 < 2^32
  rw [stack_sub_toNat pre.stack (by decide)]
  have := stack_bounds pre.stack
  omega

theorem region_work (pre : UpdateValuePre initial boundary state)
    {a : Nat} (inside : (region initial).Contains a) :
    (ScalarFrame.workRegion initial 1168).Contains a := by
  have bounds := stack_bounds pre.stack
  change (stackPtr initial - BitVec.ofNat 64 320).toNat ≤ a ∧
    a < (stackPtr initial - BitVec.ofNat 64 320).toNat + 64 at inside
  rw [stack_sub_toNat pre.stack (by decide)] at inside
  change (stackPtr initial).toNat - 1168 ≤ a ∧
    a < (stackPtr initial).toNat - 1168 + (1168 - 48)
  constructor <;> omega

theorem frame_after {components : List Component}
    (pre : UpdateValuePre initial boundary state) (frame : FrameState initial s)
    (ready : ReadyToStep t) (agrees : AgreesExcept components s t)
    (writes : WritesWithin components #v[region initial])
    (rsp : .reg 4 ∉ components)
    (hdf : Component.df ∉ components := by component_not_mem)
    (hmxcsr : Component.mxcsr ∉ components := by component_not_mem)
    (hfcw : Component.fcw ∉ components := by component_not_mem) : FrameState initial t := by
  apply frame.after_effect pre.callee (by decide) ready agrees (hdf := hdf)
    (hmxcsr := hmxcsr) (hfcw := hfcw)
  · intro c hc a ha
    obtain ⟨r, hr, hin⟩ := writes c hc a ha
    have h : r = region initial := by simpa using hr
    subst r
    exact ⟨ScalarFrame.workRegion initial 1168, by simp, region_work pre hin⟩
  · exact rsp

theorem drbg_after (pre : UpdateValuePre initial boundary state)
    (input : DrbgAt s (initial.regValue .rdi) state)
    (frame : MemoryWriteFrame s t #v[region initial]) :
    DrbgAt t (initial.regValue .rdi) state := by
  apply input.of_frame pre.stateBounded frame
  intro r member a stateContains regionContains
  have eq : r = region initial := by simpa using member
  subst r
  apply pre.separation a stateContains
  exact work_substack pre (region_work pre regionContains)

theorem hmac_preserved (pre : UpdateValuePre initial boundary state)
    (frame : MemoryWriteFrame s t #v[region initial]) :
    ∀ i < 168, i < 64 ∨ 128 ≤ i →
      t.external[scratch initial + 104 + BitVec.ofNat 64 i]? =
        s.external[scratch initial + 104 + BitVec.ofNat 64 i]? := by
  intro i hi apart
  apply frame
  intro r member contains
  have eq : r = region initial := by simpa using member
  subst r
  have startEq : scratch initial + 104 = stackPtr initial - BitVec.ofNat 64 384 := by
    change stackPtr initial - 488 + 104 = _
    rw [show (488 : BitVec 64) = 384 + 104 from rfl,
      ← BitVec.sub_sub, BitVec.sub_add_cancel]
    rfl
  have baseNat := stack_sub_toNat pre.stack (offset := 384) (by decide)
  have bounds := stack_bounds pre.stack
  change (stackPtr initial - BitVec.ofNat 64 320).toNat ≤
    (scratch initial + 104 + BitVec.ofNat 64 i).toNat ∧
    (scratch initial + 104 + BitVec.ofNat 64 i).toNat <
      (stackPtr initial - BitVec.ofNat 64 320).toNat + 64 at contains
  rw [stack_sub_toNat pre.stack (by decide), startEq, BitVec.toNat_add, baseNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 2^64),
    Nat.mod_eq_of_lt (by omega)] at contains
  omega

end P256.Proofs.Nonce.UpdateValue.Absorb.Buffer
