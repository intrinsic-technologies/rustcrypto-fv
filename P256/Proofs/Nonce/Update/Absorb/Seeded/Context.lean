import P256.Proofs.Nonce.Update.Absorb.Seeded.State

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Absorb.Seeded

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem Context.after [Bindings] {initial s t : RamState} {state : State}
    (input : Context initial s state) (frame : FrameState initial t)
    (drbg : ∀ i < 64, t.external[initial.regValue .rdi + BitVec.ofNat 64 i]? =
      s.external[initial.regValue .rdi + BitVec.ofNat 64 i]?)
    (rbp : t.regValue .rbp = s.regValue .rbp)
    (kept : ∀ off ∈ ([64,72,80,424] : List (BitVec 64)), ∀ i < 8,
      t.external[scratch initial + off + BitVec.ofNat 64 i]? =
      s.external[scratch initial + off + BitVec.ofNat 64 i]?) : Context initial t state := by
  have load (off : BitVec 64) (member : off ∈ ([64,72,80,424] : List (BitVec 64))) :
      memLoad t.external (scratch initial + off) 64 = memLoad s.external (scratch initial + off) 64 := by
    apply memLoad_congr
    intro i hi
    exact congrArg (fun x : Option UInt8 => x.getD 0) (kept off member i hi)
  exact ⟨frame, input.drbg.copy drbg, (load 72 (by simp)).trans input.savedPointer,
    (load 64 (by simp)).trans input.savedValue, (load 424 (by simp)).trans input.savedCount,
    rbp.trans input.descriptors, (load 80 (by simp)).trans input.savedEnd⟩

theorem Context.after_nomem [Bindings] {initial s t : RamState} {state : State}
    {boundary : ReturnBoundary} {components : List Component}
    (pre : DrbgCalleePre initial boundary 0x109f30 1856 state)
    (input : Context initial s state) (ready : ReadyToStep t)
    (agrees : AgreesExcept components s t) (rsp : .reg 4 ∉ components)
    (rbp : .reg 5 ∉ components) (noMem : ∀ c ∈ components, ∀ a, ¬ c.Covers a)
    (hdf : Component.df ∉ components := by component_not_mem)
    (hmxcsr : Component.mxcsr ∉ components := by component_not_mem)
    (hfcw : Component.fcw ∉ components := by component_not_mem) :
    Context initial t state := by
  have memory := agrees.external noMem
  exact input.after (frame_after pre input.toFrameState ready agrees rsp (by
    intro c hc a cover; exact (noMem c hc a cover).elim))
    (fun _ _ => by rw [memory]) (agrees.read (n := 64) (r := 5) rbp)
    (fun _ _ _ _ => by rw [memory])

theorem Context.after_copy [Bindings] {initial s t : RamState} {state : State}
    {boundary : ReturnBoundary} {count destinationOffset : Nat} {ret address : BitVec 64}
    (pre : DrbgCalleePre initial boundary 0x109f30 1856 state)
    (input : Context initial s state)
    (result : SeedCopyResult initial s t boundary count destinationOffset ret address)
    (low : 264 + count ≤ destinationOffset) (high : destinationOffset ≤ 528) :
    Context initial t state := by
  apply input.after result.toFrameState
  · intro i hi
    apply result.writes
    intro region member inside
    have eq : region = ScalarFrame.workRegion initial 1856 := by simpa using member
    subst region
    exact pre.separation _
      (memoryRegion_contains_add pre.stateBounded (Nat.le_refl _) (Nat.le_refl _) hi)
      (Prepare.work_substack pre inside)
  · exact result.calleeSaved .rbp (by decide +kernel)
  · intro off member i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · rw [show scratch initial + 64 = stackPtr initial - 616 by simp only [scratch]; bv_omega]
      exact result.stack_byte (offset := 616) (len := 8) pre (by omega) (by decide) (by decide) (by omega) hi
    · rw [show scratch initial + 72 = stackPtr initial - 608 by simp only [scratch]; bv_omega]
      exact result.stack_byte (offset := 608) (len := 8) pre (by omega) (by decide) (by decide) (by omega) hi
    · rw [show scratch initial + 80 = stackPtr initial - 600 by simp only [scratch]; bv_omega]
      exact result.stack_byte (offset := 600) (len := 8) pre (by omega) (by decide) (by decide) (by omega) hi
    · rw [show scratch initial + 424 = stackPtr initial - 256 by simp only [scratch]; bv_omega]
      exact result.stack_byte (offset := 256) (len := 8) pre (by omega) (by decide) (by decide) (by omega) hi

end P256.Proofs.Nonce.Update.Absorb.Seeded
