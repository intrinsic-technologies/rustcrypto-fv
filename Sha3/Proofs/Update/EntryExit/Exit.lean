import Sha3.Proofs.Update.EntryExit.Entry
import Sha3.Proofs.Update.EntryExit.Epilogue
import Sha3.Proofs.Stores.ByteMov

namespace Sha3.Proofs.Update

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

theorem cursorStore_lanes {pointer : BitVec 64} {s t : RamState}
    (ha : AgreesExcept [.mem (pointer + 200#64) 1, .rip] s t) :
    Permutation.memoryLanes pointer t = Permutation.memoryLanes pointer s := by
  funext lane
  apply memLoad_congr
  intro j hj
  change (t.external[pointer + BitVec.ofNat 64 (8 * lane.val) + BitVec.ofNat 64 j]?).getD 0 =
    (s.external[pointer + BitVec.ofNat 64 (8 * lane.val) + BitVec.ofNat 64 j]?).getD 0
  apply congrArg (fun x : Option UInt8 ↦ x.getD 0)
  apply ha.byte
  intro c hc hcover
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · obtain ⟨i, hi, he⟩ := hcover
    have hi0 : i = 0 := by omega
    subst i
    rw [BitVec.add_zero, BitVec.add_assoc, ← BitVec.ofNat_add] at he
    have hn := congrArg BitVec.toNat ((BitVec.add_right_inj pointer).mp he)
    have hl := lane.isLt
    simp only [BitVec.toNat_ofNat] at hn
    omega
  · exact hcover.elim

theorem cursorStore_advance [Bindings] {v : Variant} {initial s : RamState}
    {bytes : ByteArray} {state result : Incremental.State}
    (hc : CallContext v initial bytes state) (h : BodyInvariant initial s)
    {boundary : ReturnBoundary} (hb : ¬ InProgram boundary.rip)
    (hip : s.RIP = cursorWriteAddress v)
    (hlanes : Permutation.memoryLanes (initial.regValue .rsi) s = result.lanes)
    (hpointer : s.regValue .rdi = initial.regValue .rsi + 200#64)
    (hcursor : s.regValue .rcx = BitVec.ofNat 64 result.cursor)
    (hlt : result.cursor < v.rate) :
    ∃ t, Advances boundary 1 s t ∧ BodyInvariant initial t ∧
      t.RIP = cursorWriteAddress v + 2#64 ∧ StateAt (initial.regValue .rsi) result t := by
  let am : AddrMode := .base 7 .none
  have hptr : storeAddrAt (cursorWriteAddress v) am (2 + am.tail.length) s =
      initial.regValue .rsi + 200#64 := by
    change s.regValue .rdi + 0#64 = _
    rw [BitVec.add_zero]
    rw [hpointer]
  have hcode : CodeIn Extracted.programImage s := CodeIn.of_loaded h.loaded
    (SectionsLow.codeLow programSections_low)
  have hpre : StorePreReadable (cursorWriteAddress v)
      (storeAddrAt (cursorWriteAddress v) am (2 + am.tail.length)) 1 s := by
    refine ⟨⟨hip, ?_⟩, ?_⟩
    · rw [hptr]
      exact readable_slice (h.readable hc.stateRead) 200 1 (by decide)
    · intro i hi
      have hi0 : i = 0 := by omega
      subst i
      rw [hptr, BitVec.add_zero]
      apply hc.avoids (stateRegion initial) (by simp [writeRegions]) _ _ ∘ Or.inr
      have hl := hc.stateRead.low
      simp only [stateRegion, MemoryRegion.Contains, BitVec.toNat_add, BitVec.toNat_ofNat]
      constructor <;> omega
  have hstep := mov_m8_r8_effect_step_of_readable (cursorWriteAddress v) 1
    (by decide +kernel) am (by unfold am AddrMode.Valid; decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have hbytes : (0x88 :: am.modrm 1 :: am.tail) = cursorStoreBytes := by decide +kernel
  obtain ⟨t, hrun, hr, he⟩ := hstep.advances h.ready
    (hcode.mono (by rw [hbytes]; exact cursorStoreCode_subset v)) hpre (by
      change cursorWriteAddress v + 2#64 ≠ boundary.rip
      intro heq
      apply hb (heq ▸ ?_)
      simpa only [BitVec.add_zero, BitVec.ofNat_eq_ofNat] using
        epiloguePC_inProgram v (k := 0) (by decide))
  have ha : AgreesExcept [.mem (initial.regValue .rsi + 200#64) 1, .rip] s t := by
    have ha := he.agrees
    simp only [storeEffect_components, Nat.reduceDiv] at ha
    rw [hptr] at ha
    exact ha
  have hw : StateWrites initial [.mem (initial.regValue .rsi + 200#64) 1, .rip] := by
    intro c hcm address hcover
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hcm
    rcases hcm with rfl | rfl
    · obtain ⟨i, hi, rfl⟩ := hcover
      have hi0 : i = 0 := by omega
      subst i
      exact ⟨200, by decide, BitVec.add_zero _⟩
    · exact hcover.elim
  refine ⟨t, hrun, h.of_stateWrites hc hr ha hw (by simp), he.rip,
    ⟨(cursorStore_lanes ha).trans hlanes, ?_⟩⟩
  have hv := he.writes
  change (Operand.mem (s.regValue .rdi + 0#64) : Operand 8).read t =
    (s.regValue .rcx).setWidth 8 at hv
  rw [BitVec.add_zero, hpointer, hcursor] at hv
  simp only [Update.cursor, BitVec.ofNat_eq_ofNat]
  rw [hv]
  have hrate := v.rate_le
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem epiloguePre_of_body [Bindings] {v : Variant} {initial s : RamState}
    {bytes : ByteArray} {state : Incremental.State} (hc : CallContext v initial bytes state)
    (h : BodyInvariant initial s) (hip : s.RIP = cursorWriteAddress v + 2#64) :
    EpiloguePre (cursorWriteAddress v + 2#64) initial s := by
  refine ⟨hip, h.stack, h.saved, ?_, ?_⟩
  · intro i
    have hread := stack_return_readable hc.stack
    have hlo := stack_sub_low hc.stack (show 56 ≤ stackBytes by decide)
    have hu := hc.stack.2.2.1
    change 328 ≤ (initial.regValue .rsp).toNat at hu
    have he : (epilogueSlot initial i.val).toNat =
        (initial.regValue .rsp).toNat - 56 + (8 + 8 * i.val) := by
      unfold epilogueSlot frameBase
      simp only [BitVec.ofNat_eq_ofNat]
      rw [BitVec.toNat_add, stack_sub_toNat hc.stack.2.2.1 (show 56 ≤ stackBytes by decide)]
      simp only [BitVec.toNat_ofNat]
      have hi := i.isLt
      have hs := (initial.regValue .rsp).isLt
      have hlow := hread.low
      omega
    apply memReadable_of_region hc.stack.1 _
    · change (initial.regValue .rsp).toNat - 328 ≤ (epilogueSlot initial i.val).toNat
      rw [he]
      omega
    · change (epilogueSlot initial i.val).toNat + 8 ≤
        (initial.regValue .rsp).toNat - 328 +
          ((initial.regValue .rsp).toNat + 8 - ((initial.regValue .rsp).toNat - 328))
      rw [he]
      have hi := i.isLt
      omega
    · intro a hin
      exact Option.isSome_iff_exists.mp (h.grows a
        (Option.isSome_iff_exists.mpr (hc.stack.2.1 a hin)))
  · obtain ⟨b, hb⟩ := hc.target
    exact ((SectionsLow.codeLow programSections_low) _ hb)

theorem exit_advance [Bindings] {v : Variant} {initial s : RamState}
    {bytes : ByteArray} {state result : Incremental.State}
    (hc : CallContext v initial bytes state) (h : BodyInvariant initial s)
    {boundary : ReturnBoundary} (hb : ¬ InProgram boundary.rip)
    (hip : s.RIP = cursorWriteAddress v)
    (hlanes : Permutation.memoryLanes (initial.regValue .rsi) s = result.lanes)
    (hpointer : s.regValue .rdi = initial.regValue .rsi + 200#64)
    (hcursor : s.regValue .rcx = BitVec.ofNat 64 result.cursor)
    (hlt : result.cursor < v.rate) :
    ∃ t, Advances boundary 9 s t ∧ ReadyToStep t ∧ CallResult initial t result := by
  obtain ⟨u, hstore, hu, hipu, hstate⟩ := cursorStore_advance hc h hb hip hlanes hpointer hcursor hlt
  have hp := epiloguePre_of_body hc hu hipu
  have hcode := CodeIn.of_loaded hu.loaded (SectionsLow.codeLow programSections_low)
  have hbound : ∀ k ≤ 6, epiloguePopPC (cursorWriteAddress v + 2#64) k ≠ boundary.rip := by
    intro k hk he
    apply hb (he ▸ epiloguePC_inProgram v ?_)
    have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
    rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  obtain ⟨t, hrun, hr, _, ht⟩ := epilogue_advance _ initial (epilogueCode_subset v)
    hbound (fun he ↦ hb (he ▸ hc.target)) u hu.ready hcode hp
  refine ⟨t, hstore.trans hrun, hr, ht.rip, ht.stack,
    hstate.of_bytes_eq (by intro i hi; rw [ht.memory]), ht.saved, ?_,
    fun a hm ↦ ht.agrees.grow a (hu.grows a hm), (ht.agrees.scalarFrame_eq (by rfl)).trans hu.rest⟩
  intro address hout
  rw [ht.memory]
  exact hu.memory address hout

end Sha3.Proofs.Update
