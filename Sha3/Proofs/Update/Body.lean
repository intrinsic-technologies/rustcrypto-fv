import Sha3.Proofs.Update.Completion
import Sha3.Proofs.Update.Composition
import Sha3.Proofs.Update.Partial.Dispatch
import Sha3.Proofs.Update.Partial.ShortCompose
import Sha3.Proofs.Update.Partial.FillCompose
import Sha3.Proofs.Update.PartialLift.Context
import Sha3.Proofs.Update.PartialLift.Permutation

namespace Sha3.Proofs.Update

open X86 X86.Machine X86.UserProcess X86Proofs Sha3.Spec.Program
open Keccak Permutation

theorem body_advance [Bindings] {v : Variant} {initial s : RamState}
    {bytes : ByteArray} {state : Incremental.State} (hc : CallContext v initial bytes state)
    (h : BodyInvariant initial s) (boundary : ReturnBoundary) (hb : ¬InProgram boundary.rip)
    (hip : s.RIP = partialAddress v)
    (hpointer : s.regValue .r15 = initial.regValue .rsi)
    (hcursorPointer : s.regValue .rdi = initial.regValue .rsi + 200) (hsource : s.regValue .rbx = initial.regValue .rdx)
    (hcount : s.regValue .rcx = BitVec.ofNat 64 bytes.size)
    (hposition : s.regValue .rax = BitVec.ofNat 64 state.cursor)
    (hlanes : memoryLanes (initial.regValue .rsi) s = state.lanes) :
    ∃ fuel t, Advances boundary fuel s t ∧ BodyInvariant initial t ∧
      t.RIP = cursorWriteAddress v ∧ t.regValue .rdi = initial.regValue .rsi + 200 ∧
      memoryLanes (initial.regValue .rsi) t =
        (Incremental.update keccakLanes v.rate state bytes).lanes ∧
      t.regValue .rcx = BitVec.ofNat 64
        (Incremental.update keccakLanes v.rate state bytes).cursor := by
  have hcursor_lt := hc.cursor_lt
  have code := CodeIn.of_loaded h.loaded (SectionsLow.codeLow programSections_low)
  have slotAvoid (u : RamState) (hu : BodyInvariant initial u) :
      ∀ i < 8, ¬ (InProgram (u.regValue .rsp + BitVec.ofNat 64 i) ∨
        InPageTables (u.regValue .rsp + BitVec.ofNat 64 i)) := by
    intro i hi
    rw [hu.stack]
    exact hc.avoids _ (by simp [writeRegions]) _ (frameSlot_contains hc hi)
  by_cases hz : state.cursor = 0
  · obtain ⟨u, ha, ru, _, ipu, hremaining, hslot, fu⟩ :=
      Partial.zero_cursor v boundary hb s h.ready code (h.cursorSlot_readable hc)
        (slotAvoid s h) hip (by change s.regValue .rax = 0#64; simpa only [hz] using hposition)
    have hw : ∀ c : Component, c ∈ [.mem (s.regValue .rsp) 8, .reg 12, .flags, .rip] →
        ∀ address, c.Covers address → ∃ i < 8, address = frameBase initial + BitVec.ofNat 64 i := by
      intro c hcm address hcover
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hcm
      rcases hcm with rfl | rfl | rfl | rfl
      · simpa only [Component.Covers, h.stack] using hcover
      all_goals exact hcover.elim
    obtain ⟨iu, lu⟩ := h.of_cursorSlotWrites hc ru fu hw (by simp)
    have hpu : u.regValue .r15 = initial.regValue .rsi :=
      (fu.read (n := 64) (r := 15) (by simp)).trans hpointer
    have hsourceu : u.regValue .rbx = initial.regValue .rdx :=
      (fu.read (n := 64) (r := 3) (by simp)).trans hsource
    have hslotu : (Operand.mem (frameBase initial) : Operand 64).read u = initial.regValue .rsi + 200 := by
      simpa only [h.stack, hcursorPointer] using hslot
    have hremaining' : u.regValue .r12 = BitVec.ofNat 64 bytes.size := hremaining.trans hcount
    obtain ⟨fuel, t, ht, it, ipt, pt, lt, ct⟩ := completion_advance hc iu boundary hb 0
      (Nat.zero_le _) ipu hpu hslotu
      (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hsourceu)
      (by simpa only [Nat.sub_zero] using hremaining')
    have he : (⟨memoryLanes (initial.regValue .rsi) u, 0⟩ : Incremental.State) = state := by
      rw [lu, hlanes]
      exact (state_eq_zero_cursor hz).symm
    simpa only [ByteArray.extract_zero_size, he] using
      (show ∃ fuel t, Advances boundary fuel s t ∧ BodyInvariant initial t ∧
        t.RIP = cursorWriteAddress v ∧ t.regValue .rdi = initial.regValue .rsi + 200 ∧
        memoryLanes (initial.regValue .rsi) t =
          (Incremental.update keccakLanes v.rate ⟨memoryLanes (initial.regValue .rsi) u, 0⟩
            (bytes.extract 0 bytes.size)).lanes ∧
        t.regValue .rcx = BitVec.ofNat 64
          (Incremental.update keccakLanes v.rate ⟨memoryLanes (initial.regValue .rsi) u, 0⟩
            (bytes.extract 0 bytes.size)).cursor from ⟨_, t, ha.trans ht, it, ipt, pt, lt, ct⟩)
  · obtain ⟨u, ha, ru, _, ipu, hfillCount, hremainingu, fu⟩ := Partial.nonzero_cursor v boundary hb s
      state.cursor bytes.size (Nat.pos_of_ne_zero hz) hc.cursor_lt
      (by have := hc.input_size_lt; omega) h.ready code hip hposition hcount
    have hnomem : ∀ c : Component, c ∈ [.reg 2, .reg 12, .flags, .rip] → ∀ a, ¬c.Covers a := by
      simp [Component.Covers]
    have iu := h.of_stateWrites hc ru fu
      (fun c hc a ha ↦ (hnomem c hc a ha).elim) (by simp)
    have hpu : u.regValue .r15 = initial.regValue .rsi :=
      (fu.read (n := 64) (r := 15) (by simp)).trans hpointer
    have hcu : u.regValue .rdi = initial.regValue .rsi + 200 :=
      (fu.read (n := 64) (r := 7) (by simp)).trans hcursorPointer
    have hsourceu := (fu.read (n := 64) (r := 3) (by simp)).trans hsource
    have hpositionu := (fu.read (n := 64) (r := 0) (by simp)).trans hposition
    have lu : memoryLanes (initial.regValue .rsi) u = state.lanes := by
      rw [← hlanes]
      apply LaneMemory.memoryLanes_eq_of_memByte_eq
      intro address
      rw [fu.external hnomem]
    have he : (⟨memoryLanes (initial.regValue .rsi) u, state.cursor⟩ : Incremental.State) = state := by
      rw [lu]
    by_cases hfill : v.rate - state.cursor ≤ bytes.size
    · let count := v.rate - state.cursor
      obtain ⟨d, ad, rd, cd, ipd, hcf, hrem, fd⟩ :=
        Partial.FillControl.dispatch v boundary hb u ⟨state.cursor, hc.cursor_lt⟩
          (Nat.pos_of_ne_zero hz) iu.ready
          (CodeIn.of_loaded iu.loaded (SectionsLow.codeLow programSections_low))
          (by simpa only [hfill, ↓reduceIte] using ipu) hpositionu hfillCount
      have id := iu.of_stateWrites hc rd fd
        (by
          intro c hcm a hv
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hcm
          rcases hcm with rfl | rfl | rfl | rfl <;> exact hv.elim) (by simp)
      obtain ⟨d', asave, rd', cd', ipd', slot, fs⟩ := Partial.saveCursor v 0x60
        (Or.inr rfl) hb rd cd ipd (id.cursorSlot_readable hc) (slotAvoid d id)
      obtain ⟨id', lanesSave⟩ := id.of_cursorSlotWrites hc rd' fs (by
        intro c hcm address hcover
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hcm
        rcases hcm with rfl | rfl
        · simpa only [Component.Covers, id.stack] using hcover
        · exact hcover.elim) (by simp)
      have hpd : d'.regValue .r15 = initial.regValue .rsi :=
        (fs.read (n := 64) (r := 15) (by simp)).trans
          ((fd.read (n := 64) (r := 15) (by simp)).trans hpu)
      have hsd : d'.regValue .rbx = initial.regValue .rdx :=
        (fs.read (n := 64) (r := 3) (by simp)).trans
          ((fd.read (n := 64) (r := 3) (by simp)).trans hsourceu)
      have hposd : d'.regValue .rax = BitVec.ofNat 64 state.cursor :=
        (fs.read (n := 64) (r := 0) (by simp)).trans
          ((fd.read (n := 64) (r := 0) (by simp)).trans hpositionu)
      have hslotd : (Operand.mem (frameBase initial) : Operand 64).read d' = initial.regValue .rsi + 200 := by
        rw [id.stack] at slot
        exact slot.trans ((fd.read (n := 64) (r := 7) (by simp)).trans hcu)
      have ld : memoryLanes (initial.regValue .rsi) d' = memoryLanes (initial.regValue .rsi) u := by
        rw [lanesSave]
        apply LaneMemory.memoryLanes_eq_of_memByte_eq
        intro address
        rw [fd.external (by simp [Component.Covers])]
      have hed : (⟨memoryLanes (initial.regValue .rsi) d', state.cursor⟩ : Incremental.State) = state := by
        rw [ld, he]
      obtain ⟨initialBytes, hbytes, context⟩ := Partial.Context.of_invariant hc id' hpd hsd hposd
        hc.cursor_lt (show state.cursor + count ≤ v.rate by dsimp only [count]; omega) hfill
      obtain ⟨fuel, t, ht, rt⟩ := Partial.Fill.advance context boundary hb
        (Nat.pos_of_ne_zero hz) rfl
        (by simpa only [BitVec.add_assoc, BitVec.reduceAdd] using ipd')
        (by simpa only [fs.rflags (by simp) (by simp)] using hcf)
        ((fs.read (n := 64) (r := 1) (by simp)).trans hrem)
        ((fs.read (n := 64) (r := 2) (by simp)).trans
          ((fd.read (n := 64) (r := 2) (by simp)).trans hfillCount))
      obtain ⟨w, hw, iw, ipw, hpw, slotw, hsourcew, hremainingw, lw, cw⟩ :=
        rt.permutation_advance hc id' boundary hb hbytes hc.cursor_lt hfill (by omega)
      have hremainingw' : w.regValue .r12 = BitVec.ofNat 64 (bytes.size - count) := by
        rw [hremainingw]
        have heq : d'.regValue .r12 = u.regValue .r12 :=
          (fs.read (n := 64) (r := 12) (by simp)).trans (fd.read (n := 64) (r := 12) (by simp))
        rw [heq]
        change (Operand.reg 12 : Operand 64).read u = _
        rw [hremainingu, BitVec.ofNat_sub_ofNat_of_le _ _ (by have := v.rate_le; omega) hfill]
      obtain ⟨fuel', x, hx, ix, ipx, px, lx, cx⟩ :=
        completion_advance hc iw boundary hb count hfill ipw hpw (slotw.trans hslotd) hsourcew hremainingw'
      have hprefix : Incremental.update keccakLanes v.rate state (bytes.extract 0 count) =
          ⟨memoryLanes (initial.regValue .rsi) w, 0⟩ := by
        rw [hed] at lw cw
        rw [state_eq_zero_cursor cw, lw]
      have hall := update_split keccakLanes v.rate state bytes count hfill
      rw [hprefix] at hall
      rw [← hall] at lx cx
      exact ⟨_, x, (((ha.trans ad).trans asave).trans ht).trans (hw.trans hx), ix, ipx, px, lx, cx⟩
    · have hshort : state.cursor + bytes.size < v.rate := by have := hc.cursor_lt; omega
      obtain ⟨initialBytes, hbytes, context⟩ := Partial.Context.of_invariant hc iu hpu hsourceu hpositionu
        hc.cursor_lt (Nat.le_of_lt hshort) (Nat.le_refl _)
      obtain ⟨fuel, t, ht, rt⟩ := Partial.Short.advance context boundary hb hshort
        (by simpa only [hfill, ↓reduceIte] using ipu)
        ((fu.read (n := 64) (r := 1) (by simp)).trans hcount)
      obtain ⟨lt, ct⟩ := rt.incremental hbytes (by have := v.rate_le; omega) hshort
      rw [he] at lt ct
      exact ⟨_, t, ha.trans ht, Partial.bodyInvariant_of_frame hc iu rt.ready rt.frame,
        rt.rip, rt.pointerReg.trans hcu, lt, ct⟩

end Sha3.Proofs.Update
