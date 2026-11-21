import P256.Proofs.Common.Instructions.RepMovsqAny.Loop

set_option autoImplicit false

namespace P256.Proofs.Common.Instructions.RepMovsqAny

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

structure RepMovsqPre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  srcLow : (rsi.read s).toNat + 8 * (rcx.read s).toNat ≤ 2^32
  dstLow : (rdi.read s).toNat + 8 * (rcx.read s).toNat ≤ 2^32
  srcMem : ∀ i < 8 * (rcx.read s).toNat, (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 8 * (rcx.read s).toNat, (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  disjoint : (rsi.read s).toNat + 8 * (rcx.read s).toNat ≤ (rdi.read s).toNat ∨
    (rdi.read s).toNat + 8 * (rcx.read s).toNat ≤ (rsi.read s).toNat
  dstTables : PageTableEntriesApart (rdi.read s).toNat (8 * (rcx.read s).toNat)
  dstCode : RangeApart (rdi.read s) (8 * (rcx.read s).toNat) p 3

theorem rep_movsq_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF3, rex, 0xA5]) s) (hpre : RepMovsqPre p s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF3, rex, 0xA5]) t ∧ (repMovsqEffect p s).Holds s t := by
  intro t
  have hcodeS : BytesAt s s.RIP [0xF3, rex, 0xA5] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  suffices hh : ReadyToStep t ∧ (repMovsqEffect p s).Holds s t from
    ⟨hh.1, hh.2.codeIn (repMovsqEffect_avoids rex hpre.dstCode) hcode, hh.2⟩
  have hrep := h.ready.repeatClear
  rcases hn : (rcx.read s).toNat with _ | k
  ·
    have hz : rcx.read s = 0 := BitVec.eq_of_toNat_eq hn
    have ht : t = repMovsqZeroAfter s := by
      simp only [t, hn]
      exact nextState_of_step (rep_movsq_step_zero s h.midRep rex hrex hcodeS hlow hz)
    rw [ht]
    have hag : AgreesExcept [.rip] s (repMovsqZeroAfter s) :=
      (AgreesExcept.repMovsqZero s).of_clearRep hrep (repMovsqZeroAfter_repeat s)
    refine ⟨ReadyToStep.of_agreesExcept h hag h.memory.tables, ?_, ?_, trivial, ?_⟩
    · rw [repMovsqZeroAfter_rip s h.ready.msr, hpre.rip]; rfl
    · refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hag.read (by simp), hn]; simp
      · rw [hag.read (by simp), hn]; simp
      · rw [hag.read (by simp), hz]
      · apply BitVec.eq_of_getLsbD_eq
        intro i hi
        have hi' : i < 64 * (rcx.read s).toNat := hi
        omega
    · exact hag.mono (by simp)
  ·
    have hc : rcx.read s = BitVec.ofNat 64 (k + 1) := by
      apply BitVec.eq_of_toNat_eq
      have := hpre.srcLow
      rw [hn, BitVec.toNat_ofNat]
      omega
    have hready : ReadyRepLoop rex s (k + 1) :=
      ⟨h.midRep, hpre.df, hcodeS, hlow, hc, hn ▸ hpre.srcLow, hn ▸ hpre.dstLow, hn ▸ hpre.srcMem,
        hn ▸ hpre.dstMem, hn ▸ hpre.disjoint, hn ▸ hpre.dstTables, hpre.rip ▸ hn ▸ hpre.dstCode⟩
    have hd := rep_movsq_loop hstride hrex k s hready
    have ht : t = nextStates (k + 1) s := by
      simp only [t, hn, show max (k + 1) 1 = k + 1 by omega]
    rw [ht]
    have hag := hd.agrees
    rw [clearRep_eq hrep] at hag
    refine ⟨hd.ready, ?_, ?_, trivial, ?_⟩
    · rw [hd.rip, hpre.rip]; rfl
    · refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hd.rsiAfter, hn]
      · rw [hd.rdiAfter, hn]
      · exact hd.rcxZero
      · simp only [Operand.read]
        apply memLoad_congr
        intro i hi
        have hi' : i < 64 * (rcx.read s).toNat / 8 := hi
        exact memByte_congr (hd.copy i (by omega))
    · rw [repMovsqEffect_components, hn]
      exact hag.mono (by simp)

theorem ReadyRepLoop.advances [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    {rex : UInt8} (hrex : RexWPrefix rex.toBitVec) (boundary : ReturnBoundary)
    (count : Nat) (s : RamState) (h : ReadyRepLoop rex s (count + 1))
    (hstart : s.RIP ≠ boundary.rip) (hend : BitVec.add s.RIP 3#64 ≠ boundary.rip) :
    Advances boundary (count + 1) s (nextStates (count + 1) s) := by
  induction count generalizing s with
  | zero =>
    have hs := h.step hstride hrex (by omega)
    have hi : (repMovsqAfter s).RIP ≠ boundary.rip := by
      rw [repMovsqAfter_rip s h.ready.msr]
      split <;> assumption
    rw [nextStates_one, nextState_of_step hs]
    exact Advances.of_step hs (.inl hi)
  | succ k ih =>
    have hs := h.step hstride hrex (by omega)
    have hrip : (repMovsqAfter s).RIP = s.RIP := by
      rw [repMovsqAfter_rip s h.ready.msr, h.counter]
      simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := k + 1) (by omega)
        (by have := h.srcLow; omega), ↓reduceIte]
    have ha : Advances boundary 1 s (repMovsqAfter s) :=
      Advances.of_step hs (.inl (by rw [hrip]; exact hstart))
    have hb := ih (repMovsqAfter s) h.next (by rw [hrip]; exact hstart)
      (by rw [hrip]; exact hend)
    rw [nextStates_succ, nextState_of_step hs]
    simpa only [Nat.add_comm 1 (k + 1)] using ha.trans hb

theorem rep_movsq_advances [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (boundary : ReturnBoundary) (p : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec)
    (s : RamState) (h : ReadyToStep s) (hcode : CodeIn (codeRange p [0xf3, rex, 0xa5]) s)
    (hpre : RepMovsqPre p s) (hstart : p ≠ boundary.rip) (hend : p + 3#64 ≠ boundary.rip) :
    Advances boundary (max (rcx.read s).toNat 1) s (nextStates (max (rcx.read s).toNat 1) s) := by
  have hcodeS : BytesAt s s.RIP [0xf3, rex, 0xa5] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  rcases hn : (rcx.read s).toNat with _ | k
  · have hz : rcx.read s = 0 := BitVec.eq_of_toNat_eq hn
    have hs := rep_movsq_step_zero s h.midRep rex hrex hcodeS hlow hz
    simp only [Nat.max_eq_right (show 0 ≤ 1 by omega), nextStates_one, nextState_of_step hs]
    apply Advances.of_step hs
    left
    rw [repMovsqZeroAfter_rip s h.ready.msr, hpre.rip]
    exact hend
  · have hc : rcx.read s = BitVec.ofNat 64 (k + 1) := by
      rw [← hn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have hr : ReadyRepLoop rex s (k + 1) :=
      ⟨h.midRep, hpre.df, hcodeS, hlow, hc, hn ▸ hpre.srcLow, hn ▸ hpre.dstLow,
        hn ▸ hpre.srcMem, hn ▸ hpre.dstMem, hn ▸ hpre.disjoint,
        hn ▸ hpre.dstTables, hpre.rip ▸ hn ▸ hpre.dstCode⟩
    rw [Nat.max_eq_left (by omega)]
    exact hr.advances hstride hrex boundary k s (hpre.rip ▸ hstart) (hpre.rip ▸ hend)

theorem rep_movsq_copy [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec)
    (s : RamState) (h : ReadyToStep s) (hcode : CodeIn (codeRange p [0xf3, rex, 0xa5]) s)
    (hpre : RepMovsqPre p s) :
    ∀ i < 8 * (rcx.read s).toNat,
      (nextStates (max (rcx.read s).toNat 1) s).external[rdi.read s + BitVec.ofNat 64 i]? =
        s.external[rsi.read s + BitVec.ofNat 64 i]? := by
  rcases hn : (rcx.read s).toNat with _ | k
  · intro i hi; omega
  · have hc : rcx.read s = BitVec.ofNat 64 (k + 1) := by
      rw [← hn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have hr : ReadyRepLoop rex s (k + 1) :=
      ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt,
        hpre.rip ▸ hcode.low (by simp) (by simp), hc, hn ▸ hpre.srcLow, hn ▸ hpre.dstLow,
        hn ▸ hpre.srcMem, hn ▸ hpre.dstMem, hn ▸ hpre.disjoint,
        hn ▸ hpre.dstTables, hpre.rip ▸ hn ▸ hpre.dstCode⟩
    rw [Nat.max_eq_left (by omega)]
    exact (rep_movsq_loop hstride hrex k s hr).copy


end P256.Proofs.Common.Instructions.RepMovsqAny
