import Hkdf.Proofs.Common.Memory.Copy.Movsb.Loop
import X86Proofs.Program.Execution

namespace Hkdf.Proofs.Common.Memory.Copy.Movsb
open X86Proofs X86 X86.Machine X86.UserProcess

theorem ReadyRepMovsbLoop.advances [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (boundary : ReturnBoundary)
    (count : Nat) (s : RamState) (h : ReadyRepMovsbLoop s (count + 1))
    (hstart : s.RIP ≠ boundary.rip) (hend : BitVec.add s.RIP 2#64 ≠ boundary.rip) :
    Advances boundary (count + 1) s (nextStates (count + 1) s) := by
  induction count generalizing s with
  | zero =>
    have hs := h.step hstride (by omega)
    have hi : (repMovsbAfter s).RIP ≠ boundary.rip := by
      rw [repMovsbAfter_rip s h.ready.msr]
      split <;> assumption
    rw [nextStates_one, nextState_of_step hs]
    exact Advances.of_step hs (.inl hi)
  | succ k ih =>
    have hs := h.step hstride (by omega)
    have hrip : (repMovsbAfter s).RIP = s.RIP := by
      rw [repMovsbAfter_rip s h.ready.msr, h.counter]
      simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := k + 1) (by omega)
        (by have := h.srcLow; omega), ↓reduceIte]
    have ha : Advances boundary 1 s (repMovsbAfter s) :=
      Advances.of_step hs (.inl (by rw [hrip]; exact hstart))
    have hb := ih (repMovsbAfter s) h.next (by rw [hrip]; exact hstart)
      (by rw [hrip]; exact hend)
    rw [nextStates_succ, nextState_of_step hs]
    simpa only [Nat.add_comm 1 (k + 1)] using ha.trans hb

theorem rep_movsb_advances [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (boundary : ReturnBoundary) (p : BitVec 64)
    (s : RamState) (h : ReadyToStep s) (hcode : CodeIn (codeRange p [0xf3, 0xa4]) s)
    (hpre : RepMovsbPre p s) (hstart : p ≠ boundary.rip) (hend : p + 2#64 ≠ boundary.rip) :
    Advances boundary (max (rcx.read s).toNat 1) s (nextStates (max (rcx.read s).toNat 1) s) := by
  have hcodeS : BytesAt s s.RIP [0xf3, 0xa4] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  rcases hn : (rcx.read s).toNat with _ | k
  · have hz : rcx.read s = 0 := BitVec.eq_of_toNat_eq hn
    have hs := rep_movsb_step_zero s h.midRep hcodeS hlow hz
    simp only [Nat.max_eq_right (show 0 ≤ 1 by omega), nextStates_one, nextState_of_step hs]
    apply Advances.of_step hs
    left
    rw [repMovsbZeroAfter_rip s h.ready.msr, hpre.rip]
    exact hend
  · have hc : rcx.read s = BitVec.ofNat 64 (k + 1) := by
      rw [← hn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have hr : ReadyRepMovsbLoop s (k + 1) :=
      ⟨h.midRep, hpre.df, hcodeS, hlow, hc, hn ▸ hpre.srcLow, hn ▸ hpre.dstLow,
        hn ▸ hpre.srcMem, hn ▸ hpre.dstMem, hn ▸ hpre.disjoint,
        hn ▸ hpre.dstTables, hpre.rip ▸ hn ▸ hpre.dstCode⟩
    rw [Nat.max_eq_left (by omega)]
    exact hr.advances hstride boundary k s (hpre.rip ▸ hstart) (hpre.rip ▸ hend)

theorem rep_movsb_copy [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64)
    (s : RamState) (h : ReadyToStep s) (hcode : CodeIn (codeRange p [0xf3, 0xa4]) s)
    (hpre : RepMovsbPre p s) :
    ∀ i < (rcx.read s).toNat,
      (nextStates (max (rcx.read s).toNat 1) s).external[rdi.read s + BitVec.ofNat 64 i]? =
        s.external[rsi.read s + BitVec.ofNat 64 i]? := by
  rcases hn : (rcx.read s).toNat with _ | k
  · intro i hi; omega
  · have hc : rcx.read s = BitVec.ofNat 64 (k + 1) := by
      rw [← hn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have hr : ReadyRepMovsbLoop s (k + 1) :=
      ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt,
        hpre.rip ▸ hcode.low (by simp) (by simp), hc, hn ▸ hpre.srcLow, hn ▸ hpre.dstLow,
        hn ▸ hpre.srcMem, hn ▸ hpre.dstMem, hn ▸ hpre.disjoint,
        hn ▸ hpre.dstTables, hpre.rip ▸ hn ▸ hpre.dstCode⟩
    rw [Nat.max_eq_left (by omega)]
    exact (rep_movsb_loop hstride k s hr).copy

theorem rep_movsb_zero [Bindings] (boundary : ReturnBoundary) (p : BitVec 64)
    (s : RamState) (h : ReadyToStep s) (hcode : CodeIn (codeRange p [0xf3, 0xa4]) s)
    (hrip : s.RIP = p) (hcount : rcx.read s = 0) (hend : p + 2#64 ≠ boundary.rip) :
    let t := nextState s
    Advances boundary 1 s t ∧ ReadyToStep t ∧ t.RIP = p + 2#64 ∧
      AgreesExcept [.rip] s t ∧ CodeIn (codeRange p [0xf3, 0xa4]) t := by
  have hs := rep_movsb_step_zero s h.midRep (hrip ▸ hcode.bytesAt)
    (hrip ▸ hcode.low (by simp) (by simp)) hcount
  dsimp only
  rw [nextState_of_step hs]
  have hag : AgreesExcept [.rip] s (repMovsbZeroAfter s) :=
    (AgreesExcept.repMovsbZero s).of_clearRep h.ready.repeatClear (repMovsbZeroAfter_repeat s)
  have hip : (repMovsbZeroAfter s).RIP = p + 2#64 := by
    rw [repMovsbZeroAfter_rip s h.ready.msr, hrip]
    rfl
  refine ⟨Advances.of_step hs (.inl (hip ▸ hend)),
    ReadyToStep.of_agreesExcept h hag h.memory.tables, hip, hag, ?_⟩
  apply CodeIn.of_agreesExcept hag ?_ hcode
  intro x hx c hc hcov
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  subst c
  exact hcov

end Hkdf.Proofs.Common.Memory.Copy.Movsb
