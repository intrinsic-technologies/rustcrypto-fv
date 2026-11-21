import Sha3.Proofs.Memcpy.Movs.RepTriple
import X86Proofs.Instructions.Movs.Execution

namespace X86Proofs
open X86 X86.Machine X86.UserProcess

theorem ReadyMovsLoop.advances {byte : Bool} [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    {rex : UInt8} (hrex : byte = false → RexWPrefix rex.toBitVec) (boundary : ReturnBoundary)
    (count : Nat) (s : RamState) (h : ReadyMovsLoop byte rex s (count + 1))
    (hsp : s.GPR[4] ≠ boundary.rsp) :
    Advances boundary (count + 1) s (nextStates (count + 1) s) := by
  induction count generalizing s with
  | zero =>
    have hkeep : (repMovsAfter byte s).GPR[4] = s.GPR[4] :=
      (AgreesExcept.repMovs byte s).read (n := 64) (r := 4) (by simp)
    have hs := h.step hstride hrex (by omega)
    rw [nextStates_one, nextState_of_step hs]
    exact Advances.of_step hs (.inr (hkeep ▸ hsp))
  | succ k ih =>
    have hkeep : (repMovsAfter byte s).GPR[4] = s.GPR[4] :=
      (AgreesExcept.repMovs byte s).read (n := 64) (r := 4) (by simp)
    have hs := h.step hstride hrex (by omega)
    have ha : Advances boundary 1 s (repMovsAfter byte s) :=
      Advances.of_step hs (.inr (hkeep ▸ hsp))
    have hb := ih (repMovsAfter byte s) h.next (hkeep ▸ hsp)
    rw [nextStates_succ, nextState_of_step hs]
    simpa only [Nat.add_comm 1 (k + 1)] using ha.trans hb

theorem rep_movs_advances {byte : Bool} [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (boundary : ReturnBoundary) (p : BitVec 64) (rex : UInt8) (hrex : byte = false → RexWPrefix rex.toBitVec)
    (s : RamState) (h : ReadyToStep s) (hcode : CodeIn (codeRange p (movsCode byte rex)) s)
    (hpre : RepMovsPre byte p s) (hsp : s.GPR[4] ≠ boundary.rsp) :
    Advances boundary (max (rcx.read s).toNat 1) s (nextStates (max (rcx.read s).toNat 1) s) := by
  have hcodeS : BytesAt s s.RIP (movsCode byte rex) := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + movsLength byte ≤ 2^32 := hpre.rip ▸ (by simpa only [movsCode_length] using hcode.low (by cases byte <;> simp [movsCode]) (by cases byte <;> simp [movsCode]))
  rcases hn : (rcx.read s).toNat with _ | k
  · have hz : rcx.read s = 0 := BitVec.eq_of_toNat_eq hn
    have hs := rep_movs_step_zero byte s h.midRep rex hrex hcodeS hlow hz
    simp only [Nat.max_eq_right (show 0 ≤ 1 by omega), nextStates_one, nextState_of_step hs]
    exact Advances.of_step hs (.inr hsp)
  · have hc : rcx.read s = BitVec.ofNat 64 (k + 1) := by
      rw [← hn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have hr : ReadyMovsLoop byte rex s (k + 1) :=
      ⟨h.midRep, hpre.df, hcodeS, hlow, hc, hn ▸ hpre.srcLow, hn ▸ hpre.dstLow,
        hpre.dstAlign, hn ▸ hpre.srcMem, hn ▸ hpre.dstMem, hn ▸ hpre.disjoint,
        hn ▸ hpre.dstTables, hpre.rip ▸ hn ▸ hpre.dstCode⟩
    rw [Nat.max_eq_left (by omega)]
    exact hr.advances hstride hrex boundary k s hsp

theorem rep_movs_copy {byte : Bool} [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (rex : UInt8) (hrex : byte = false → RexWPrefix rex.toBitVec)
    (s : RamState) (h : ReadyToStep s) (hcode : CodeIn (codeRange p (movsCode byte rex)) s)
    (hpre : RepMovsPre byte p s) :
    ∀ i < movsBytes byte * (rcx.read s).toNat,
      (nextStates (max (rcx.read s).toNat 1) s).external[rdi.read s + BitVec.ofNat 64 i]? =
        s.external[rsi.read s + BitVec.ofNat 64 i]? := by
  rcases hn : (rcx.read s).toNat with _ | k
  · intro i hi; simp only [Nat.mul_zero] at hi; omega
  · have hc : rcx.read s = BitVec.ofNat 64 (k + 1) := by
      rw [← hn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have hr : ReadyMovsLoop byte rex s (k + 1) :=
      ⟨h.midRep, hpre.df, hpre.rip ▸ hcode.bytesAt,
        hpre.rip ▸ (by simpa only [movsCode_length] using hcode.low (by cases byte <;> simp [movsCode]) (by cases byte <;> simp [movsCode])), hc, hn ▸ hpre.srcLow, hn ▸ hpre.dstLow,
        hpre.dstAlign, hn ▸ hpre.srcMem, hn ▸ hpre.dstMem, hn ▸ hpre.disjoint,
        hn ▸ hpre.dstTables, hpre.rip ▸ hn ▸ hpre.dstCode⟩
    rw [Nat.max_eq_left (by omega)]
    exact (rep_movs_loop hstride hrex k s hr).copy


theorem rep_movsb_advances [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (boundary : ReturnBoundary) (p : BitVec 64)
    (s : RamState) (h : ReadyToStep s) (hcode : CodeIn (codeRange p [0xf3,0xa4]) s)
    (hpre : RepMovsbPre p s) (hsp : s.GPR[4] ≠ boundary.rsp) :
    Advances boundary (max (rcx.read s).toNat 1) s (nextStates (max (rcx.read s).toNat 1) s) := by
  simpa only [movsBytes, ite_true, Nat.one_mul] using rep_movs_advances (byte := true) hstride boundary p 0 (by simp) s h hcode hpre hsp

theorem rep_movsb_copy [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64)
    (s : RamState) (h : ReadyToStep s) (hcode : CodeIn (codeRange p [0xf3,0xa4]) s)
    (hpre : RepMovsbPre p s) :
    ∀ i < (rcx.read s).toNat,
      (nextStates (max (rcx.read s).toNat 1) s).external[rdi.read s + BitVec.ofNat 64 i]? =
        s.external[rsi.read s + BitVec.ofNat 64 i]? := by
  simpa only [movsBytes, ite_true, Nat.one_mul] using rep_movs_copy (byte := true) hstride p 0 (by simp) s h hcode hpre

end X86Proofs
