import P256.Proofs.Common.Memory.Fill.Stos.Loop

namespace P256.Proofs.Common.Memory.Fill.Stos

open X86Proofs X86 X86.Machine X86.UserProcess

theorem ReadyRepStosLoop.advances [Bindings] {bytes : Nat} {code : List UInt8}
    (hs : StosInstruction bytes code) (boundary : ReturnBoundary)
    (count : Nat) (s : RamState) (h : ReadyRepStosLoop bytes code s (count + 1))
    (hstart : s.RIP ≠ boundary.rip)
    (hend : BitVec.add s.RIP (BitVec.ofNat 64 code.length) ≠ boundary.rip) :
    Advances boundary (count + 1) s (nextStates (count + 1) s) := by
  induction count generalizing s with
  | zero =>
    have hstep := h.step hs (by omega)
    have hi : (repStosAfter bytes code.length s).RIP ≠ boundary.rip := by
      rw [repStosAfter_rip bytes code.length s h.ready.msr]
      split <;> assumption
    rw [nextStates_one, nextState_of_step hstep]
    exact Advances.of_step hstep (.inl hi)
  | succ k ih =>
    have hstep := h.step hs (by omega)
    have hrip := h.rip_after hs.positive
    have ha : Advances boundary 1 s (repStosAfter bytes code.length s) :=
      Advances.of_step hstep (.inl (by rw [hrip]; exact hstart))
    have hb := ih (repStosAfter bytes code.length s) (h.next hs.positive)
      (by rw [hrip]; exact hstart) (by rw [hrip]; exact hend)
    rw [nextStates_succ, nextState_of_step hstep]
    simpa only [Nat.add_comm 1 (k + 1)] using ha.trans hb

theorem rep_stos_zero_fill [Bindings] {bytes : Nat} {code : List UInt8}
    (hs : StosInstruction bytes code) (boundary : ReturnBoundary)
    (p : BitVec 64) (s : RamState) (count : Nat)
    (h : ReadyToStep s) (hcode : CodeIn (codeRange p code) s)
    (hrip : s.RIP = p) (hc : rcx.read s = BitVec.ofNat 64 count)
    (hdf : DirectionFlagClear s.RFLAGS)
    (hz : (Operand.reg 0 : Operand (8 * bytes)).read s = 0)
    (hdst : (rdi.read s).toNat + bytes * count ≤ 2^32)
    (hmem : ∀ i < bytes * count, (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome)
    (htables : 0 < count →
      (rdi.read s).toNat + bytes * count ≤ 0x1000 ∨ 0x3000 ≤ (rdi.read s).toNat)
    (hapart : RangeApart (rdi.read s) (bytes * count) p code.length)
    (halign : 0 < count → (rdi.read s).toNat % bytes = 0)
    (hstart : p ≠ boundary.rip)
    (hend : p + BitVec.ofNat 64 code.length ≠ boundary.rip) :
    ∃ t, Advances boundary (max count 1) s t ∧ ReadyToStep t ∧
      t.RIP = p + BitVec.ofNat 64 code.length ∧
      rdi.read t = rdi.read s + BitVec.ofNat 64 (bytes * count) ∧ rcx.read t = 0 ∧
      (∀ i < bytes * count, t.external[rdi.read s + BitVec.ofNat 64 i]? = some 0) ∧
      AgreesExcept [.reg 1, .reg 7, .mem (rdi.read s) (bytes * count), .rip] s t := by
  have hcodeS : BytesAt s s.RIP code := hrip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + code.length ≤ 2^32 :=
    hrip ▸ hcode.low (List.length_pos_iff.mpr hs.codeNonempty) (by have := hs.codeSmall; omega)
  cases count with
  | zero =>
    have hstep := hs.zero s h.midRep hcodeS hlow hc
    have hag : AgreesExcept [.rip] s (repStosZeroAfter code.length s) :=
      (repStosZeroAfter_agrees code.length s).of_clearRep h.ready.repeatClear
        (repStosZeroAfter_repeat code.length s)
    have hi : (repStosZeroAfter code.length s).RIP = p + BitVec.ofNat 64 code.length := by
      rw [repStosZeroAfter_rip code.length s h.ready.msr, hrip]
      rfl
    refine ⟨repStosZeroAfter code.length s, ?_,
      ReadyToStep.of_agreesExcept h hag h.memory.tables, hi, ?_, ?_, ?_, ?_⟩
    · exact Advances.of_step hstep (.inl (hi ▸ hend))
    · rw [hag.read (by simp), Nat.mul_zero]
      simp
    · exact (hag.read (by simp)).trans hc
    · intro i hi
      omega
    · exact hag.mono (by simp)
  | succ count =>
    have hr : ReadyRepStosLoop bytes code s (count + 1) :=
      ⟨h.midRep, hdf, hcodeS, hlow, hc, hz, hdst, halign (by omega), hmem,
        htables (by omega), hrip ▸ hapart⟩
    have hd := rep_stos_loop hs count s hr
    have ha := hr.advances hs boundary count s (hrip ▸ hstart) (hrip ▸ hend)
    refine ⟨nextStates (count + 1) s, ?_, hd.ready, ?_, hd.rdiAfter, hd.rcxZero,
      hd.fill, ?_⟩
    · simpa only [Nat.max_eq_left (show 1 ≤ count + 1 by omega)] using ha
    · rw [hd.rip, hrip]; rfl
    · simpa only [clearRep_eq h.ready.repeatClear] using hd.agrees

end P256.Proofs.Common.Memory.Fill.Stos
