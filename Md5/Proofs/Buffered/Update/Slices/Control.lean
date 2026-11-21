import Md5.Proofs.Buffered.Update.Slices.Entry

namespace Md5.Proofs.Buffered.Update.Slices

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Block

theorem position_eq {variant : Bool} [Bindings] {boundary : ReturnBoundary} {message input : ByteArray}
    {s : RamState} (h : UpdatePre (kind variant) boundary message input s) :
    position s = BitVec.ofNat 64 (message.size % 64) := by
  have hp := h.absorbed.position
  rw [kind_context] at hp
  change (Operand.mem ((stackPtr s + 192) + 63) : Operand 8).read s = _ at hp
  rw [BitVec.add_assoc] at hp
  change (Operand.mem (stackPtr s + 255) : Operand 8).read s = _ at hp
  unfold position
  rw [hp]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem inputSize_lt {variant : Bool} [Bindings] {boundary : ReturnBoundary} {message input : ByteArray}
    {s : RamState} (h : UpdatePre (kind variant) boundary message input s) : input.size < 2^32 := by
  have hi := h.inputBounded
  change ((Operand.reg (kind variant).inputRegister : Operand 64).read s).toNat +
    input.size < 2^32 at hi
  rw [kind_inputRegister] at hi
  omega

theorem prepared_carry {variant : Bool} [Bindings] {boundary : ReturnBoundary} {message input : ByteArray}
    {s u : RamState} (h : UpdatePre (kind variant) boundary message input s)
    (hp : Prepared variant boundary s u) :
    (StatusFlags.ofRFLAGS u.RFLAGS).CF = decide (input.size < 64 - message.size % 64) := by
  have hcf := hp.effect.flags.1
  change (StatusFlags.ofRFLAGS u.RFLAGS).CF =
    (subSpec ((Operand.reg 3 : Operand 64).read s) (64 - position s)).2.CF at hcf
  have hs : (Operand.reg 3 : Operand 64).read s = BitVec.ofNat 64 input.size := by
    simpa only [kind_sizeRegister] using h.inputSize
  rw [hcf, position_eq h, hs]
  simp only [subSpec, BitVec.toNat_ofNat, BitVec.toNat_sub]
  have hi := inputSize_lt h
  congr 1
  change (input.size % 2^64 < (2^64 - message.size % 64 % 2^64 + 64) % 2^64) = _
  apply propext
  omega

theorem branch {variant : Bool} [Bindings] {boundary : ReturnBoundary} {message input : ByteArray}
    {s u : RamState} (h : UpdatePre (kind variant) boundary message input s)
    (hp : Prepared variant boundary s u) :
    ∃ v, Advances boundary 1 u v ∧ ReadyToStep v ∧ CodeIn Extracted.programImage v ∧
      v.RIP = (if input.size < 64 - message.size % 64 then (pc variant 0x100310) else (pc variant 0x10036e)) ∧
      AgreesExcept [.rip] u v := by
  cases variant with
  | false =>
    have hc : CodeIn (codeRange 0x10036c [0x72, 0xa2]) u :=
      program_text_slice hp.code 0x36c 2 (by decide +kernel)
    have he : (jccEffect 0x10036c 2 2 ((0xa2#8).signExtend 64) u).rip =
        (if input.size < 64 - message.size % 64 then 0x100310 else 0x10036e) := by
      change (if (StatusFlags.ofRFLAGS u.RFLAGS).CF = true then 0x100310 else 0x10036e) = _
      rw [prepared_carry h hp]
      simp only [decide_eq_true_eq]
    have hn : (jccEffect 0x10036c 2 2 ((0xa2#8).signExtend 64) u).rip ≠ boundary.rip := by
      rw [he]
      split
      · exact text_address_ne_return h.boundaryOutside 0x310 (by decide +kernel)
      · exact text_address_ne_return h.boundaryOutside 0x36e (by decide +kernel)
    obtain ⟨v, hav, hr, heffect⟩ := (jcc_rel8_effect_step 0x10036c 2 0xa2).advances
      hp.ready hc ⟨hp.effect.rip, fun _ ↦ by decide +kernel⟩ hn
    refine ⟨v, hav, hr, heffect.codeIn ?_ hp.code, heffect.rip.trans he, ?_⟩
    · exact branchEffect_avoids _ _ _ _
    · exact heffect.agrees
  | true =>
    have hc : CodeIn (codeRange 0x10191c [0x72, 0xa2]) u :=
      program_text_slice hp.code 0x191c 2 (by decide +kernel)
    have he : (jccEffect 0x10191c 2 2 ((0xa2#8).signExtend 64) u).rip =
        (if input.size < 64 - message.size % 64 then 0x1018c0 else 0x10191e) := by
      change (if (StatusFlags.ofRFLAGS u.RFLAGS).CF = true then 0x1018c0 else 0x10191e) = _
      rw [prepared_carry h hp]
      simp only [decide_eq_true_eq]
    have hn : (jccEffect 0x10191c 2 2 ((0xa2#8).signExtend 64) u).rip ≠ boundary.rip := by
      rw [he]
      split
      · exact text_address_ne_return h.boundaryOutside 0x18c0 (by decide +kernel)
      · exact text_address_ne_return h.boundaryOutside 0x191e (by decide +kernel)
    obtain ⟨v, hav, hr, heffect⟩ := (jcc_rel8_effect_step 0x10191c 2 0xa2).advances
      hp.ready hc ⟨hp.effect.rip, fun _ ↦ by decide +kernel⟩ hn
    refine ⟨v, hav, hr, heffect.codeIn ?_ hp.code, heffect.rip.trans he, ?_⟩
    · exact branchEffect_avoids _ _ _ _
    · exact heffect.agrees

end Md5.Proofs.Buffered.Update.Slices
