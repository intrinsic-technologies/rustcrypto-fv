import P256.Proofs.Nonce.Initialize.Conversions.ShiftZero.Frame

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Conversions.ShiftZero

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Field
open P256.Proofs.SecretKeyFromBytes.Scalar

variable [Bindings] {s t u : RamState} {boundary : ReturnBoundary}

theorem Stage.scratch_address (stage : Stage s t boundary) {offset : Nat} (ho : offset ≤ 72) :
    rspOf t + BitVec.ofNat 64 offset = stackPtr s - BitVec.ofNat 64 (72-offset) := by
  change stackPtr t + BitVec.ofNat 64 offset = _
  rw [stage.rsp, ← BitVec.ofNat_sub_ofNat_of_le 72 offset (by omega) ho]
  simp only [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.neg_neg]
  exact BitVec.add_assoc _ _ _

theorem Stage.scratch_readable (pre : CalleePre s boundary 0x109530 32 32 128)
    (stage : Stage s t boundary) {offset len : Nat} (bound : offset + len ≤ 24) :
    MemReadable t (rspOf t + BitVec.ofNat 64 offset) len := by
  rw [stage.scratch_address (by omega)]
  exact readable_of_grow
    (stack_sub_readable pre.stack (by omega) (by omega))
    stage.agrees.grow

theorem Stage.scratch_word_writable (pre : CalleePre s boundary 0x109530 32 32 128)
    (stage : Stage s t boundary) {offset : Nat} (bound : offset + 8 ≤ 24)
    (aligned : offset % 8 = 0) : MemWritable t (rspOf t + BitVec.ofNat 64 offset) 8 := by
  rw [stage.scratch_address (by omega)]
  exact writable_of_grow
    (stack_sub_writable8 pre.stack
      (fun a ha h => pre.avoids _ (by simp) a ha (.inr h)) (by omega) (by omega))
    stage.agrees.grow

theorem Stage.scratch_byte_writable (pre : CalleePre s boundary 0x109530 32 32 128)
    (stage : Stage s t boundary) {offset : Nat} (bound : offset < 24) :
    MemWritable t (rspOf t + BitVec.ofNat 64 offset) 1 := by
  rw [stage.scratch_address (by omega)]
  apply writable_of_grow _ stage.agrees.grow
  exact stack_sub_writable pre.stack
    (fun a ha h => pre.avoids _ (by simp) a ha (.inr h))
    (by omega) (by omega) (by decide) (by omega)

theorem Stage.scratch_code_apart (pre : CalleePre s boundary 0x109530 32 32 128)
    (stage : Stage s t boundary) {offset len codeOffset codeLen : Nat}
    (ho : offset + len ≤ 24) (hc : codeOffset + codeLen ≤ 118431) :
    RangeApart (rspOf t + BitVec.ofNat 64 offset) len
      (Extracted.textAddress + BitVec.ofNat 64 codeOffset) codeLen := by
  rw [stage.scratch_address (by omega)]
  intro i hi j hj he
  apply pre.avoids (Stack.region s 128) (by simp) _
    (stack_contains pre (offset := 72-offset) (len := len) (by omega) (by omega) ⟨i, hi, rfl⟩)
  left
  change InProgram (stackPtr s - BitVec.ofNat 64 (72-offset) + BitVec.ofNat 64 i)
  rw [he, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact inProgram_of_textOffset (codeOffset+j) (by omega)

theorem body_input_read (pre : CalleePre s boundary 0x109530 32 32 128)
    (stage : Stage s t boundary) {cs : List Component}
    (h : AgreesExcept cs t u) (hcs : ∀ c ∈ cs, BodyComponent (rspOf t) c)
    {offset : Nat} (ho : offset+8 ≤ 32) :
    (Operand.mem (s.regValue .rsi + BitVec.ofNat 64 offset) : Operand 64).read u =
      (Operand.mem (s.regValue .rsi + BitVec.ofNat 64 offset) : Operand 64).read t := by
  apply P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees h
  intro i hi c hc ha
  have hs := body_covers (hcs c hc) ha
  change (Component.mem (stackPtr t) 24).Covers _ at hs
  rw [stage.rsp] at hs
  have contains := stack_contains pre (offset := 72) (len := 24) (by decide) (by decide) hs
  apply (pre.separation ⟨0, by decide⟩ ⟨2, by decide⟩ (by decide)) _ _ contains
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact memoryRegion_contains_add pre.inputBounded (Nat.le_refl _) (Nat.le_refl _)
    (show offset+i<32 by omega)

end P256.Proofs.Nonce.Initialize.Conversions.ShiftZero
