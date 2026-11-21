import Sha2.Proofs.Common.SHA256.Blocks.Absorb.Instruction

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Absorb.Blocks

open Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions

private theorem low_number (r : BitVec 4) (low : r.toNat < 8) :
    gprNumber 0 0 (regLow r) = r.setWidth 5 := by
  have : ∀ r : BitVec 4, r.toNat < 8 → gprNumber 0 0 (regLow r) = r.setWidth 5 := by
    decide +kernel
  exact this r low

theorem loadTail_step [Bindings] (p : BitVec 64) (r : BitVec 4) (am : AddrMode)
    (valid : am.Valid) :
    StepEffect (LoadPre p (fun s => am.addr s
      (p + BitVec.ofNat 64 (bytes (.loadTail r am)).length)) 1)
      (codeRange p (bytes (.loadTail r am)))
      (movzxR32M8Effect p (bytes (.loadTail r am)).length (r.setWidth 5) am) := by
  by_cases low : r.toNat < 8 ∧ am.rexX = 0 ∧ am.rexB = 0
  · have len : (bytes (.loadTail r am)).length = 3 + am.tail.length := by
      rw [bytes, loadBytePrefix, ite_eq_left low]
      simp only [List.nil_append, List.length_append, List.length_cons, List.length_nil]
    rw [len]
    have step := movzx_r32_m8_effect_step p (regLow r) am valid low.2.1 low.2.2
    rw [low_number r low.1] at step
    simpa only [bytes, loadBytePrefix, low, ↓reduceIte, List.nil_append, List.cons_append,
      List.nil_append, and_true, true_and] using step
  · have len : (bytes (.loadTail r am)).length = 4 + am.tail.length := by
      rw [bytes, loadBytePrefix, ite_eq_right low]
      simp only [List.length_append, List.length_cons, List.length_nil]
    rw [len]
    obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec r
    have step := movzx_r32_m8_rex_effect_step p _ hrex (regLow r) am valid hx hb
    rw [hr, gprNumber_reg] at step
    simpa only [bytes, loadBytePrefix, low, ↓reduceIte, List.cons_append,
      List.nil_append, and_true, true_and] using step

theorem storeTail_step [Bindings] (p : BitVec 64) (r : BitVec 4) (am : AddrMode)
    (valid : am.Valid) :
    StepEffect (X86Proofs.StorePre p (bytes (.storeTail r am)).length
      (fun s => am.addr s (p + BitVec.ofNat 64 (bytes (.storeTail r am)).length)) 1)
      (codeRange p (bytes (.storeTail r am)))
      (fun s => storeEffect p (bytes (.storeTail r am)).length
        (fun u => am.addr u (p + BitVec.ofNat 64 (bytes (.storeTail r am)).length))
        (fun u => (.reg (r.setWidth 5) : Operand 8).read u) s) := by
  by_cases low : r.toNat < 4 ∧ am.rexX = 0 ∧ am.rexB = 0
  · have num := low_number r (by omega)
    have regBound : (gprNumber 0 0 (regLow r)).toNat < 4 := by
      rw [num, BitVec.toNat_setWidth]
      have := r.isLt
      omega
    have len : (bytes (.storeTail r am)).length = 2 + am.tail.length := by
      rw [bytes, bytePrefix, ite_eq_left low]
      simp only [List.nil_append, List.length_append, List.length_cons, List.length_nil]
    rw [len]
    have step := mov_m8_r8_legacy_effect_step p (regLow r) regBound am valid low.2.1 low.2.2
    rw [num] at step
    simpa only [bytes, bytePrefix, low, ↓reduceIte, List.nil_append, List.cons_append,
      storeAddrAt, and_true, true_and] using step
  · have len : (bytes (.storeTail r am)).length = 3 + am.tail.length := by
      rw [bytes, bytePrefix, ite_eq_right low]
      simp only [List.length_append, List.length_cons, List.length_nil]
    rw [len]
    obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec r
    have step := Common.Instructions.mov_m8_r8_effect_step p _ hrex.rexPrefix
      (regLow r) am valid hx hb
    rw [hr, gprNumber_reg] at step
    simpa only [bytes, bytePrefix, low, ↓reduceIte, List.nil_append, List.cons_append,
      storeAddrAt, and_true, true_and] using step

theorem addTail_step [Bindings] (p : BitVec 64) (dst src : BitVec 4) :
    StepEffect (fun s => s.RIP = p) (codeRange p (bytes (.addTail dst src)))
      (AddByte.addR8R8Effect p (dst.setWidth 5) (src.setWidth 5)) := by
  have fields : ∀ dst src : BitVec 4,
      let rex := UInt8.ofNat (0x40 + 4 * (src.toNat / 8) + dst.toNat / 8)
      let modrm := UInt8.ofNat (0xc0 + 8 * (src.toNat % 8) + dst.toNat % 8)
      RexPrefix rex.toBitVec ∧ modrmMod modrm = 3 ∧
        gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = dst.setWidth 5 ∧
        gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm) = src.setWidth 5 := by
    unfold RexPrefix
    decide +kernel
  obtain ⟨hrex, hmod, hdst, hsrc⟩ := fields dst src
  have step := AddByte.add_r8_r8_effect_step p _ _ hrex hmod
  rw [hdst, hsrc] at step
  exact step

end Sha2.Proofs.Common.SHA256.Absorb.Blocks
