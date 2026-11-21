import Md5.Proofs.Buffered.Stores.Step
import X86Proofs.Instructions.MovStore.Triple

namespace Md5.Proofs.Buffered.Stores

open X86 X86.Machine X86.UserProcess X86Proofs X86.Helpers

theorem mov_m64_r64_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (Md5.Proofs.Memory.StorePre p (3 + am.tail.length) (storeAddrAt p am (3 + am.tail.length)) 8)
      (codeRange p (rex :: 0x89 :: am.modrm reg :: am.tail))
      (movM64R64Effect p (gprNumber 0 (rexR rex.toBitVec) reg) am) :=
  Md5.Proofs.Memory.stepEffect_of_store (n := 64) (by decide) (by decide) _ _
    fun s h hcode hpre => by
      obtain ⟨hp, hw, _⟩ := hpre
      subst hp
      have := am.tail_length_le
      exact mov_m64_r64_step s h rex hrex reg am hv hx hb hcode.bytesAt
        (hcode.low_len (by simp; omega) (by omega) (by omega)) hw

theorem mov_m32_r32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (Md5.Proofs.Memory.StorePre p (3 + am.tail.length) (storeAddrAt p am (3 + am.tail.length)) 4)
      (codeRange p (rex :: 0x89 :: am.modrm reg :: am.tail))
      (movM32R32Effect p (gprNumber 0 (rexR rex.toBitVec) reg) am) :=
  Md5.Proofs.Memory.stepEffect_of_store (n := 32) (by decide) (by decide) _ _
    fun s h hcode hpre => by
      obtain ⟨hp, hw, _⟩ := hpre
      subst hp
      have := am.tail_length_le
      exact mov_m32_r32_step s h rex hrex reg am hv hx hb hcode.bytesAt
        (hcode.low_len (by simp; omega) (by omega) (by omega)) hw

theorem mov_m64_imm32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 32) :
    StepEffect (Md5.Proofs.Memory.StorePre p (7 + am.tail.length) (storeAddrAt p am (7 + am.tail.length)) 8)
      (codeRange p (rex :: 0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 32 imm)))
      (movM64Imm32Effect p am imm) :=
  Md5.Proofs.Memory.stepEffect_of_store (n := 64) (by decide) (by decide) _ _
    fun s h hcode hpre => by
      obtain ⟨hp, hw, _⟩ := hpre
      subst hp
      have := am.tail_length_le
      exact mov_m64_imm32_step s h rex hrex am hv hx hb imm hcode.bytesAt
        (hcode.low_len (by simp; omega) (by omega) (by omega)) hw

theorem mov_m8_imm8_effect_step [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 8) :
    StepEffect (Md5.Proofs.Memory.StorePre p (3 + am.tail.length) (storeAddrAt p am (3 + am.tail.length)) 1)
      (codeRange p (0xC6 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)))
      (movM8Imm8Effect p am imm) := by
  have hse : imm.signExtend 8 = imm := BitVec.signExtend_eq imm
  refine Md5.Proofs.Memory.stepEffect_of_store (n := 8) (by decide) (by decide) _ _
    fun s h hcode hpre => ?_
  obtain ⟨hp, hw, _⟩ := hpre
  subst hp
  have := am.tail_length_le
  have := mov_m8_imm8_step s h am hv hx hb imm hcode.bytesAt
    (hcode.low_len (by simp; omega) (by omega) (by omega)) hw
  rwa [movSpec, hse] at this

end Md5.Proofs.Buffered.Stores
