import Sha2.Proofs.Common.SHA256.Absorb.Blocks

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Absorb.Blocks

open Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions

theorem move_step [Bindings] (p : BitVec 64) (dst src : BitVec 4) :
    StepEffect (fun s => s.RIP = p) (codeRange p (encodeMovR64R64 dst src))
      (movR64R64Effect p (dst.setWidth 5) (src.setWidth 5)) := by
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩ := encodeMovR64R64_spec dst src
  rw [hbytes, ← hdst, ← hsrc]
  exact mov_r64_r64_effect_step p rex modrm hrex hmod

theorem subtract_step [Bindings] (p : BitVec 64) (dst src : BitVec 4) :
    StepEffect (fun s => s.RIP = p) (codeRange p (encodeSubR64R64 dst src))
      (subR64R64Effect p (dst.setWidth 5) (src.setWidth 5)) := by
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩ := encodeSubR64R64_spec dst src
  rw [hbytes, ← hdst, ← hsrc]
  exact sub_r64_r64_effect_step p rex modrm hrex hmod

theorem and_step [Bindings] (p : BitVec 64) (dst src : BitVec 4) :
    StepEffect (fun s => s.RIP = p) (codeRange p (encodeAndR64R64 dst src))
      (andR64R64Effect p (dst.setWidth 5) (src.setWidth 5)) := by
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩ := encodeAndR64R64_spec dst src
  rw [hbytes, ← hdst, ← hsrc]
  exact and_r64_r64_effect_step p rex modrm hrex hmod

theorem add_step [Bindings] (p : BitVec 64) (dst src : BitVec 4) :
    StepEffect (fun s => s.RIP = p) (codeRange p (encodeAddR64R64 dst src))
      (addR64R64Effect p (dst.setWidth 5) (src.setWidth 5)) := by
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩ := encodeAddR64R64_spec dst src
  rw [hbytes, ← hdst, ← hsrc]
  exact add_r64_r64_effect_step p rex modrm hrex hmod

theorem test_step [Bindings] (p : BitVec 64) (dst src : BitVec 4) :
    StepEffect (fun s => s.RIP = p) (codeRange p (encodeTestR64R64 dst src))
      (testR64R64Effect p (dst.setWidth 5) (src.setWidth 5)) := by
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩ := encodeTestR64R64_spec dst src
  rw [hbytes, ← hdst, ← hsrc]
  exact test_r64_r64_effect_step p rex modrm hrex hmod

theorem compare_step [Bindings] (p : BitVec 64) (dst src : BitVec 4) :
    StepEffect (fun s => s.RIP = p) (codeRange p (encodeCmpR64R64 dst src))
      (cmpR64R64Effect p (dst.setWidth 5) (src.setWidth 5)) := by
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩ := encodeCmpR64R64_spec dst src
  rw [hbytes, ← hdst, ← hsrc]
  exact cmp_r64_r64_effect_step p rex modrm hrex hmod

theorem constant_step [Bindings] (p : BitVec 64) (dst : BitVec 4) (value : BitVec 32) :
    StepEffect (fun s => s.RIP = p) (codeRange p (encodeMovR32Imm32 dst value))
      (movR32Imm32Effect p (encodeMovR32Imm32 dst value).length (dst.setWidth 5) value) := by
  rcases encodeMovR32Imm32_spec dst value with ⟨op, hbytes, hop, hdst⟩ |
    ⟨rex, op, hbytes, hrex, hop, hdst⟩
  · rw [hbytes, ← hdst]
    simpa only [List.length_cons, immBytes_length] using mov_r32_imm32_effect_step p op hop value
  · rw [hbytes, ← hdst]
    simpa only [List.length_cons, immBytes_length] using
      mov_r32_imm32_rex_effect_step p rex op hrex hop value

theorem constant64_step [Bindings] (p : BitVec 64) (dst : BitVec 4) (value : BitVec 64) :
    StepEffect (fun s => s.RIP = p) (codeRange p (encodeMovR64Imm64 dst value))
      (movR64Imm64Effect p (dst.setWidth 5) value) := by
  obtain ⟨rex, op, hbytes, hrex, hop, hdst⟩ := encodeMovR64Imm64_spec dst value
  rw [hbytes, ← hdst]
  exact mov_r64_imm64_effect_step p rex op hrex hop value

theorem address_step [Bindings] (p : BitVec 64) (dst : BitVec 4) (am : AddrMode)
    (valid : am.Valid) :
    StepEffect (fun s => s.RIP = p) (codeRange p (encodeLeaR64M dst am))
      (leaR64Effect p (dst.setWidth 5) am) := by
  obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_true_spec dst
  have step := lea_r64_effect_step p _ hrex (regLow dst) am valid hx hb
  rwa [hr, gprNumber_reg] at step

theorem load64_step [Bindings] (p : BitVec 64) (dst : BitVec 4) (am : AddrMode)
    (valid : am.Valid) :
    StepEffect (LoadPre p (fun s => am.addr s
      (p + BitVec.ofNat 64 (encodeMovR64M64 dst am).length)) 8)
      (codeRange p (encodeMovR64M64 dst am)) (movR64M64Effect p (dst.setWidth 5) am) := by
  obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_true_spec dst
  have step := mov_r64_m64_effect_step p _ hrex (regLow dst) am valid hx hb
  rw [hr, gprNumber_reg] at step
  have length : (encodeMovR64M64 dst am).length = 3 + am.tail.length := by
    simp only [encodeMovR64M64, List.length_cons]
    omega
  rw [length]
  exact step

theorem increment_step [Bindings] (p : BitVec 64) (dst : BitVec 4) :
    StepEffect (fun s => s.RIP = p) (codeRange p (encodeIncR64 dst))
      (incR64Effect p (dst.setWidth 5)) := by
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩ := encodeIncR64_spec dst
  rw [hbytes, ← hdst]
  exact inc_r64_effect_step p rex modrm hrex hmod hreg

theorem shift_right_step [Bindings] (p : BitVec 64) (dst : BitVec 4) :
    StepEffect (fun s => s.RIP = p) (codeRange p (encodeShrR64Imm8 dst 6))
      (shrR64Effect p 4 (dst.setWidth 5) 6) := by
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩ := encodeShrR64Imm8_spec 6 dst
  rw [hbytes, ← hdst]
  exact shr_r64_imm8_effect_step p rex modrm 6 hrex hmod hreg

theorem and32_step [Bindings] (p : BitVec 64) (dst : BitVec 4) :
    StepEffect (fun s => s.RIP = p) (codeRange p (encodeAndR32Imm8 dst 63))
      (andR32Imm8Effect p (encodeAndR32Imm8 dst 63).length (dst.setWidth 5) 63) := by
  rcases encodeAndR32Imm8_spec dst 63 with ⟨modrm, hbytes, hmod, hreg, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    simpa only [List.length_cons, immBytes_length] using
      and_r32_imm8_effect_step p modrm 63 hmod hreg
  · rw [hbytes, ← hdst]
    simpa only [List.length_cons, immBytes_length] using
      and_r32_imm8_rex_effect_step p rex modrm 63 hrex hmod hreg

theorem widened_eq (a b : BitVec 4) : a.setWidth 5 = b.setWidth 5 ↔ a = b := by
  revert a b
  decide +kernel

end Sha2.Proofs.Common.SHA256.Absorb.Blocks
