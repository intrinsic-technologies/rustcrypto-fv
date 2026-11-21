import X86Proofs.Step.Prefix
import X86Proofs.Step.Decode
import X86Proofs.Step.FetchImm
import X86Proofs.Core.Gpr

namespace X86Proofs

def encodeCmpR64Imm32 (dst : BitVec 4) (imm : BitVec 32) : List UInt8 :=
  UInt8.ofNat (0x48 + dst.toNat / 8) :: 0x81 :: UInt8.ofNat (0xF8 + dst.toNat % 8) ::
    immBytes 32 imm

theorem encodeCmpR64Imm32_spec (dst : BitVec 4) (imm : BitVec 32) : ∃ rex modrm,
    encodeCmpR64Imm32 dst imm = rex :: 0x81 :: modrm :: immBytes 32 imm ∧ RexWPrefix rex.toBitVec ∧
    modrmMod modrm = 3 ∧ modrmReg modrm = 7 ∧
    gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = dst.setWidth 5 := by
  refine ⟨_, _, rfl, ?_⟩
  unfold RexWPrefix
  revert dst
  decide

def encodeCmpR32Imm32 (dst : BitVec 4) (imm : BitVec 32) : List UInt8 :=
  let modrm := UInt8.ofNat (0xF8 + dst.toNat % 8)
  if dst.toNat < 8 then 0x81 :: modrm :: immBytes 32 imm
  else UInt8.ofNat (0x40 + dst.toNat / 8) :: 0x81 :: modrm :: immBytes 32 imm

theorem encodeCmpR32Imm32_spec (dst : BitVec 4) (imm : BitVec 32) :
    (∃ modrm, encodeCmpR32Imm32 dst imm = 0x81 :: modrm :: immBytes 32 imm ∧
      modrmMod modrm = 3 ∧ modrmReg modrm = 7 ∧ gprNumber 0 0 (modrmRm modrm) = dst.setWidth 5) ∨
    (∃ rex modrm, encodeCmpR32Imm32 dst imm = rex :: 0x81 :: modrm :: immBytes 32 imm ∧
      RexNoWPrefix rex.toBitVec ∧ modrmMod modrm = 3 ∧ modrmReg modrm = 7 ∧
      gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = dst.setWidth 5) := by
  by_cases hlow : dst.toNat < 8
  · refine .inl ⟨_, ite_eq_left hlow, ?_⟩
    revert dst
    decide
  · refine .inr ⟨_, _, ite_eq_right hlow, ?_⟩
    unfold RexNoWPrefix
    revert dst
    decide

end X86Proofs
