import X86Proofs.Step.Prefix
import X86Proofs.Step.Decode
import X86Proofs.Step.FetchImm
import X86Proofs.Core.Gpr

namespace X86Proofs

def encodeShrR64Imm8 (dst : BitVec 4) (imm : BitVec 8) : List UInt8 :=
  [UInt8.ofNat (0x48 + dst.toNat / 8), 0xC1, UInt8.ofNat (0xE8 + dst.toNat % 8)] ++ immBytes 8 imm

theorem encodeShrR64Imm8_spec (imm : BitVec 8) : ∀ dst : BitVec 4, ∃ rex modrm,
    encodeShrR64Imm8 dst imm = [rex, 0xC1, modrm] ++ immBytes 8 imm ∧ RexWPrefix rex.toBitVec ∧
    modrmMod modrm = 3 ∧ modrmReg modrm = 5 ∧
    gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = dst.setWidth 5 := by
  intro dst
  refine ⟨_, _, rfl, ?_⟩
  unfold RexWPrefix
  revert dst
  decide

def encodeShrR32Imm8 (dst : BitVec 4) (imm : BitVec 8) : List UInt8 :=
  let modrm := UInt8.ofNat (0xE8 + dst.toNat % 8)
  if dst.toNat < 8 then [0xC1, modrm] ++ immBytes 8 imm
  else [UInt8.ofNat (0x40 + dst.toNat / 8), 0xC1, modrm] ++ immBytes 8 imm

theorem encodeShrR32Imm8_spec (imm : BitVec 8) : ∀ dst : BitVec 4,
    (∃ modrm, encodeShrR32Imm8 dst imm = [0xC1, modrm] ++ immBytes 8 imm ∧ modrmMod modrm = 3 ∧
      modrmReg modrm = 5 ∧ gprNumber 0 0 (modrmRm modrm) = dst.setWidth 5) ∨
    (∃ rex modrm, encodeShrR32Imm8 dst imm = [rex, 0xC1, modrm] ++ immBytes 8 imm ∧ RexNoWPrefix rex.toBitVec ∧
      modrmMod modrm = 3 ∧ modrmReg modrm = 5 ∧
      gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = dst.setWidth 5) := by
  intro dst
  by_cases hlow : dst.toNat < 8
  · refine .inl ⟨_, ite_eq_left hlow, ?_⟩
    revert dst
    decide
  · refine .inr ⟨_, _, ite_eq_right hlow, ?_⟩
    unfold RexNoWPrefix
    revert dst
    decide

def encodeShrR64One (dst : BitVec 4) : List UInt8 :=
  [UInt8.ofNat (0x48 + dst.toNat / 8), 0xD1, UInt8.ofNat (0xE8 + dst.toNat % 8)]

theorem encodeShrR64One_spec : ∀ dst : BitVec 4, ∃ rex modrm,
    encodeShrR64One dst = [rex, 0xD1, modrm] ∧ RexWPrefix rex.toBitVec ∧
    modrmMod modrm = 3 ∧ modrmReg modrm = 5 ∧
    gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = dst.setWidth 5 := by
  intro dst
  refine ⟨_, _, rfl, ?_⟩
  unfold RexWPrefix
  revert dst
  decide

def encodeShrR32One (dst : BitVec 4) : List UInt8 :=
  let modrm := UInt8.ofNat (0xE8 + dst.toNat % 8)
  if dst.toNat < 8 then [0xD1, modrm]
  else [UInt8.ofNat (0x40 + dst.toNat / 8), 0xD1, modrm]

theorem encodeShrR32One_spec : ∀ dst : BitVec 4,
    (∃ modrm, encodeShrR32One dst = [0xD1, modrm] ∧ modrmMod modrm = 3 ∧
      modrmReg modrm = 5 ∧ gprNumber 0 0 (modrmRm modrm) = dst.setWidth 5) ∨
    (∃ rex modrm, encodeShrR32One dst = [rex, 0xD1, modrm] ∧ RexNoWPrefix rex.toBitVec ∧
      modrmMod modrm = 3 ∧ modrmReg modrm = 5 ∧
      gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = dst.setWidth 5) := by
  intro dst
  by_cases hlow : dst.toNat < 8
  · refine .inl ⟨_, ite_eq_left hlow, ?_⟩
    revert dst
    decide
  · refine .inr ⟨_, _, ite_eq_right hlow, ?_⟩
    unfold RexNoWPrefix
    revert dst
    decide

end X86Proofs
