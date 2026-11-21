import X86Proofs.Step.Prefix
import X86Proofs.Step.Decode
import X86Proofs.Core.Gpr

namespace X86Proofs

def encodeNotR64 (dst : BitVec 4) : List UInt8 :=
  [UInt8.ofNat (0x48 + dst.toNat / 8), 0xF7, UInt8.ofNat (0xD0 + dst.toNat % 8)]

theorem encodeNotR64_spec : ∀ dst : BitVec 4, ∃ rex modrm,
    encodeNotR64 dst = [rex, 0xF7, modrm] ∧ RexWPrefix rex.toBitVec ∧ modrmMod modrm = 3 ∧
    modrmReg modrm = 2 ∧ gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = dst.setWidth 5 := by
  intro dst
  refine ⟨_, _, rfl, ?_⟩
  unfold RexWPrefix
  revert dst
  decide

def encodeNotR32 (dst : BitVec 4) : List UInt8 :=
  let modrm := UInt8.ofNat (0xD0 + dst.toNat % 8)
  if dst.toNat < 8 then [0xF7, modrm] else [0x41, 0xF7, modrm]

theorem encodeNotR32_spec : ∀ dst : BitVec 4,
    (∃ modrm, encodeNotR32 dst = [0xF7, modrm] ∧ modrmMod modrm = 3 ∧ modrmReg modrm = 2 ∧
      gprNumber 0 0 (modrmRm modrm) = dst.setWidth 5) ∨
    (∃ rex modrm, encodeNotR32 dst = [rex, 0xF7, modrm] ∧ RexNoWPrefix rex.toBitVec ∧
      modrmMod modrm = 3 ∧ modrmReg modrm = 2 ∧
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
