import X86Proofs.Step.Prefix
import X86Proofs.Step.Decode
import X86Proofs.Core.Gpr

set_option autoImplicit false

open X86Proofs

namespace Hkdf.Proofs.Common.Instructions

def encodeImulR64R64 (dst src : BitVec 4) : List UInt8 :=
  [UInt8.ofNat (0x48 + 4 * (dst.toNat / 8) + src.toNat / 8), 0x0F, 0xAF,
    UInt8.ofNat (0xC0 + 8 * (dst.toNat % 8) + src.toNat % 8)]

theorem encodeImulR64R64_spec : ∀ dst src : BitVec 4, ∃ rex modrm,
    encodeImulR64R64 dst src = [rex, 0x0F, 0xAF, modrm] ∧
    RexWPrefix rex.toBitVec ∧ modrmMod modrm = 3 ∧
    gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm) = dst.setWidth 5 ∧
    gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = src.setWidth 5 := by
  intro dst src
  refine ⟨_, _, rfl, ?_⟩
  unfold RexWPrefix
  revert dst src
  decide +kernel

end Hkdf.Proofs.Common.Instructions
