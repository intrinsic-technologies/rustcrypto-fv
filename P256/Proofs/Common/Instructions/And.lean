import X86Proofs.Instructions.And.Generated.Imm8.Triple
import P256.Proofs.Common.EffectCompose
set_option autoImplicit false
namespace P256.Proofs.Common.Instructions
open X86 X86.Machine X86.UserProcess X86Proofs
@[x86_local] theorem andR32Imm8Effect_local (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) :
    Effect.Local (andR32Imm8Effect p len dst imm) := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [andR32Imm8Effect, h.read_reg]
  · intro s
    simp [andR32Imm8Effect, Write.Full, Operand.Full]
attribute [x86_compose] andR32Imm8Effect
end P256.Proofs.Common.Instructions
