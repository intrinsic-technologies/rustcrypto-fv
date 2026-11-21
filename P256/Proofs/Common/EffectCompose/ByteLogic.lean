import P256.Proofs.Common.EffectCompose
import P256.Proofs.Common.Instructions.ByteLogic.And
import P256.Proofs.Common.Instructions.ByteLogic.Unary
import P256.Proofs.Common.Instructions.ByteLogic.XorLoad

set_option autoImplicit false

open X86 X86.Machine X86.UserProcess X86Proofs

namespace P256.Proofs.Common.Instructions.ByteLogic

@[x86_local] theorem andR8Imm8Effect_local
    (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) :
    Effect.Local (andR8Imm8Effect p len dst imm) := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [andR8Imm8Effect, h.read_reg]
  · intro s
    simp [andR8Imm8Effect, Write.Full, Operand.Full]

attribute [x86_compose] andR8Imm8Effect notAlEffect incClEffect xorR8M8LegacyEffect incSpec

end P256.Proofs.Common.Instructions.ByteLogic
