import P256.Proofs.Common.Field.Montgomery.Schoolbook.CarryCompose
import P256.Proofs.Sec1.SquareRoot.Square.Wide.Arithmetic.DoubleTriple

set_option autoImplicit false

open P256.Proofs.Common.Instructions.ShiftLeft (shldOneFlags shldR64R64OneEffect)

namespace P256.Proofs.Sec1.SquareRoot.Square.Wide


open X86 X86.Machine X86.UserProcess X86Proofs

@[x86_local] theorem shldR64R64OneEffect_local (p : BitVec 64) (dst src : BitVec 5) :
    Effect.Local (shldR64R64OneEffect p dst src) := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [shldR64R64OneEffect, h.read_reg]
  · intro s
    simp [shldR64R64OneEffect, Write.Full, Operand.Full]

attribute [x86_compose] shldR64R64OneEffect shldOneFlags

@[x86_compose] theorem addSpec_low (a b : BitVec 64) : (addSpec a b).1 = a+b := rfl

end P256.Proofs.Sec1.SquareRoot.Square.Wide
