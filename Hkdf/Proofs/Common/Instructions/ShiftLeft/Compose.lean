import Hkdf.Proofs.Common.EffectCompose
import Hkdf.Proofs.Common.Instructions.ShiftLeft.Triple

set_option autoImplicit false

namespace Hkdf.Proofs.Common.Instructions.ShiftLeft

open X86 X86.Machine X86.UserProcess X86Proofs

@[x86_local] theorem shlR64Effect_local (p : BitVec 64) (len : Nat)
    (dst : BitVec 5) (count : Nat) (nonzero : count ≠ 0) :
    Effect.Local (shlR64Effect p len dst count) := by
  apply Hkdf.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t ho
    simp only [shlR64Effect, shlFlags, nonzero, ite_false, ho.read_reg]
  · intro t
    simp [shlR64Effect, Write.Full, Operand.Full]

end Hkdf.Proofs.Common.Instructions.ShiftLeft
