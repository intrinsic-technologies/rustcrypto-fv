import P256.Proofs.Common.EffectCompose
import P256.Proofs.Common.Encoding.Serialize.Tail.ByteOps.Store
import X86Proofs.Program.Compose

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Radix

open X86 X86.Machine X86.UserProcess X86Proofs

@[x86_local] theorem storeByte_local (p : BitVec 64) (len : Nat) (am : AddrMode) (r : BitVec 5) :
    Effect.Local (storeEffect p len (storeAddrAt p am len)
      (fun s => (Operand.reg r : Operand 8).read s)) := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [storeEffect, storeAddrAt, AddrMode.addr_obs h, h.read_reg]
  · intro s
    simp [storeEffect, Write.Full, Operand.Full]

end P256.Proofs.Projective.Multiply.Machine.Radix
