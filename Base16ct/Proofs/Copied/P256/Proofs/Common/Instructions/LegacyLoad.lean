import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Decode

set_option autoImplicit false

namespace Base16ct.Proofs.Copied.P256.Proofs.Common.Instructions.LegacyLoad

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

def movR32M32LegacyEffect (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 (2 + am.tail.length)
    writes := [⟨(Operand.reg dst : Operand 64),
      ((Operand.mem (am.addr s (p + BitVec.ofNat 64 (2 + am.tail.length))) : Operand 32).read s).setWidth
        64⟩] }

end Base16ct.Proofs.Copied.P256.Proofs.Common.Instructions.LegacyLoad
