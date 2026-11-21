import X86Proofs.Step.Address
import X86Proofs.Program.ReadWrite.WriteResult
import X86Proofs.Instructions.Lea.Decode
import X86Proofs.Instructions.MovLoad.Step
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Step.LegacyStep
import X86Proofs.Instructions.MovStore.Decode

set_option autoImplicit false

namespace Base16ct.Proofs.Copied.P256.Proofs.Common.Instructions.Lea32

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

def leaR32Effect (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (len : Nat)
    (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      ((am.addr s (p + BitVec.ofNat 64 len)).setWidth 32).setWidth 64⟩] }

end Base16ct.Proofs.Copied.P256.Proofs.Common.Instructions.Lea32
