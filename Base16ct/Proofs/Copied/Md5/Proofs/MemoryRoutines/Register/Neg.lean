import X86Proofs.Instructions.Sub.Operation
import X86Proofs.Core.Operand
import X86Proofs.Step.Decode.Legacy0
import X86Proofs.Step.Decode.Legacy0OpcodeF7
import X86Proofs.Step.AfterStep
import X86Proofs.Step.LegacyStep
import X86Proofs.Program.Effect

namespace Base16ct.Proofs.Copied.Md5.Proofs.MemoryRoutines.Register

open X86 X86.Helpers X86Proofs X86.Machine X86.UserProcess

def negR32Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 32).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64), (-a).setWidth 64⟩]
    flags := some (.ofStatusFlags (subSpec 0 a).2) }

end Base16ct.Proofs.Copied.Md5.Proofs.MemoryRoutines.Register
