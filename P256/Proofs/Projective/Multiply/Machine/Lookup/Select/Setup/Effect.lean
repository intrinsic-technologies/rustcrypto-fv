import P256.Proofs.Projective.Multiply.Machine.Lookup.Select.State
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Not.Generated.R.Triple
import X86Proofs.Instructions.Rol.Generated.R.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Xor.Generated.RM.Triple
import X86Proofs.Instructions.Xor.Generated.MR.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Movs.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)

namespace P256.Proofs.Projective.Multiply.Machine.Lookup.Select

open P256.Proofs.Field P256.Proofs.Program P256.Spec.Program.Routines
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

def setupEffect (s : RamState) : Effect :=
  { rip := 0x1143ba
    writes := [
      ⟨(.reg 0 : Operand 64), (.mem (s.regValue .rsi) : Operand 64).read s⟩,
      ⟨(.reg 1 : Operand 64), 4⟩,
      ⟨(.reg 3 : Operand 64), s.regValue .rdi⟩,
      ⟨(.reg 4 : Operand 64), scratch s⟩,
      ⟨(.reg 6 : Operand 64), 4⟩,
      ⟨(.reg 7 : Operand 64), scratch s⟩,
      ⟨(.reg 8 : Operand 64), (s.regValue .rcx).setWidth 32 |>.setWidth 64⟩,
      ⟨(.mem (stackPtr s - 8) : Operand 64), s.regValue .rbx⟩,
      ⟨(.mem (scratch s) : Operand 64), (.mem (s.regValue .rsi) : Operand 64).read s⟩,
      ⟨(.mem (scratch s + 8) : Operand 64), (.mem (s.regValue .rsi + 8) : Operand 64).read s⟩,
      ⟨(.mem (scratch s + 16) : Operand 64), (.mem (s.regValue .rsi + 16) : Operand 64).read s⟩,
      ⟨(.mem (scratch s + 24) : Operand 64), (.mem (s.regValue .rsi + 24) : Operand 64).read s⟩]
    flags := some (.ofStatusFlags (subSpec (stackPtr s - 8) (32 : BitVec 64)).2) }

end P256.Proofs.Projective.Multiply.Machine.Lookup.Select
