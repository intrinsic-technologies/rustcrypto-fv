import Md5.Proofs.MemoryRoutines.Register.Neg
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

namespace Md5.Proofs.MemoryRoutines.Register

open X86 X86.Machine X86.UserProcess X86Proofs

attribute [x86_compose] negR32Effect andR32Imm8Effect

@[x86_local] theorem negR32Effect_local (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    Effect.Local (negR32Effect p len dst) := by
  refine ⟨fun _ _ _ ↦ rfl, fun t t' h ↦ ?_, fun _ _ _ ↦ rfl,
    fun t t' h i _ ↦ ?_, fun _ ↦ ?_⟩
  · simp [negR32Effect, h.read_reg]
  · cases i <;> simp [negR32Effect, Effect.flag, h.read_reg]
  · simp [negR32Effect, Write.Full, Operand.Full]

@[x86_local] theorem andR32Imm8Effect_local (p : BitVec 64) (len : Nat)
    (dst : BitVec 5) (imm : BitVec 8) : Effect.Local (andR32Imm8Effect p len dst imm) := by
  refine ⟨fun _ _ _ ↦ rfl, fun t t' h ↦ ?_, fun _ _ _ ↦ rfl,
    fun t t' h i _ ↦ ?_, fun _ ↦ ?_⟩
  · simp [andR32Imm8Effect, h.read_reg]
  · cases i <;> simp [andR32Imm8Effect, Effect.flag, h.read_reg]
  · simp [andR32Imm8Effect, Write.Full, Operand.Full]

end Md5.Proofs.MemoryRoutines.Register
