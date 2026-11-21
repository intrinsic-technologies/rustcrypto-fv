import P256.Proofs.Program.Compare.Instructions.Common
namespace P256.Proofs.Program.Compare.Instructions
open X86 X86.Machine X86.UserProcess X86Proofs
attribute [x86_compose] andR32Imm8Effect
@[x86_local] theorem andR32Imm8Effect_local (p : BitVec 64) (len : Nat)
    (dst : BitVec 5) (imm : BitVec 8) : Effect.Local (andR32Imm8Effect p len dst imm) := by
  refine ⟨fun _ _ _ ↦ rfl, fun t t' h ↦ ?_, fun _ _ _ ↦ rfl,
    fun t t' h i _ ↦ ?_, fun _ ↦ ?_⟩
  · simp [andR32Imm8Effect, h.read_reg]
  · cases i <;> simp [andR32Imm8Effect, Effect.flag, h.read_reg]
  · simp [andR32Imm8Effect, Write.Full, Operand.Full]

end P256.Proofs.Program.Compare.Instructions
