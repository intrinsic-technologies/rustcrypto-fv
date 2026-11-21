import Base16ct.Proofs.Copied.Md5.Proofs.Block.Rounds.Register.Or
namespace Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine

open X86 X86.Machine X86.UserProcess X86Proofs

attribute [x86_compose] subR32R32Effect

@[x86_local] theorem subR32R32Effect_local {p : BitVec 64} {len : Nat}
    {dst src : BitVec 5} : Effect.Local (subR32R32Effect p len dst src) := by
  refine ⟨fun t t' h => ?_, fun t t' h => ?_, fun t t' h => ?_,
    fun t t' h i hi => ?_, fun t => ?_⟩
  · rfl
  · simp only [subR32R32Effect, h.read_reg]
  · rfl
  · cases i <;> simp_all [subR32R32Effect, Effect.flag, StatusFlagsOutcome.get,
      StatusFlags.get, StatusFlagsOutcome.ofStatusFlags, h.read_reg]
  · simp [subR32R32Effect, Write.Full, Operand.Full]

end Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine
