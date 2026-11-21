import Base16ct.Proofs.Copied.Md5.Proofs.Buffered.FinalizeReset.Length.Register
namespace Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine

open X86 X86.Machine X86.UserProcess X86Proofs

attribute [x86_compose] shrR32Effect

@[x86_local] theorem shrR32Effect_local {p : BitVec 64} {len : Nat}
    {dst : BitVec 5} {c : Nat} : Effect.Local (shrR32Effect p len dst c) := by
  refine ⟨fun _ _ _ ↦ rfl, fun t t' h ↦ ?_, fun _ _ _ ↦ rfl,
    fun t t' h i hi ↦ ?_, fun _ ↦ ?_⟩
  · simp only [shrR32Effect, h.read_reg]
  · by_cases h0 : c = 0 <;> by_cases h1 : c = 1 <;> cases i <;>
      simp_all [shrR32Effect, Effect.flag, StatusFlagsOutcome.get,
        StatusFlags.get, StatusFlagsOutcome.ofStatusFlags, shrFlags, h.read_reg]
  · simp [shrR32Effect, Write.Full, Operand.Full]

end Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine
