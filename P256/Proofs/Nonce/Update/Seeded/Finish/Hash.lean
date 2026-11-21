import P256.Proofs.Nonce.Update.Seeded.Finish.State
import P256.Proofs.Nonce.Update.Finish.HashMemory

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Seeded.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem hash [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {original state : State} {input : ByteArray}
    (pre : DrbgCalleePre initial boundary 0x109f30 1856 original)
    (current : HashReady initial s state input)
    (inputSize : input.size = 97) :
    ∃ fuel t, Advances boundary fuel s t ∧ Hashed initial t state input := by
  let layout : StackCallLayout 1856 32 168 672 :=
    ⟨688, 680, 248, by decide, by decide, by decide, by decide,
      by decide, by decide, .inl (by decide)⟩
  have stateAddress : scratch initial + 432#64 = stackPtr initial - 248#64 := by
    simp only [scratch, BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  obtain ⟨t, result⟩ := Update.Finish.hmac_call pre current.toFrameState layout
    (by rfl) (by decide) (by decide) (by decide) 0xa890 0xffff667b
    (by decide) (by decide +kernel) (by decide +kernel) current.rip
    current.outputPointer (current.hashPointer.trans stateAddress)
    current.drbg.key_size (.inr (.inr inputSize))
    (by simpa only [BitVec.ofNat_eq_ofNat, stateAddress, layout] using current.hmac)
  have saved : memLoad t.external (scratch initial + 72) 64 = initial.regValue .rdi := by
    apply Eq.trans _ current.savedPointer
    apply memLoad_congr
    intro i hi
    apply congrArg (fun x : Option UInt8 => x.getD 0)
    have savedAddress : scratch initial + 72 = stackPtr initial - 608 := by
      simp only [scratch, BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
    rw [savedAddress]
    exact result.stack_byte pre (by decide) (by decide) (by decide)
      (by decide) (by decide) (.inl (by decide)) (.inr (by decide)) hi
  obtain ⟨fuel, run⟩ := result.execution
  exact ⟨fuel, t, run, ⟨result.toFrameState, current.drbg.copy result.drbg, saved⟩,
    result.rip, result.output⟩

end P256.Proofs.Nonce.Update.Seeded.Finish
