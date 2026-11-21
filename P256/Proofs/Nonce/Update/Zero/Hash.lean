import P256.Proofs.Nonce.Update.Zero.State
import P256.Proofs.Nonce.Update.Finish.HashMemory

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Zero

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem hash [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {original state : State} {input : ByteArray}
    (pre : DrbgCalleePre initial boundary 0x109f30 1856 original)
    (current : HashReady initial s state input)
    (inputSize : input.size = 33 ∨ input.size = 97) :
    ∃ fuel t, Advances boundary fuel s t ∧ Hashed initial t state input := by
  let layout : StackCallLayout 1856 32 168 672 :=
    ⟨688, 424, 248, by decide, by decide, by decide, by decide,
      by decide, by decide, .inl (by decide)⟩
  have stateAddress : scratch initial + 432#64 = stackPtr initial - 248#64 := by
    simp only [scratch, BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have outputAddress : scratch initial + 256#64 = stackPtr initial - 424#64 := by
    simp only [scratch, BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  obtain ⟨t, result⟩ := Finish.hmac_call (depth := 680) pre current.toFrameState layout
    (by rfl) (by decide) (by decide) (by decide) 0xa3f2 0xffff6b19
    (by decide) (by decide +kernel) (by decide +kernel) current.rip
    (by simpa only [BitVec.ofNat_eq_ofNat, outputAddress, layout] using current.outputPointer)
    (by simpa only [BitVec.ofNat_eq_ofNat, stateAddress, layout] using current.hashPointer)
    current.drbg.key_size (.inr inputSize)
    (by simpa only [BitVec.ofNat_eq_ofNat, stateAddress, layout] using current.hmac)
  have localAddress (offset : Nat) (bound : offset ≤ 680) :
      scratch initial + BitVec.ofNat 64 offset = stackPtr initial - BitVec.ofNat 64 (680-offset) := by
    rw [← show stackPtr s = scratch initial from current.rsp]
    exact ScalarFrame.scalar_stack_address current.rsp (by decide) bound
  have keep : ∀ offset ∈ ([64,72,80,424] : List Nat), ∀ i < 8,
      t.external[scratch initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
        s.external[scratch initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
    intro offset member i hi
    have cases : offset = 64 ∨ offset = 72 ∨ offset = 80 ∨ offset = 424 := by
      simpa using member
    rw [localAddress offset (by omega)]
    exact result.stack_byte (offset := 680-offset) (len := 8) pre (by decide) (by decide) (by decide)
      (by omega) (by omega) (.inl (by change 248 + 8 ≤ 680-offset; omega))
      (by change 424 + 8 ≤ 680-offset ∨ 680-offset+32 ≤ 424; omega) hi
  have context := current.toContext.of_copied result.toFrameState (current.drbg.copy result.drbg)
    ((result.calleeSaved .rbp (by simp)).trans current.descriptors) keep
  obtain ⟨fuel, run⟩ := result.execution
  refine ⟨fuel, t, run, context, result.rip, ?_⟩
  simpa only [BitVec.ofNat_eq_ofNat, outputAddress, layout] using result.output

end P256.Proofs.Nonce.Update.Zero
