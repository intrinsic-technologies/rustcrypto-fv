import P256.Proofs.Nonce.Update.Zero.Copy
import P256.Proofs.Nonce.Update.Zero.PrepareHash
import P256.Proofs.Nonce.Update.Zero.Hash
import P256.Proofs.Nonce.Update.Zero.Save
import P256.Proofs.Nonce.Update.Finish.ValueMemory

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem zero [Bindings]
    {initial s : RamState} {boundary : ReturnBoundary}
    {state : State} {input : UpdateInput}
    (pre : UpdatePre initial boundary state input) (absorbed : Absorbed initial s state input) :
    ∃ fuel t, Advances boundary fuel s t ∧ RoundZeroDone initial t state input := by
  obtain ⟨_, u, setupRun, copyReady⟩ := Zero.setup_copy pre.drbg absorbed
  obtain ⟨_, v, copyRun, copied⟩ := Zero.copy_hmac pre.drbg copyReady
  obtain ⟨_, w, prepareRun, hashReady⟩ := Zero.prepare_hash pre.drbg copied
  have inputSize : (state.value ++ ⟨#[0]⟩ ++ input.seed).size = 33 ∨
      (state.value ++ ⟨#[0]⟩ ++ input.seed).size = 97 := by
    cases input with
    | empty =>
      left
      simp only [ByteArray.size_append, UpdateInput.seed, ByteArray.size_empty,
        hashReady.drbg.value_size]
      rfl
    | seeded secret reduced =>
      right
      simp only [ByteArray.size_append, UpdateInput.seed,
        hashReady.drbg.value_size, pre.secretSize, pre.reducedSize]
      rfl
  obtain ⟨_, x, hashRun, hashed⟩ := Zero.hash pre.drbg hashReady inputSize
  obtain ⟨_, y, saveRun, valueReady⟩ := Zero.Save.store pre.drbg hashed
  obtain ⟨t, result⟩ := Finish.value_call (depth := 680) pre.drbg valueReady.toFrameState
    (by decide) (by decide) (by decide) 0xa441 0x4ba
    (by decide) (by decide +kernel) (by decide +kernel) valueReady.rip
    valueReady.drbgPointer valueReady.drbg
  have localAddress (offset : Nat) (bound : offset ≤ 680) :
      scratch initial + BitVec.ofNat 64 offset = stackPtr initial - BitVec.ofNat 64 (680-offset) := by
    rw [← show stackPtr y = scratch initial from valueReady.rsp]
    exact Program.ScalarFrame.scalar_stack_address valueReady.rsp (by decide) bound
  have keep : ∀ offset ∈ ([64,72,80,424] : List Nat), ∀ i < 8,
      t.external[scratch initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
        y.external[scratch initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
    intro offset member i hi
    have bound : offset ≤ 424 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      omega
    rw [localAddress offset (by omega)]
    exact result.stack_byte (offset := 680-offset) (len := 8) pre.drbg (by decide) (by omega) (by omega) hi
  have context := valueReady.toContext.of_copied result.toFrameState result.drbg
    ((result.calleeSaved .rbp (by simp)).trans valueReady.descriptors) keep
  obtain ⟨fuel, valueRun⟩ := result.execution
  exact ⟨_, t, ((((setupRun.trans copyRun).trans prepareRun).trans hashRun).trans saveRun).trans valueRun,
    context.toFrameState, result.rip, context.drbg,
    (result.calleeSaved .rbx (by simp)).trans valueReady.savedDrbgPointer,
    context.savedPointer, context.savedValue, context.savedCount, context.descriptors, context.savedEnd⟩

end P256.Proofs.Nonce.Update
