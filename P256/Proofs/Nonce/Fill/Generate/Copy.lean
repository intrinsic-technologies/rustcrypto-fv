import P256.Proofs.Nonce.Fill.Generate.Copy.Memory

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill.Generate

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program

theorem copy [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} {original state : State}
    (pre : Pre initial boundary orderAddress original)
    (input : HasValue initial s orderAddress state) :
    ∃ fuel t, Advances boundary fuel s t ∧ Copied initial t orderAddress state := by
  obtain ⟨prepared, prefixRun, preparedState⟩ := Copy.prepare pre input
  obtain ⟨called, callRun, ready, effect⟩ := Copy.push pre preparedState
  have calleePre := Copy.call_pre pre preparedState ready effect
  have count : called.regValue .rdx = 32 :=
    (effect.agrees.read (n := 64) (r := 2) (by simp)).trans preparedState.rdx
  obtain ⟨t, result, copied, agrees⟩ := memcpy_correct calleePre count (by decide)
  have memory := Copy.result_memory pre preparedState effect agrees
  obtain ⟨fuel, run⟩ := result.execution
  refine ⟨3 + 1 + fuel, t, (prefixRun.trans callRun).trans run,
    preparedState.toFrame.after_call_result pre effect result (Copy.result_work pre memory),
    Copy.result_slots pre preparedState.toSlots memory,
    result.rip.trans (callEffect_stack effect).1, ?_, ?_,
    Copy.result_generator pre memory preparedState.generator, ?_⟩
  · exact (result.calleeSaved .rbp (by simp)).trans
      ((effect.agrees.read (n := 64) (r := 5) (by simp)).trans preparedState.rbp)
  · exact (result.calleeSaved .r15 (by simp)).trans
      ((effect.agrees.read (n := 64) (r := 15) (by simp)).trans preparedState.r15)
  · have source : called.regValue .rsi = initial.regValue .rdi + 40 :=
      (effect.agrees.read (n := 64) (r := 6) (by simp)).trans preparedState.rsi
    have destination : called.regValue .rdi = initial.regValue .rsi :=
      (effect.agrees.read (n := 64) (r := 7) (by simp)).trans preparedState.rdi
    have generator := call_generator pre preparedState.toFrame effect preparedState.generator
    have bytes : (MemoryRegion.mk (called.regValue .rsi).toNat 32).HasBytes called.external
        (updateValue state).value := by
      rw [source]
      have value := generator.2.2.2
      change (MemoryRegion.mk ((initial.regValue .rdi + 8) + 32).toNat 32).HasBytes
        called.external (updateValue state).value at value
      rw [BitVec.add_assoc] at value
      exact value
    have output := hasBytes_copy bytes copied
    simpa only [registerRegion, destination] using output

end P256.Proofs.Nonce.Fill.Generate
