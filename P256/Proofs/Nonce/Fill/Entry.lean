import P256.Proofs.Nonce.Fill.Entry.Configure
import P256.Proofs.Nonce.Fill.Entry.Branch

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem entry [Bindings] {initial : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} {state : State} (pre : Pre initial boundary orderAddress state) :
    ∃ fuel t, Advances boundary fuel initial t ∧ Loop initial t orderAddress state := by
  obtain ⟨fuelS, s, runS, prepared⟩ := Entry.prepare pre
  obtain ⟨fuelU, u, runU, configured⟩ := Entry.configure pre prepared
  obtain ⟨t, runT, readyT, ripT, r12, rbx, agrees⟩ := Entry.branch
    (readyToStep configured.machine configured.bindingsSupported) configured.loaded configured.rip
    configured.r13 pre.outerBoundary (stack_readable pre configured.toFrame (by decide))
  have memory := agrees.external (by simp [Component.Covers])
  refine ⟨fuelS + fuelU + 5, t, (runS.trans runU).trans runT,
    configured.toFrame.after_registers readyT agrees (by simp [Component.Covers]) (by simp),
    configured.toSlots.of_memory_eq memory, ripT, ?_, ?_, rbx, ?_⟩
  · exact (agrees.read (n := 64) (r := 7) (by simp)).trans configured.rdi
  · rw [configured.rsp] at r12
    exact r12.trans configured.valuePointerSlot
  · simpa only [GeneratorAt, DrbgAt, SecretKeyFromBytes.Scalar.Nat256At, memory] using
      configured.generator

end P256.Proofs.Nonce.Fill
