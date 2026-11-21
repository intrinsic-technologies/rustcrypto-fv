import P256.Proofs.Generate.Sampler.FirstRead
import P256.Proofs.Generate.Sampler.Retry

set_option autoImplicit false

namespace P256.Proofs.Generate.Sampler

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem next_read [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {input : ByteArray} {offset : Nat} (pre : Pre s boundary input)
    (state : LoopReady s t input offset 0x100ce5 32)
    (remaining : t.regValue .rbx = BitVec.ofNat 64 (input.size-(offset+32)))
    (available : offset+32+32 ≤ input.size) :
    ∃ u, (∃ fuel, Advances boundary fuel t u) ∧ ReadReady s u input (offset+32) := by
  have bound : 32 ≤ ((Operand.reg 3 : Operand 64).read t).toNat := by
    change 32 ≤ (t.regValue .rbx).toNat
    rw [remaining,BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
    · omega
    · have low : (source s).toNat+input.size < 2^32 := pre.bounded
      omega
  obtain ⟨fuel,u,run,ready,_,effect⟩ := retry_run boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported) (retry_loaded state.loaded) ⟨state.rip,bound⟩
  have frame := state.toState.after_registers pre ready effect.agrees
    (by simp [retryEffect,Effect.components,Component.Covers]) (by simp [retryEffect,Effect.components])
  refine ⟨u,⟨fuel,run⟩,
    {toState := frame,rip := effect.rip,descriptor := ?_,source := ?_,
      remaining := ?_,decoded := ?_,buffer := ?_,output := ?_}⟩
  · exact (effect.agrees.read (n := 64) (r := 14) (by simp [retryEffect,Effect.components])).trans state.descriptor
  · have h : u.regValue .rbp = t.regValue .rbp+32#64 := effect.writes.1
    simp only [h,state.source,BitVec.ofNat_add,BitVec.add_assoc]
  · exact effect.writes.2.trans remaining
  · exact (effect.agrees.read (n := 64) (r := 15) (by simp [retryEffect,Effect.components])).trans state.decoded
  · exact (effect.agrees.read (n := 64) (r := 12) (by simp [retryEffect,Effect.components])).trans state.buffer
  · rw [effect.agrees.external (by simp [retryEffect,Effect.components,Component.Covers])]
    exact state.output

end P256.Proofs.Generate.Sampler
