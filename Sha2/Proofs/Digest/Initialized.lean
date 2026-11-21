import Sha2.Proofs.Digest.Initialize
import Sha2.Proofs.Digest.State
import Sha2.Proofs.Wrapper512.Machine.Initialize

set_option autoImplicit false

namespace Sha2.Proofs.Digest

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine
  X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Wrapper512
open Sha2.Proofs.Wrapper512.Machine.Initialize

 theorem initialized512 [Bindings] {v : Variant} {initial s : RamState} {inputs : Array Input}
    (ctx : Context v initial inputs .digest) (input : Preserved v initial s .digest)
    (rip : s.RIP = v.pc 0x1a .digest) :
    ∃ t, Buffered v initial t ByteArray.empty .digest ∧ t.RIP = v.pc 0xca .digest ∧
      t.regValue .rsi = s.regValue .rsi ∧ t.regValue .r14 = s.regValue .r14 := by
  obtain ⟨data,_,call⟩ := ctx.call
  have pre := initialize512_pre call input.toState.toExecutionState input.rsp rip
  obtain ⟨fuel,t,run,ready,_,effect⟩ := Dispatch.Store.run (form := .digest)
    (returnBoundary initial) (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2
    s (supportedMachine_readyToStep input.machine) (Dispatch.Store.code input.loaded .digest) pre
  have writes := local_writes input.toState
  have stateT := Wrapper512.Absorb.State.of_agrees input.toState ctx run ready effect.agrees (by
    intro c hc a ha
    refine ⟨Stack.region initial (v.routine .digest).minStackBytes,
      by exact Vector.mem_of_getElem (i := 1) (h := by decide) rfl, ?_⟩
    rcases writes c hc a ha with low | high
    · exact stackRegion_contains_sub ctx.stack.2.2.1 (by change 816 ≤ 1152; decide) (by decide) low
    · exact stackRegion_contains_sub ctx.stack.2.2.1 (by change 152 ≤ 1152; decide) (by decide) high)
    (by simp [Dispatch.Store.effectWithRegister, Dispatch.Store.registerWrites, Dispatch.Store.effect, Dispatch.Store.suffixEffect,
      Effect.components, Write.component, Operand.component]) writes.saved
    (by simp [Dispatch.Store.effectWithRegister, Dispatch.Store.registerWrites, Dispatch.Store.effect, Dispatch.Store.suffixEffect,
      Effect.components, Write.component, Operand.component])
  have output : t.regValue .rbx = s.regValue .rbx := effect.agrees.read (n := 64) (r := 3)
    (by simp [Dispatch.Store.effectWithRegister, Dispatch.Store.registerWrites, Dispatch.Store.effect, Dispatch.Store.suffixEffect,
      Effect.components, Write.component, Operand.component])
  have preservedT : Preserved v initial t .digest :=
    ⟨stateT,output.trans input.outputPointer,trivial,trivial⟩
  have address (offset : Nat) :
      rspOf s + BitVec.ofNat 64 (Dispatch.Store.slotOffset .digest offset) =
        stackPtr initial - (600#64 - BitVec.ofNat 64 (offset - 32)) := by
    exact stack_address input.rsp _
  refine ⟨t, ⟨preservedT, ?_, ?_, ?_, ?_, ?_⟩, effect.rip, ?_, ?_⟩
  · have read : MemReadable t (rspOf s + BitVec.ofNat 64 (Dispatch.Store.slotOffset .digest 0x170)) 64 := by
      rw [address]
      exact stack_readable ctx stateT (offset := 264) (by change 264 ≤ 1152; decide) (by decide)
    have value := hash_words (suffix_stores effect) read
    rw [address] at value
    exact value
  · constructor
    · rfl
    · intro i
      have h := i.isLt
      change i.val < 0 at h
      omega
  · have read : MemReadable t (rspOf s + BitVec.ofNat 64 (Dispatch.Store.slotOffset .digest 0x16f)) 1 := by
      rw [address]
      exact stack_readable ctx stateT (offset := 265) (by change 265 ≤ 1152; decide) (by decide)
    have value := tail_length (suffix_stores effect) read
    rw [address] at value
    exact value
  · have value := blocks (suffix_stores effect)
    rw [address] at value
    exact value
  · have value := blocks_high (suffix_stores effect)
    rw [address] at value
    exact value
  · exact effect.agrees.read (n := 64) (r := 6)
      (by simp [Dispatch.Store.effectWithRegister, Dispatch.Store.registerWrites, Dispatch.Store.effect, Dispatch.Store.suffixEffect,
        Effect.components, Write.component, Operand.component])
  · exact effect.agrees.read (n := 64) (r := 14)
      (by simp [Dispatch.Store.effectWithRegister, Dispatch.Store.registerWrites, Dispatch.Store.effect, Dispatch.Store.suffixEffect,
        Effect.components, Write.component, Operand.component])

end Sha2.Proofs.Digest
