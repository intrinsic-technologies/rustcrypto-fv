import Sha2.Proofs.Wrapper.Prologue
import Sha2.Proofs.Wrapper.Initialize.Payload

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper.Initialize

variable {v : Variant}

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.SHA256

 theorem pre [Bindings] {initial s : RamState} {inputs : Array Input}
    (ctx : Context initial inputs v) (input : Preserved initial s v) (rip : s.RIP = (v.pc 0x29)) :
    Store.Pre s v := by
  refine ⟨rip, ?_, ?_⟩
  · intro slot hs
    rw [stack_address input.rsp]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp only [BitVec.reduceSub]
    all_goals first
      | exact stack_writable8 ctx input.toState (by decide) (by decide)
      | exact stack_writable1 ctx input.toState (by decide)
  · intro slot hs offset len bound
    rw [stack_address input.rsp]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp only [BitVec.reduceSub]
    all_goals exact stack_codeApart ctx (by decide) (by decide) bound

 theorem local_writes [Bindings] {initial s : RamState} (input : Preserved initial s v) :
    LocalWrites initial (Store.effect s v).components := by
  intro c hc a ha
  simp only [Store.effect, Effect.components, List.map_cons, List.map_nil,
    Write.component, Operand.component, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
  all_goals try exact ha.elim
  all_goals rw [stack_address input.rsp] at ha
  all_goals simp only [BitVec.reduceSub, Nat.reduceDiv] at ha
  all_goals exact local_memory (by decide) (by decide) (by decide) a ha

 theorem store [Bindings] {initial s : RamState} {inputs : Array Input}
    (ctx : Context initial inputs v) (input : Preserved initial s v) (rip : s.RIP = (v.pc 0x29)) :
    ∃ t, Buffered initial t ByteArray.empty v ∧ t.RIP = (v.pc 0x85) ∧
      t.regValue .rsi = s.regValue .rsi := by
  obtain ⟨fuel, t, execution, ready, _, effect⟩ := Store.run (returnBoundary initial)
    (validCall_returnBoundary ctx.machine ctx.call).2.2 s
    (supportedMachine_readyToStep input.machine) (Store.code input.loaded) (pre ctx input rip)
  have preserved := preserved_of_agrees ctx input execution ready effect.agrees
    (local_writes input) (by simp [Store.effect, Effect.components, Write.component, Operand.component])
    (by simp [Store.effect, Effect.components, Write.component, Operand.component])
  refine ⟨t, ⟨preserved, ?_, ?_, ?_, ?_⟩, effect.rip, ?_⟩
  · have read : MemReadable t (rspOf s + 256) 32 := by
      rw [stack_address input.rsp]
      exact stack_readable ctx preserved.toState (offset := 88) (by decide) (by decide)
    have value := Store.hash_words effect read
    rw [stack_address input.rsp] at value
    simpa [compressBlocks, compressBlocksFrom] using value
  · constructor
    · rfl
    · intro i
      have impossible := i.isLt
      simp at impossible
  · have read : MemReadable t (rspOf s + 255) 1 := by
      rw [stack_address input.rsp]
      exact stack_readable ctx preserved.toState (offset := 89) (by decide) (by decide)
    have value := Store.tail_length effect read
    rw [stack_address input.rsp] at value
    simpa using value
  · have value := Store.blocks effect
    rw [stack_address input.rsp] at value
    simpa using value
  · exact effect.agrees.read (n := 64) (r := 6)
      (by simp [Store.effect, Effect.components, Write.component, Operand.component])

 theorem run [Bindings] {initial : RamState} {inputs : Array Input}
    (ctx : Context initial inputs v) :
    ∃ s, Buffered initial s ByteArray.empty v ∧ s.RIP = (v.pc 0x85) ∧
      s.regValue .rsi = initial.regValue .rsi := by
  obtain ⟨saved, hs⟩ := Prologue.run ctx
  obtain ⟨header, hh, rip, count⟩ := Prologue.header ctx hs
  obtain ⟨s, hs, rip, kept⟩ := store ctx hh rip
  exact ⟨s, hs, rip, kept.trans count⟩

end Sha2.Proofs.Wrapper.Initialize
