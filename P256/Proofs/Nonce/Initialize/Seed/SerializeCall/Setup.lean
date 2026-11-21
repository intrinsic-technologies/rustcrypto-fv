import P256.Proofs.Nonce.Initialize.Seed.SerializeCall.Interface
import P256.Proofs.Nonce.Initialize.Seed.Serialize
import P256.Proofs.Nonce.Initialize.Prepare.Memory

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Seed

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

variable [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
  {orderAddress : BitVec 64}

theorem serialization_setup {value : Nat}
    (pre : Nonce.InitializePre initial boundary orderAddress)
    (reduced : Reduce.Selected initial s boundary value) :
    ∃ t, SerializationReady initial t boundary orderAddress value := by
  have blockPre : SerializePre s := by
    refine ⟨reduced.rip, ?_⟩
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact ScalarFrame.stack_readable pre.toCalleePre reduced.stage.toFrameState (offset := 176) (len := 8) (by decide) (by decide)
    · exact Prepare.argument_readable pre reduced.stage
  obtain ⟨fuel, t, run, ready, _, effect⟩ := serialize_run boundary pre.outerBoundary s
    (readyToStep reduced.stage.machine reduced.stage.bindingsSupported)
    (programText_slice (programLoaded_codeIn reduced.stage.loaded) 0x7b5c serializeBytes
      (by decide +kernel) (by decide +kernel)) blockPre
  have sp : stackPtr t = stackPtr s :=
    effect.agrees.read (n := 64) (r := 4) (by simp [serializeEffect, Effect.components])
  have memory : ∀ a : BitVec 64, t.external[a]? = s.external[a]? := by
    intro a
    apply effect.agrees.memory
    intro c hc
    simp only [serializeEffect, Effect.components, List.map_cons, List.map_nil,
      List.nil_append, List.append_nil, List.cons_append, Write.component_reg,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Component.Covers]
  have word : ∀ a : BitVec 64, memLoad t.external a 64 = memLoad s.external a 64 := by
    intro a
    apply memLoad_congr
    intro i hi
    change (t.external[_]?).getD 0 = (s.external[_]?).getD 0
    rw [memory]
  have order : memLoad s.external (stackPtr s + 296) 64 = orderAddress :=
    Prepare.argument_order pre reduced.stage
  have stage : Stage initial t boundary := reduced.stage.after_registers run ready effect.agrees (by
    intro c hc a ha
    simp only [serializeEffect, Effect.components, List.map_cons, List.map_nil,
      List.nil_append, List.append_nil, List.cons_append, Write.component_reg,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ha.elim)
    (by simp [serializeEffect, Effect.components])
  refine ⟨t, {
    stage := stage
    rip := effect.rip
    order := ?_
    buffer := ?_
    length := ?_
    secret := ?_
    output := ?_
    entropy := ?_
    outputPointer := (effect.agrees.read (n := 64) (r := 14)
      (by simp [serializeEffect, Effect.components])).trans reduced.outputPointer
    source := ?_
    orderArg := ?_
    destination := ?_
    count := ?_
    reduced := ?_
  }⟩
  · have h := effect.writes.2.2.1
    change t.regValue .r15 = memLoad s.external (stackPtr s + 296) 64 at h
    exact h.trans order
  · have h := effect.writes.1
    change t.regValue .r12 = stackPtr s + 200 at h
    simpa only [sp] using h
  · have h := effect.writes.2.2.2.2.2.1
    change t.regValue .rbx = memLoad s.external (stackPtr s + 176) 64 at h
    exact h.trans reduced.length
  · rw [sp, word]; exact reduced.secret
  · rw [sp, word]; exact reduced.output
  · rw [sp, word]; exact reduced.entropy
  · have h := effect.writes.2.1
    change t.regValue .rdi = s.regValue .rbp at h
    simpa only [sp] using h.trans reduced.buffer
  · have h := effect.writes.2.2.2.1
    change t.regValue .rsi = memLoad s.external (stackPtr s + 296) 64 at h
    exact h.trans order
  · have h := effect.writes.2.2.2.2.1
    change t.regValue .rdx = stackPtr s + 200 at h
    simpa only [sp] using h
  · have h := effect.writes.2.2.2.2.2.2
    change t.regValue .rcx = memLoad s.external (stackPtr s + 176) 64 at h
    exact h.trans reduced.length
  · rw [sp]
    exact ⟨reduced.value.1, fun i hi => (memory _).trans (reduced.value.2 i hi)⟩

end P256.Proofs.Nonce.Initialize.Seed
