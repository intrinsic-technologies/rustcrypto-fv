import P256.Proofs.Signing.Core.Iteration.Components.Addition.Output.Selection.Store

set_option autoImplicit false

open P256.Proofs.Program

open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)
open P256.Proofs.SecretKeyFromBytes.Scalar (Limbs)
open P256.Proofs.Program (CalleePre memoryRegion_contains_add memoryRegion_memReadable
  inProgram_of_textOffset programLoaded_codeIn programText_slice)

namespace P256.Proofs.Signing.Core.Iteration.Components.Addition.Selection

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem output_pre [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x113310 32 32 64) (state : FrameState s t)
    (rip : t.RIP = 0x113ac4) (ptr : t.regValue .rax = s.regValue .rdi) : OutputPre t := by
  have readable := Program.readable_of_grow
    (memoryRegion_memReadable pre.outputBounded pre.outputAllocated (Nat.le_refl _) (Nat.le_refl _))
    state.allocated
  have writable : P256.Proofs.Common.Instructions.CrossPageStore.Writable t (s.regValue .rdi) 32 := by
    refine ⟨readable, ?_⟩
    apply tables_of_not_reserved (by change 0 < 32; decide) readable.low
    intro i hi hreserved
    exact pre.avoids _ (by simp) _
      (memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) hi) (.inr hreserved)
  have bounds (offset : Nat) (ho : offset ∈ [0,8,16,24]) : offset+8 ≤ 32 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl <;> decide
  refine ⟨rip, ?_, ?_⟩
  · intro offset ho
    rw [ptr]
    exact writable.add offset (bounds offset ho)
  · intro offset ho codeOffset codeLen bound i hi j hj he
    rw [ptr,BitVec.add_assoc,← BitVec.ofNat_add] at he
    apply pre.avoids _ (by simp) _
      (memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _)
        (show offset+i < 32 by have := bounds offset ho; omega))
    left
    rw [he,BitVec.add_assoc,← BitVec.ofNat_add]
    exact inProgram_of_textOffset (codeOffset+j) (by omega)

theorem output_writes [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x113310 32 32 64)
    (ptr : t.regValue .rax = s.regValue .rdi) :
    WritesWithin (outputEffect t).components #v[registerRegion s .rdi 32, workRegion s] := by
  have covered {offset : Nat} (bound : offset+8 ≤ 32) {a : BitVec 64}
      (ha : (Component.mem (s.regValue .rdi + BitVec.ofNat 64 offset) 8).Covers a) :
      (registerRegion s .rdi 32).Contains a.toNat := by
    obtain ⟨i,hi,rfl⟩ := ha
    rw [BitVec.add_assoc,← BitVec.ofNat_add]
    exact memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) (show offset+i < 32 by omega)
  intro c hc a ha
  simp only [outputEffect, Effect.components, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false, Write.component_mem] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  all_goals refine ⟨registerRegion s .rdi 32, by simp, ?_⟩
  · change (Component.mem (t.regValue .rax + BitVec.ofNat 64 0) 8).Covers a at ha
    rw [ptr] at ha
    exact covered (by decide) ha
  · change (Component.mem (t.regValue .rax + BitVec.ofNat 64 8) 8).Covers a at ha
    rw [ptr] at ha
    exact covered (by decide) ha
  · change (Component.mem (t.regValue .rax + BitVec.ofNat 64 16) 8).Covers a at ha
    rw [ptr] at ha
    exact covered (by decide) ha
  · change (Component.mem (t.regValue .rax + BitVec.ofNat 64 24) 8).Covers a at ha
    rw [ptr] at ha
    exact covered (by decide) ha

theorem store_output [Bindings] {s t : RamState} {boundary : ReturnBoundary} {a : Limbs}
    (pre : CalleePre s boundary 0x113310 32 32 64) (state : FrameState s t)
    (rip : t.RIP = 0x113ac4) (ptr : t.regValue .rax = s.regValue .rdi)
    (value : Limbs.mk (t.regValue .rdi) (t.regValue .rdx) (t.regValue .rsi) (t.regValue .rcx) = a) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u ∧ u.RIP = 0x113ad3 ∧
      Nat256At u (s.regValue .rdi) a.toNat := by
  obtain ⟨fuel,u,run,ready,_,effect⟩ := output_correct boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x13ac4 outputBytes
      (by decide +kernel) (by decide +kernel)) (output_pre pre state rip ptr)
  have final := state.after_effect pre ready effect.agrees (output_writes pre ptr)
    (by simp [outputEffect,Effect.components])
  refine ⟨fuel,u,run,final,effect.rip,?_⟩
  have limbs : P256.Proofs.Field.readLimbs u (s.regValue .rdi) = a := by
    rw [← value]
    have h0 : (Operand.mem (t.regValue .rax + 0#64) : Operand 64).read u = t.regValue .rdi := effect.writes.1
    have h1 : (Operand.mem (t.regValue .rax + 8) : Operand 64).read u = t.regValue .rdx := effect.writes.2.1
    have h2 : (Operand.mem (t.regValue .rax + 16) : Operand 64).read u = t.regValue .rsi := effect.writes.2.2.1
    have h3 : (Operand.mem (t.regValue .rax + 24) : Operand 64).read u = t.regValue .rcx := effect.writes.2.2.2
    rw [ptr,BitVec.add_zero] at h0
    rw [ptr] at h1 h2 h3
    change memLoad u.external _ 64 = _ at h0 h1 h2 h3
    unfold P256.Proofs.Field.readLimbs
    rw [h0,h1,h2,h3]

  rw [← limbs]
  apply P256.Proofs.Field.nat256At_readLimbs
  intro i hi
  exact final.allocated _
    ((memoryRegion_memReadable pre.outputBounded pre.outputAllocated (Nat.le_refl _) (Nat.le_refl _)).mem i hi)

end P256.Proofs.Signing.Core.Iteration.Components.Addition.Selection
