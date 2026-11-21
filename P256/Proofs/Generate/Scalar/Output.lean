import P256.Proofs.Generate.Scalar.Entry
import P256.Proofs.Generate.Scalar.Stores
import P256.Proofs.Program.ScalarFrame.Output

set_option autoImplicit false

namespace P256.Proofs.Generate.Scalar

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program
open SecretKeyFromBytes.Scalar (Nat256At nat256At_of_memLoad_limbs)

theorem output_limbs [Bindings] {s t : RamState} {boundary : ReturnBoundary} {value : Nat}
    (pre : Pre s boundary) (state : State s t) (rip : t.RIP = 0x112fab)
    (output : t.regValue .rbx = s.regValue .rdi) (bound : value < 2^256)
    (decoded : Decoded t value) :
    ∃ n u, Advances boundary n t u ∧ State s u ∧ u.RIP = 0x112fba ∧
      Nat256At u (s.regValue .rdi) value ∧
      AgreesExcept [.mem (s.regValue .rdi + 0#64) 8, .mem (s.regValue .rdi + 8#64) 8,
        .mem (s.regValue .rdi + 16#64) 8, .mem (s.regValue .rdi + 24#64) 8, .rip] t u := by
  have hp : StoreLimbsPre t := by
    refine ⟨rip, ?_, ?_⟩
    · intro i hi
      change Common.Instructions.CrossPageStore.Writable t (t.regValue .rbx + i) 8
      rw [output]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      all_goals exact (ScalarFrame.output_writable pre (by decide) state.allocated).add _ (by decide)
    · intro i hi codeOffset len hlen
      change RangeApart (t.regValue .rbx + i) 8 _ len
      rw [output]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      all_goals exact Common.Instructions.RangeApart.add_left (ScalarFrame.output_code pre hlen) _ (by decide)
  obtain ⟨n, u, run, ready, _, effect⟩ := store_limbs_correct boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x12fab storeLimbsBytes
      (by decide) storeLimbs_bytes) hp
  have ag : AgreesExcept [.mem (s.regValue .rdi + 0#64) 8, .mem (s.regValue .rdi + 8#64) 8,
      .mem (s.regValue .rdi + 16#64) 8, .mem (s.regValue .rdi + 24#64) 8, .rip] t u := by
    have bx : (Operand.reg 3 : Operand 64).read t = s.regValue .rdi := output
    have g := effect.agrees
    simp only [storeLimbsEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component_mem, Nat.reduceDiv, List.append_nil, List.nil_append, List.cons_append] at g
    rw [bx] at g
    exact g
  have stateU := state.after_agrees pre ready ag (by
    apply ag.memoryWriteFrame
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> try exact ha.elim
    all_goals exact ⟨registerRegion s .rdi 33, by simp, ScalarFrame.output_contains pre (by decide) ha⟩)
    (by simp)
  have words := effect.writes
  change memLoad u.external (t.regValue .rbx + 0) 64 = t.regValue .r13 ∧
    memLoad u.external (t.regValue .rbx + 8) 64 = t.regValue .r12 ∧
    memLoad u.external (t.regValue .rbx + 16) 64 = t.regValue .r15 ∧
    memLoad u.external (t.regValue .rbx + 24) 64 = t.regValue .r14 at words
  rw [output] at words
  refine ⟨n, u, run, stateU, effect.rip, ?_, ag⟩
  apply nat256At_of_memLoad_limbs bound
  · intro i hi
    exact stateU.allocated _ (Option.isSome_iff_exists.mpr (pre.outputAllocated _
      (memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) (by omega : i < 33))))
  · intro j hj
    have casesJ : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases casesJ with rfl | rfl | rfl | rfl
    · simpa using words.1.trans decoded.1
    · exact words.2.1.trans decoded.2.1
    · exact words.2.2.1.trans decoded.2.2.1
    · exact words.2.2.2.trans decoded.2.2.2

end P256.Proofs.Generate.Scalar
