import P256.Proofs.Projective.Multiply.Machine.Lookup.Select.Setup.Effect
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Program.Push
import X86Proofs.Instructions.Sub.Generated.Imm8.Triple

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)

open P256.Proofs.Program (CalleePre boundary_ne_program inProgram_of_textOffset memoryRegion_contains_add programLoaded_codeIn programText_slice stack_region_end readyToStep)

namespace P256.Proofs.Projective.Multiply.Machine.Lookup.Select

open P256.Proofs.Field P256.Proofs.Program P256.Spec.Program.Routines
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

attribute [local x86_compose] pushR64Effect pushEffect pushAddr stackPtr subR64Imm8Effect

def prepareBytes : List UInt8 :=
  [0x53, 0x48, 0x83, 0xec, 0x20, 0x41, 0x89, 0xc8, 0x48, 0x89, 0xfb]

def prepareEffect (s : RamState) : Effect :=
  { rip := 0x11438b
    writes := [
      ⟨(.reg 4 : Operand 64), scratch s⟩,
      ⟨(.reg 8 : Operand 64), (s.regValue .rcx).setWidth 32 |>.setWidth 64⟩,
      ⟨(.reg 3 : Operand 64), s.regValue .rdi⟩,
      ⟨(.mem (stackPtr s - 8) : Operand 64), s.regValue .rbx⟩]
    flags := some (.ofStatusFlags (subSpec (stackPtr s - 8) (32 : BitVec 64)).2) }

theorem prepare_push_apart [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x114380 32 32 128) {len : Nat} (hlen : len ≤ 11) :
    RangeApart (pushAddr s) 8 0x114380 len := by
  intro i hi j hj he
  have hin : (Stack.region s 128).Contains (pushAddr s + BitVec.ofNat 64 i).toNat := by
    apply memoryRegion_contains_add pre.stack.1 (len := 8) _ _ hi
    · rw [show pushAddr s = stackPtr s - BitVec.ofNat 64 8 from rfl,
        P256.Proofs.Program.stack_sub_toNat pre.stack (by decide)]
      change (stackPtr s).toNat - 128 ≤ (stackPtr s).toNat - 8
      omega
    · rw [stack_region_end, show pushAddr s = stackPtr s - BitVec.ofNat 64 8 from rfl,
        P256.Proofs.Program.stack_sub_toNat pre.stack (by decide)]
      have := (P256.Proofs.Program.stack_bounds pre.stack).1
      omega
  apply pre.avoids _ (by simp) _ hin (.inl ?_)
  rw [he]
  have hcode := inProgram_of_textOffset (0x14380 + j) (by omega)
  change InProgram (BitVec.ofNat 64 0x114380 + BitVec.ofNat 64 j)
  simpa only [Extracted.textAddress, BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.reduceAdd] using hcode

set_option maxHeartbeats 800000 in
theorem prepare_block [Bindings] (boundary : ReturnBoundary) :
    AdvanceTriple boundary (fun s => CalleePre s boundary 0x114380 32 32 128)
      (codeRange 0x114380 prepareBytes) (Effect.post prepareEffect) := by
  advance_begin (push_r64_effect_step 0x114380 0x53 (by decide +kernel))
  case pre =>
    intro s hP
    exact ⟨hP.rip, P256.Proofs.Program.stack_sub_writable8 hP.stack (fun a ha hp => hP.avoids _ (by simp) a ha (.inr hp)) (offset := 8) (by decide) (by decide),
      prepare_push_apart hP (by decide)⟩
  case av =>
    intro s hP
    apply Effect.avoids_codeRange
    intro c hc a len he
    subst c
    simp only [pushR64Effect_components, List.mem_cons, List.not_mem_nil, or_false,
      reduceCtorEq, false_or, Component.mem.injEq] at hc
    obtain ⟨ha, hl⟩ := hc
    subst a
    subst len
    exact prepare_push_apart hP (len := prepareBytes.length) (by decide)
  case next =>
    intro s hP
    exact boundary_ne_program hP.outerBoundary (inProgram_of_textOffset 0x14381 (by decide))
  advance_then (sub_r64_imm8_effect_step 0x114381 0x48 0xec 32
    (by simp [RexWPrefix]) (by decide) (by decide))
  case sub => exact codeRange_slice_subset 0x114380 prepareBytes 1 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · exact subR64Imm8Effect_avoids _ _ _ _ _
    · exact boundary_ne_program hP.outerBoundary (inProgram_of_textOffset 0x14385 (by decide))
  advance_then (mov_r32_r32_rex_effect_step 0x114385 0x41 0xc8
    (by simp [RexNoWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x114380 prepareBytes 5 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hP.outerBoundary (inProgram_of_textOffset 0x14388 (by decide))
  advance_then (mov_r64_r64_effect_step 0x114388 0x48 0xfb
    (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x114380 prepareBytes 8 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip, ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hP.outerBoundary (inProgram_of_textOffset 0x1438b (by decide))
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [prepareEffect, scratch, stackPtr]
  · x86_norm [prepareEffect, scratch, stackPtr]
    refine ⟨?_, rfl, rfl, rfl⟩
    rw [BitVec.sub_sub]
    rfl
  · intro i; cases i <;> x86_norm [prepareEffect, scratch, stackPtr]
  · x86_norm [prepareEffect, scratch, stackPtr]

theorem setup_prepare [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x114380 32 32 128) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      (prepareEffect s).Holds s t := by
  obtain ⟨fuel, t, run, ready, _, effect⟩ := prepare_block boundary s
    (readyToStep pre.machine pre.bindingsSupported)
    (programText_slice (programLoaded_codeIn pre.loaded) 0x14380 prepareBytes
      (by decide) (by decide +kernel)) pre
  refine ⟨fuel, t, run, ready, ?_, effect⟩
  intro a b hfetch
  rw [effect.agrees.byte]
  · exact pre.loaded a b hfetch
  · intro c hc ha
    simp only [prepareEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component_reg, Write.component_mem, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> try exact ha.elim
    obtain ⟨i, hi, rfl⟩ := ha
    apply pre.avoids (Stack.region s 128) (by simp) _ _ (.inl ⟨b, hfetch⟩)
    apply memoryRegion_contains_add pre.stack.1 (len := 8) _ _ hi
    · change (Stack.region s 128).start ≤ (stackPtr s - BitVec.ofNat 64 8).toNat
      rw [P256.Proofs.Program.stack_sub_toNat pre.stack (offset := 8) (by decide)]
      change (stackPtr s).toNat - 128 ≤ (stackPtr s).toNat - 8
      omega
    · change (stackPtr s - BitVec.ofNat 64 8).toNat + 8 ≤ _
      rw [stack_region_end, P256.Proofs.Program.stack_sub_toNat pre.stack (offset := 8) (by decide)]
      have := (P256.Proofs.Program.stack_bounds pre.stack).1
      omega

end P256.Proofs.Projective.Multiply.Machine.Lookup.Select
