import P256.Proofs.Nonce.Fill.Tail.Compare.Blocks.Copy

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill.Tail.Compare

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Signing.Search
open P256.Proofs.SecretKeyFromBytes.Scalar

structure ZeroPrepared [Bindings] (initial s : RamState) (orderAddress : BitVec 64)
    (state : Nonce.State) : Prop extends Compared initial s orderAddress state where
  rip : s.RIP = 0x1075e0
  rdi : s.regValue .rdi = frameBase initial + 72
  rdx : s.regValue .rdx = frameBase initial + 8
  rsi : s.regValue .rsi = 4
  rcx : s.regValue .rcx = 4
  zero : Nat256At s (frameBase initial + 8) 0

theorem zero_prepare [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} {original state : Nonce.State}
    (pre : Fill.Pre initial boundary orderAddress original)
    (input : Decoded initial s orderAddress state) :
    ∃ fuel t, Advances boundary fuel s t ∧ ZeroPrepared initial t orderAddress state := by
  obtain ⟨fuel, t, run, ready, _, effect⟩ := Blocks.copy_run boundary pre.outerBoundary s
    (readyToStep input.machine input.bindingsSupported)
    (programText_slice (programLoaded_codeIn input.loaded) 0x757a Blocks.copyBytes
      (by decide) (by decide +kernel)) (Blocks.block_pre pre input.toContext input.rip)
  have writes : WordWrites (frameBase initial) [8,16,24,32,72,80,88,96,152]
      (Blocks.copyEffect s).components := by
    intro c member a cover
    simp only [Blocks.copyEffect, Effect.components, Write.component, Operand.component,
      List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact cover.elim
    all_goals obtain ⟨i, hi, rfl⟩ := cover
    · exact ⟨8, by simp, i, hi, by rw [input.rsp]; rfl⟩
    · exact ⟨16, by simp, i, hi, by rw [input.rsp]; rfl⟩
    · exact ⟨24, by simp, i, hi, by rw [input.rsp]; rfl⟩
    · exact ⟨32, by simp, i, hi, by rw [input.rsp]; rfl⟩
    · exact ⟨72, by simp, i, hi, by rw [input.rsp]; rfl⟩
    · exact ⟨80, by simp, i, hi, by rw [input.rsp]; rfl⟩
    · exact ⟨88, by simp, i, hi, by rw [input.rsp]; rfl⟩
    · exact ⟨96, by simp, i, hi, by rw [input.rsp]; rfl⟩
    · exact ⟨152, by simp, i, hi, by rw [input.rsp]; rfl⟩
  have ctx := context_after_stack pre input.toContext ready effect.agrees writes
    (by intro off member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member; unfold ScratchOffset; omega)
    (by simp [Blocks.copyEffect, Effect.components])
    (by simp [Blocks.copyEffect, Effect.components])
    (by simp [Blocks.copyEffect, Effect.components])
  have values := effect.writes
  change t.regValue .rax = memLoad s.external (stackPtr s + 8) 64 ∧
    t.regValue .rcx = 4 ∧ t.regValue .rdx = s.regValue .r12 ∧ t.regValue .rsi = 4 ∧
    t.regValue .rdi = stackPtr s + 72 ∧
    memLoad t.external (stackPtr s + 8) 64 = 0 ∧
    memLoad t.external (stackPtr s + 16) 64 = 0 ∧
    memLoad t.external (stackPtr s + 24) 64 = 0 ∧
    memLoad t.external (stackPtr s + 32) 64 = 0 ∧
    memLoad t.external (stackPtr s + 72) 64 = memLoad s.external (stackPtr s + 8) 64 ∧
    memLoad t.external (stackPtr s + 80) 64 = memLoad s.external (stackPtr s + 16) 64 ∧
    memLoad t.external (stackPtr s + 88) 64 = memLoad s.external (stackPtr s + 24) 64 ∧
    memLoad t.external (stackPtr s + 96) 64 = memLoad s.external (stackPtr s + 32) 64 ∧
    memLoad t.external (stackPtr s + 152) 64 = memLoad s.external (stackPtr s + 8) 64 at values
  rw [input.rsp, input.r12] at values
  rcases values with ⟨_, cx, dx, si, di, z0, z1, z2, z3, a0, a1, a2, a3, _⟩
  have integer : Nat256At t (frameBase initial + 72) (nextCandidate state).1 := by
    apply nat256At_of_memLoad_limbs input.integer.1
    · have h := stack_readable pre ctx.toFrame (offset := 72) (len := 32) (by decide)
      rw [ctx.rsp] at h
      exact h.mem
    · intro j hj
      have h := input.integer.memLoad_limb j hj
      have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
      rcases cases with rfl | rfl | rfl | rfl
      all_goals simp only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] at h ⊢
      · exact a0.trans h
      · exact a1.trans h
      · exact a2.trans h
      · exact a3.trans h
  refine ⟨fuel, t, run, ⟨⟨ctx, integer⟩, effect.rip, di, dx, si, cx, ?_⟩⟩
  apply nat256At_of_memLoad_limbs (by decide)
  · have h := stack_readable pre ctx.toFrame (offset := 8) (len := 32) (by decide)
    rw [ctx.rsp] at h
    exact h.mem
  · intro j hj
    have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    all_goals simp only [Nat.reduceMul, Nat.zero_div, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero]
    · exact z0
    · exact z1
    · exact z2
    · exact z3

end P256.Proofs.Nonce.Fill.Tail.Compare
