import P256.Proofs.Nonce.Update.Seeded.Prepare.Assemble.State
import P256.Proofs.Nonce.Update.Seeded.Prepare.Assemble.Setup
import P256.Proofs.Common.Instructions.RepMovsqAny

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Seeded.Prepare.Assemble

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

structure RepReady [Bindings] (initial s : RamState) (state : State) : Prop extends
    Context initial s state where
  rip : s.RIP = 0x10a5a2
  bufferPointer : s.regValue .r12 = scratch initial + 320
  destination : s.regValue .rdi = scratch initial + 496
  source : s.regValue .rsi = scratch initial + 256
  count : s.regValue .rcx = 13
  key : (MemoryRegion.mk (scratch initial).toNat 64).HasBytes s.external
    (HMAC.keyPad state.key 0x5c)
  inner : HMAC.Sha256StateAt s (scratch initial + 256) (HMAC.keyPad state.key 0x36)

theorem setup_inner [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {original state : State} (pre : DrbgCalleePre initial boundary 0x109f30 1856 original)
    (current : OuterPadded initial s state) :
    ∃ fuel t, Advances boundary fuel s t ∧ RepReady initial t state := by
  obtain ⟨fuel, t, run, ready, _, effect⟩ := Setup.run boundary pre.outerBoundary s
    (readyToStep current.machine current.bindingsSupported) (Setup.code current.loaded) current.rip
  have agrees : AgreesExcept [.reg 7, .reg 6, .reg 1, .rip] s t := by
    simpa only [Setup.effect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.cons_append, List.nil_append] using effect.agrees
  have context := current.toContext.after_agrees pre ready agrees
    (by intro r member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl <;> decide)
    (by intro c member a covered
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl <;> exact covered.elim)
    (by intro i hi; rw [agrees.external (by simp [Component.Covers])])
  have memory : t.external = s.external := agrees.external (by simp [Component.Covers])
  have writes := effect.writes
  change t.regValue .rdi = rspOf s + 496 ∧
    t.regValue .rsi = rspOf s + 256 ∧ t.regValue .rcx = 13 at writes
  have rsp : rspOf s = scratch initial := current.rsp
  refine ⟨fuel, t, run, context, effect.rip,
    (agrees.read (n := 64) (r := 12) (by simp)).trans current.bufferPointer,
    ?_, ?_, writes.2.2, ?_, ?_⟩
  · exact writes.1.trans (congrArg (· + 496) rsp)
  · exact writes.2.1.trans (congrArg (· + 256) rsp)
  · rw [memory]; exact current.key
  · exact current.inner.copy (by intro i hi; rw [memory])

theorem run_inner [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {original state : State} (pre : DrbgCalleePre initial boundary 0x109f30 1856 original)
    (current : RepReady initial s state) :
    ∃ t, Advances boundary 13 s t ∧ InnerCopied initial t state := by
  have src : rsi.read s = stackPtr s + 256 := by
    change s.regValue .rsi = stackPtr s + 256
    rw [current.source, current.rsp]
    rfl
  have dst : rdi.read s = stackPtr s + 496 := by
    change s.regValue .rdi = stackPtr s + 496
    rw [current.destination, current.rsp]
    rfl
  have count : (rcx.read s).toNat = 13 := by
    change (s.regValue .rcx).toNat = 13
    rw [current.count]
    rfl
  have readable : MemReadable s (rsi.read s) 104 := by
    rw [src]
    exact stack_readable current.toFrameState pre (by decide) (by decide) (by decide)
  have writable : P256.Proofs.Common.Instructions.CrossPageStore.Writable s (rdi.read s) 104 := by
    rw [dst]
    exact stack_writable current.toFrameState pre (by decide) (by decide) (by decide) (by decide)
  have apart : (rsi.read s).toNat + 104 ≤ (rdi.read s).toNat ∨
      (rdi.read s).toNat + 104 ≤ (rsi.read s).toNat := by
    rw [src, dst]
    change (stackPtr s + BitVec.ofNat 64 256).toNat + 104 ≤
      (stackPtr s + BitVec.ofNat 64 496).toNat ∨
      (stackPtr s + BitVec.ofNat 64 496).toNat + 104 ≤ (stackPtr s + BitVec.ofNat 64 256).toNat
    rw [stack_address current.toFrameState (by decide : 256 ≤ 680),
      stack_address current.toFrameState (by decide : 496 ≤ 680)]
    rw [(stack_sub_toNat pre.stack) (by decide : 680 - 256 ≤ 1856),
      (stack_sub_toNat pre.stack) (by decide : 680 - 496 ≤ 1856)]
    have := stack_bounds pre.stack
    left
    omega
  have codeApart : RangeApart (rdi.read s) 104 0x10a5a2 3 := by
    rw [dst]
    exact stack_codeApart current.toFrameState pre (pc := 0xa5a2)
      (by decide) (by decide) (by decide) (by decide)
  have rep := P256.Proofs.Common.Instructions.RepMovsqAny.pre_of_memory current.rip
    current.directionFlag.df count readable writable apart codeApart
  obtain ⟨run, ready, effect, copied⟩ :=
    P256.Proofs.Common.Instructions.RepMovsqAny.rep_movsq_execution pre.bindingsSupported.stringStride
      (readyToStep current.machine current.bindingsSupported)
      (programText_slice (programLoaded_codeIn current.loaded) 0xa5a2 [0xf3,0x48,0xa5]
        (by decide) (by decide +kernel)) rep count
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xa5a2 (by decide)))
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xa5a5 (by decide)))
  simp only [show max 13 1 = 13 from rfl] at run ready effect copied
  generalize hu : nextStates 13 s = t at run ready effect copied
  have agrees : AgreesExcept [.reg 6, .reg 7, .reg 1,
      .mem (scratch initial + 496) 104, .rip] s t := by
    simpa only [repMovsqEffect_components, count,
      show rdi.read s = scratch initial + 496 from current.destination, Nat.reduceMul]
      using effect.agrees
  have context := current.toContext.after_agrees pre ready agrees
    (by intro r member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl <;> simp)
    (by intro c member a covered
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl
        all_goals try exact covered.elim
        exact Update.Prepare.work_contains_scratch pre (by decide) covered)
    (by
      intro i hi
      apply agrees.byte
      intro c member covered
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl
      all_goals try exact covered.elim
      obtain ⟨j, hj, equal⟩ := covered
      exact OffsetsApart.ne (len₁ := 24) (len₂ := 104)
        (by unfold OffsetsApart; decide +kernel) (scratch initial) hi hj (by decide) equal)
  refine ⟨t, run, context, effect.rip,
    (agrees.read (n := 64) (r := 12) (by simp)).trans current.bufferPointer, ?_, ?_⟩
  · apply hasBytes_copy current.key
    intro i hi
    apply agrees.byte
    intro c member covered
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    all_goals try exact covered.elim
    obtain ⟨j, hj, eq⟩ := covered
    exact OffsetsApart.ne (c₁ := 496) (len₁ := 104) (c₂ := 0#64) (len₂ := 64)
      (by unfold OffsetsApart; decide +kernel) (scratch initial) hj hi (by decide) (by simpa only [BitVec.add_zero] using eq.symm)
  · apply current.inner.copy
    simpa only [show rdi.read s = scratch initial + 496 from current.destination,
      show rsi.read s = scratch initial + 256 from current.source] using copied

theorem copy_inner [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {original state : State} (pre : DrbgCalleePre initial boundary 0x109f30 1856 original)
    (current : OuterPadded initial s state) :
    ∃ fuel t, Advances boundary fuel s t ∧ InnerCopied initial t state := by
  obtain ⟨fuel, t, setup, prepared⟩ := setup_inner pre current
  obtain ⟨u, run, result⟩ := run_inner pre prepared
  exact ⟨fuel + 13, u, setup.trans run, result⟩

end P256.Proofs.Nonce.Update.Seeded.Prepare.Assemble
