import P256.Proofs.Nonce.UpdateValue.Prepare.Assemble.State
import P256.Proofs.Nonce.UpdateValue.Prepare.Assemble.Setup
import P256.Proofs.Common.Instructions.RepMovsqAny

set_option autoImplicit false

namespace P256.Proofs.Nonce.UpdateValue.Prepare.Assemble

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

structure RepReady [Bindings] (initial s : RamState) (state : State) : Prop extends
    Context initial s state where
  rip : s.RIP = 0x10aa70
  destination : s.regValue .rdi = scratch initial + 336
  source : s.regValue .rsi = scratch initial + 104
  count : s.regValue .rcx = 13
  bufferPointer : s.regValue .r14 = scratch initial + 168
  key : (MemoryRegion.mk (scratch initial + 8).toNat 64).HasBytes s.external
    (HMAC.keyPad state.key 0x5c)
  inner : HMAC.Sha256StateAt s (scratch initial + 104) (HMAC.keyPad state.key 0x36)

theorem setup_inner [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {state : State} (pre : DrbgCalleePre initial boundary 0x10a900 1168 state)
    (current : OuterPadded initial s state) :
    ∃ fuel t, Advances boundary fuel s t ∧ RepReady initial t state := by
  obtain ⟨fuel, t, run, ready, _, effect⟩ := Setup.run boundary pre.outerBoundary s
    (readyToStep current.machine current.bindingsSupported) (Setup.code current.loaded) current.rip
  have agrees : AgreesExcept [.reg 7, .reg 6, .reg 1, .rip] s t := by
    simpa only [Setup.effect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.cons_append, List.nil_append] using effect.agrees
  have context := current.toContext.after_agrees pre ready agrees
    (by intro r member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl <;> decide)
    (by intro c member a covered
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl <;> exact covered.elim)
  have memory : t.external = s.external := agrees.external (by simp [Component.Covers])
  have writes := effect.writes
  change t.regValue .rdi = rspOf s + 336 ∧
    t.regValue .rsi = rspOf s + 104 ∧ t.regValue .rcx = 13 at writes
  have rsp : rspOf s = scratch initial := current.rsp
  refine ⟨fuel, t, run, context, effect.rip, ?_, ?_, writes.2.2, ?_, ?_, ?_⟩
  · exact writes.1.trans (congrArg (· + 336) rsp)
  · exact writes.2.1.trans (congrArg (· + 104) rsp)
  · exact (agrees.read (n := 64) (r := 14) (by simp)).trans current.bufferPointer
  · rw [memory]; exact current.key
  · exact current.inner.copy (by intro i hi; rw [memory])

theorem run_inner [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {state : State} (pre : DrbgCalleePre initial boundary 0x10a900 1168 state)
    (current : RepReady initial s state) :
    ∃ t, Advances boundary 13 s t ∧ InnerCopied initial t state := by
  have src : rsi.read s = stackPtr s + 104 := by
    change s.regValue .rsi = stackPtr s + 104
    rw [current.source, current.rsp]
    rfl
  have dst : rdi.read s = stackPtr s + 336 := by
    change s.regValue .rdi = stackPtr s + 336
    rw [current.destination, current.rsp]
    rfl
  have count : (rcx.read s).toNat = 13 := by
    change (s.regValue .rcx).toNat = 13
    rw [current.count]
    rfl
  have readable : MemReadable s (rsi.read s) 104 := by
    rw [src]
    exact ScalarFrame.stack_readable pre.callee current.toFrameState (by decide) (by decide)
  have writable : P256.Proofs.Common.Instructions.CrossPageStore.Writable s (rdi.read s) 104 := by
    rw [dst]
    exact ScalarFrame.stack_writable pre.callee current.toFrameState (by decide) (by decide) (by decide)
  have apart : (rsi.read s).toNat + 104 ≤ (rdi.read s).toNat ∨
      (rdi.read s).toNat + 104 ≤ (rsi.read s).toNat := by
    rw [src, dst]
    change (stackPtr s + BitVec.ofNat 64 104).toNat + 104 ≤
      (stackPtr s + BitVec.ofNat 64 336).toNat ∨
      (stackPtr s + BitVec.ofNat 64 336).toNat + 104 ≤ (stackPtr s + BitVec.ofNat 64 104).toNat
    rw [ScalarFrame.scalar_stack_address current.rsp (by decide) (by decide : 104 ≤ 488),
      ScalarFrame.scalar_stack_address current.rsp (by decide) (by decide : 336 ≤ 488)]
    rw [stack_sub_toNat pre.stack (by decide : 488 - 104 ≤ 1168),
      stack_sub_toNat pre.stack (by decide : 488 - 336 ≤ 1168)]
    have := stack_bounds pre.stack
    left
    omega
  have codeApart : RangeApart (rdi.read s) 104 0x10aa70 3 := by
    rw [dst]
    exact ScalarFrame.stack_code pre.callee current.toFrameState (codeOffset := 0xaa70)
      (by decide) (by decide) (by decide)
  have rep := P256.Proofs.Common.Instructions.RepMovsqAny.pre_of_memory current.rip
    current.directionFlag.df count readable writable apart codeApart
  obtain ⟨run, ready, effect, copied⟩ :=
    P256.Proofs.Common.Instructions.RepMovsqAny.rep_movsq_execution pre.bindingsSupported.stringStride
      (readyToStep current.machine current.bindingsSupported)
      (programText_slice (programLoaded_codeIn current.loaded) 0xaa70 [0xf3,0x48,0xa5]
        (by decide) (by decide +kernel)) rep count
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xaa70 (by decide)))
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xaa73 (by decide)))
  simp only [show max 13 1 = 13 from rfl] at run ready effect copied
  generalize hu : nextStates 13 s = t at run ready effect copied
  have agrees : AgreesExcept [.reg 6, .reg 7, .reg 1,
      .mem (scratch initial + 336) 104, .rip] s t := by
    simpa only [repMovsqEffect_components, count,
      show rdi.read s = scratch initial + 336 from current.destination, Nat.reduceMul]
      using effect.agrees
  have context := current.toContext.after_agrees pre ready agrees
    (by intro r member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl <;> simp)
    (by intro c member a covered
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl
        all_goals try exact covered.elim
        exact work_contains_scratch pre (by decide) covered)
  refine ⟨t, run, context, effect.rip, ?_, ?_, ?_⟩
  · exact (agrees.read (n := 64) (r := 14) (by simp)).trans current.bufferPointer
  · apply hasBytes_copy current.key
    intro i hi
    apply agrees.byte
    intro c member covered
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    all_goals try exact covered.elim
    obtain ⟨j, hj, eq⟩ := covered
    exact OffsetsApart.ne (c₁ := 336) (len₁ := 104) (c₂ := 8) (len₂ := 64)
      (by unfold OffsetsApart; decide +kernel) (scratch initial) hj hi (by decide) eq.symm
  · apply current.inner.copy
    simpa only [show rdi.read s = scratch initial + 336 from current.destination,
      show rsi.read s = scratch initial + 104 from current.source] using copied

theorem copy_inner [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {state : State} (pre : DrbgCalleePre initial boundary 0x10a900 1168 state)
    (current : OuterPadded initial s state) :
    ∃ fuel t, Advances boundary fuel s t ∧ InnerCopied initial t state := by
  obtain ⟨fuel, t, setup, prepared⟩ := setup_inner pre current
  obtain ⟨u, run, result⟩ := run_inner pre prepared
  exact ⟨fuel + 13, u, setup.trans run, result⟩

end P256.Proofs.Nonce.UpdateValue.Prepare.Assemble
