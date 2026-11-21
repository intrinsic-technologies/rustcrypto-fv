import P256.Proofs.Verifying.Combination.Naf.Interface
import P256.Proofs.Verifying.Combination.Naf.Machine.Prologue
import P256.Proofs.Verifying.Combination.Naf.Machine.Setup

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Machine

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar

structure EntryState [Bindings] (s t : RamState) : Prop extends FrameState s t where
  rip : t.RIP = 0x10f385
  r12 : t.regValue .r12 = 5
  r13 : t.regValue .r13 = 256
  rax : t.regValue .rax = 32
  r15 : t.regValue .r15 = 257
  rbx : t.regValue .rbx = 32
  rcx : t.regValue .rcx = 5
  rdi : t.regValue .rdi = stackPtr s - 88
  rsi : t.regValue .rsi = s.regValue .rdx
  rdx : t.regValue .rdx = 32
  outputPointer : memLoad t.external (stackPtr s - 120) 64 = s.regValue .rdi

theorem entry [Bindings] {s : RamState} {boundary : ReturnBoundary} (pre : Pre s boundary) :
    ∃ fuel t, Advances boundary fuel s t ∧ EntryState s t ∧
      MemoryWriteFrame s t #v[Stack.region s 168] := by
  obtain ⟨u, run0, state0, rip0, ag0⟩ := prologue_frame pre
  have setupPre : SetupPre u := ⟨rip0,
    stack_writable pre.toCalleePre state0 (by decide) (by decide),
    stack_code pre.toCalleePre state0 (offset := 16) (len := 8)
      (codeOffset := 0xf35e) (codeLen := 39) (by decide) (by decide)⟩
  obtain ⟨fuel, t, run, ready, _, effect⟩ := setup_block boundary pre.outerBoundary u
    (readyToStep state0.machine state0.bindingsSupported)
    (programText_slice (programLoaded_codeIn state0.loaded) 0xf35e setupBytes
      (by decide) (by decide +kernel)) setupPre
  have writes : WritesWithin (setupEffect u).components
      #v[registerRegion s .rdi 257, workRegion s] := by
    intro c hc a cover
    simp only [setupEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact cover.elim
    refine ⟨workRegion s, by simp, work_contains pre.toCalleePre (offset := 120) (len := 8) (by decide) (by decide) ?_⟩
    have addr : (Operand.reg 4 : Operand 64).read u + 16 = stackPtr s - 120 :=
      stack_address state0.rsp (offset := 16) (by decide)
    rwa [addr] at cover
  have state := after pre.toCalleePre state0 ready effect.agrees writes
    (by simp [setupEffect, Effect.components])
  have regs (r : BitVec 5) (hr : r ≠ 4#5) :
      (Operand.reg r : Operand 64).read u = (Operand.reg r : Operand 64).read s :=
    ag0.read (by simp [prologueComponents, P256.Proofs.Program.saveFrame, hr])
  have r9 : u.regValue .r9 = 5 := (regs 9 (by decide)).trans pre.window
  have r8 : u.regValue .r8 = 256 := (regs 8 (by decide)).trans pre.inputBits
  have rcx : u.regValue .rcx = 32 := (regs 1 (by decide)).trans pre.inputLength
  have rsi : u.regValue .rsi = 257 := (regs 6 (by decide)).trans pre.outputLength
  have rdi : u.regValue .rdi = s.regValue .rdi := regs 7 (by decide)
  have rdx : u.regValue .rdx = s.regValue .rdx := regs 2 (by decide)
  have hw := effect.writes
  change t.regValue .r12 = u.regValue .r9 ∧ t.regValue .r13 = u.regValue .r8 ∧
    t.regValue .rax = u.regValue .rcx ∧ t.regValue .r15 = u.regValue .rsi ∧
    memLoad t.external (stackPtr u + 16#64) 64 = u.regValue .rdi ∧
    t.regValue .rbx = (1#64) <<< shiftCount 64 ((u.regValue .r9).setWidth 8) ∧
    t.regValue .rcx = ((u.regValue .r9).setWidth 32).setWidth 64 ∧
    t.regValue .rdi = stackPtr u + 48#64 ∧ t.regValue .rsi = u.regValue .rdx ∧
    t.regValue .rdx = u.regValue .rcx at hw
  rw [r9, r8, rcx, rsi, rdi, rdx] at hw
  have ptr16 := stack_address state0.rsp (offset := 16) (by decide)
  have ptr48 := stack_address state0.rsp (offset := 48) (by decide)
  rw [ptr16, ptr48] at hw
  have total := ag0.trans effect.agrees
  refine ⟨7+fuel, t, run0.trans run,
    ⟨state, effect.rip, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1,
      hw.2.2.2.2.2.1, hw.2.2.2.2.2.2.1, hw.2.2.2.2.2.2.2.1,
      hw.2.2.2.2.2.2.2.2.1, hw.2.2.2.2.2.2.2.2.2, hw.2.2.2.2.1⟩, ?_⟩
  apply total.memoryWriteFrame
  intro c hc a cover
  simp only [List.mem_append] at hc
  rcases hc with hc | hc
  · simp only [prologueComponents, P256.Proofs.Program.saveFrame,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    all_goals try exact cover.elim
    all_goals exact ⟨_, by simp,
      ScalarFrame.stack_contains pre.toCalleePre (by decide) (by decide) cover⟩
  · obtain ⟨region, hr, hin⟩ := writes c hc a cover
    have hr' : region = registerRegion s .rdi 257 ∨ region = workRegion s := by simpa using hr
    rcases hr' with rfl | rfl
    · simp only [setupEffect, Effect.components, List.map_cons, List.map_nil,
        Write.component, Operand.component, List.cons_append, List.nil_append,
        List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals try exact cover.elim
      refine ⟨Stack.region s 168, by simp, ?_⟩
      change (Component.mem (stackPtr u + 16#64) 8).Covers a at cover
      rw [ptr16] at cover
      exact ScalarFrame.stack_contains pre.toCalleePre (by decide) (by decide) cover
    · refine ⟨Stack.region s 168, by simp, ?_⟩
      have bounds := P256.Proofs.Program.stack_bounds pre.stack
      change (stackPtr s).toNat-168 ≤ a.toNat ∧ a.toNat < (stackPtr s).toNat-168+120 at hin
      change (stackPtr s).toNat-168 ≤ a.toNat ∧ a.toNat < (Stack.region s 168).start + (Stack.region s 168).size
      rw [stack_region_end]
      constructor <;> omega

end P256.Proofs.Verifying.Combination.Naf.Machine
