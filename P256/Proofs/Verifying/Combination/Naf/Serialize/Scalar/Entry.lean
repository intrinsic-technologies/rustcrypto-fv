import P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar.Prologue
import P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar.Cursor
import P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar.Memory


set_option autoImplicit false

open P256.Proofs.Program (memoryRegion_memReadable programText_slice programLoaded_codeIn
  readyToStep supportedMachine_of_ready_agrees inProgram_of_textOffset ScalarFrame.stack_contains stack_region_end)

namespace P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar

open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Proofs.Verifying.Combination.Naf

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.SecretKeyFromBytes.Scalar


theorem read_of_stack_frame {s t u : RamState} {addr : BitVec 64} {n : Nat}
    (frame : MemoryWriteFrame t u #v[Stack.region s 536])
    (bounded : addr.toNat + n/8 < 2^32)
    (apart : (⟨addr.toNat, n/8⟩ : MemoryRegion).Disjoint (Stack.region s 536)) :
    memLoad u.external addr n = memLoad t.external addr n := by
  apply memLoad_congr
  intro i hi
  change (u.external[addr + BitVec.ofNat 64 i]?).getD 0 =
    (t.external[addr + BitVec.ofNat 64 i]?).getD 0
  rw [frame _]
  intro region hr ha
  have hr' : region = Stack.region s 536 := by simpa using hr
  subst region
  apply apart _ ?_ ha
  change addr.toNat ≤ _ ∧ _ < addr.toNat + n/8
  rw [toNat_add_ofNat _ _ (by omega)]
  constructor <;> omega

theorem prologue_stack_frame [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {cursor point : BitVec 64} (pre : ScalarPre s boundary cursor point)
    (agrees : AgreesExcept (saveFrame s ++ [.flags]) s t) :
    MemoryWriteFrame s t #v[Stack.region s 536] := by
  apply agrees.memoryWriteFrame
  intro c hc a ha
  simp only [saveFrame, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with (rfl | rfl | rfl | rfl) | rfl
  all_goals try exact ha.elim
  all_goals exact ⟨_, by simp,
    P256.Proofs.Program.ScalarFrame.stack_contains pre.toCalleePre (by decide) (by decide) ha⟩

theorem cursor_readable [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {cursor point : BitVec 64} (pre : ScalarPre s boundary cursor point)
    (grow : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome) :
    P256.Proofs.Common.Instructions.CrossPageStore.Writable t cursor 8 := by
  have readable : MemReadable t cursor 8 :=
    readable_of_grow
      (memoryRegion_memReadable pre.cursorBounded pre.cursorAllocated (Nat.le_refl _) (Nat.le_refl _)) grow
  refine ⟨readable, ?_⟩
  apply tables_of_not_reserved (by decide) readable.low
  intro i hi hreserved
  apply pre.cursorAvoids (cursor + BitVec.ofNat 64 i) ?_ (.inr hreserved)
  have bound : cursor.toNat + 8 < 2^32 := pre.cursorBounded
  change cursor.toNat ≤ _ ∧ _ < cursor.toNat + 8
  rw [toNat_add_ofNat _ _ (by omega)]
  constructor <;> omega

theorem cursor_code [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {cursor point : BitVec 64} (pre : ScalarPre s boundary cursor point) :
    RangeApart cursor 8 0x10b17a 19 := by
  intro i hi j hj he
  apply pre.cursorAvoids (cursor + BitVec.ofNat 64 i) ?_ (.inl ?_)
  · have bound : cursor.toNat + 8 < 2^32 := pre.cursorBounded
    change cursor.toNat ≤ _ ∧ _ < cursor.toNat + 8
    rw [toNat_add_ofNat _ _ (by omega)]
    constructor <;> omega
  · rw [he]
    have h := inProgram_of_textOffset (0xb17a + j) (by omega)
    rw [BitVec.ofNat_add, ← BitVec.add_assoc] at h
    exact h

theorem cursor_stack_read [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {cursor point : BitVec 64} (pre : ScalarPre s boundary cursor point)
    (memory : MemoryWriteFrame t u #v[cursorRegion cursor])
    {off n : Nat} (ho : off ≤ 16) (hn : n/8 ≤ off+8) :
    memLoad u.external (stackPtr s - BitVec.ofNat 64 off) n =
      memLoad t.external (stackPtr s - BitVec.ofNat 64 off) n := by
  apply memLoad_congr
  intro i hi
  change (u.external[stackPtr s - BitVec.ofNat 64 off + BitVec.ofNat 64 i]?).getD 0 =
    (t.external[stackPtr s - BitVec.ofNat 64 off + BitVec.ofNat 64 i]?).getD 0
  rw [memory _]
  intro region hr ha
  have hr' : region = cursorRegion cursor := by simpa using hr
  subst region
  apply pre.cursorApart (Stack.region s 536) (by simp) _ ha
  have bounds := stack_bounds pre.stack
  have low := stack_sub_toNat pre.stack (offset := off) (by omega)
  change (stackPtr s).toNat - 536 ≤ _ ∧
    (stackPtr s - BitVec.ofNat 64 off + BitVec.ofNat 64 i).toNat <
      (Stack.region s 536).start + (Stack.region s 536).size
  rw [stack_region_end, toNat_add_ofNat _ _ (by rw [low]; omega), low]
  constructor <;> omega

theorem entry [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {cursor point : BitVec 64} (pre : ScalarPre s boundary cursor point) :
    ∃ fuel t, Advances boundary fuel s t ∧ Memory s t cursor point ∧
      t.RIP = 0x10b18d ∧ t.regValue .rbx = s.regValue .rdi ∧ t.regValue .rcx = point := by
  obtain ⟨u, run, state, rip, _, agrees⟩ := prologue pre
  have sm := prologue_stack_frame pre agrees
  have rsi : u.regValue .rsi = s.regValue .rsi := agrees.read (n := 64) (r := 6) (by simp [saveFrame])
  have rdi : u.regValue .rdi = s.regValue .rdi := agrees.read (n := 64) (r := 7) (by simp [saveFrame])
  have ca : cursorAddress u = cursor := by
    change memLoad u.external (u.regValue .rsi) 64 = cursor
    rw [rsi, read_of_stack_frame (addr := s.regValue .rsi) (n := 64) sm pre.inputBounded
      (pre.separation (0 : Fin 3) (2 : Fin 3) (by decide)), pre.cursorPointer]
  have pa : pointAddress u = point := by
    change memLoad u.external (cursorAddress u) 64 = point
    rw [ca, read_of_stack_frame (addr := cursor) (n := 64) sm pre.cursorBounded (pre.cursorApart _ (by simp)), pre.pointPointer]
  have cp : CursorPre u := by
    refine ⟨rip, ?_, ca ▸ cursor_readable pre state.allocated, ca ▸ cursor_code pre⟩
    rw [rsi]
    exact readable_of_grow
      (memoryRegion_memReadable pre.inputBounded pre.inputAllocated (Nat.le_refl _) (Nat.le_refl _)) state.allocated
  obtain ⟨fuel, t, run', ready, _, effect⟩ := cursor_correct boundary pre.outerBoundary u
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xb17a cursorBytes
      (by decide) (by decide +kernel)) cp
  have cm : MemoryWriteFrame u t #v[cursorRegion cursor] := by
    have ag : AgreesExcept [.reg 3, .reg 0, .reg 1, .reg 2,
        .mem (cursorAddress u) 8, .rip] u t := by
      simpa only [cursorEffect, Effect.components, List.map_cons, List.map_nil,
        Write.component, Operand.component, List.append_nil, List.cons_append,
        List.nil_append, Nat.reduceDiv] using effect.agrees
    rw [ca] at ag
    apply ag.memoryWriteFrame
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    refine ⟨cursorRegion cursor, by simp, ?_⟩
    obtain ⟨i, hi, rfl⟩ := ha
    have bound : cursor.toNat + 8 < 2^32 := pre.cursorBounded
    change cursor.toNat ≤ _ ∧ _ < cursor.toNat + 8
    rw [toNat_add_ofNat _ _ (by omega)]
    constructor <;> omega
  have cm' : MemoryWriteFrame u t
      #v[registerRegion s .rdi 272, cursorRegion cursor, Stack.region s 536] := by
    intro a ha
    apply cm a
    intro region hr hin
    have hr' : region = cursorRegion cursor := by simpa using hr
    exact ha _ (by simp [hr']) hin
  have total := memoryWriteFrame_trans state.frame cm'
  have sf : FrameState s t cursor := by
    refine ⟨bindingsSupported_of_ready_agrees state.bindingsSupported ready effect.agrees,
    supportedMachine_of_ready_agrees state.machine ready effect.agrees,
      loaded_of_frame pre total, effect.agrees.directionFlagClear (by component_not_mem) state.directionFlag,
      fun a ha => effect.agrees.grow a (state.allocated a ha), total,
      (effect.agrees.read (n := 64) (r := 4) (by simp [cursorEffect, Effect.components])).trans state.rsp,
      ?_, (effect.agrees.read (n := 64) (r := 5) (by simp [cursorEffect, Effect.components])).trans state.rbp,
      (effect.agrees.read (n := 64) (r := 12) (by simp [cursorEffect, Effect.components])).trans state.r12,
      (effect.agrees.read (n := 64) (r := 13) (by simp [cursorEffect, Effect.components])).trans state.r13,
      (effect.agrees.read (n := 64) (r := 15) (by simp [cursorEffect, Effect.components])).trans state.r15,
      ?_, (effect.agrees.mxcsr (by component_not_mem)).trans state.mxcsr,
      (effect.agrees.fcw (by component_not_mem)).trans state.fp87⟩
    · intro e he
      have bound : e.2 ≤ 16 := by
        simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl <;> decide
      exact (cursor_stack_read pre cm bound (by omega)).trans (state.saved e he)
    · have h := cursor_stack_read pre cm (off := 0) (n := 64) (by decide) (by decide)
      simp only [BitVec.sub_zero] at h
      exact h.trans state.returnAddress
  have values := effect.writes
  change t.regValue .rbx = u.regValue .rdi ∧ t.regValue .rax = cursorAddress u ∧
    t.regValue .rcx = pointAddress u ∧ t.regValue .rdx = pointAddress u + 128 ∧
    memLoad t.external (cursorAddress u) 64 = pointAddress u + 128 at values
  refine ⟨3 + fuel, t, run.trans run', ⟨sf, ?_⟩,
    effect.rip, values.1.trans rdi, values.2.2.1.trans pa⟩
  · rw [ca, pa] at values
    exact values.2.2.2.2

end P256.Proofs.Verifying.Combination.Naf.Serialize.Scalar
