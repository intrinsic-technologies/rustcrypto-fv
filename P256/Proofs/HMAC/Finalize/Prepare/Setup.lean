import P256.Proofs.HMAC.Interface
import P256.Proofs.HMAC.Finalize.PrologueFrame
import P256.Proofs.HMAC.Finalize.OuterSetup
import P256.Proofs.HMAC.Finalize.Frame

set_option autoImplicit false

namespace P256.Proofs.HMAC.Finalize.Prepare

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Program.ScalarFrame (workRegion)
open P256.Proofs.Common
open P256.Proofs.Program (saveFrame)

structure Initialized [Bindings] (initial s : RamState) (key input : ByteArray) : Prop
    extends ScalarFrame.FrameState initial s 0 672 328 where
  rip : s.RIP = 0x100f96
  outputPointer : s.regValue .rbx = initial.regValue .rsi
  sourcePointer : s.regValue .r15 = initial.regValue .rdi
  inputPointer : s.regValue .rsi = initial.regValue .rdi
  hashPointer : s.regValue .rdi = stackPtr initial - 88#64
  countRegister : s.regValue .rdx = 1
  state : HmacStateAt s (initial.regValue .rdi) key input
  hash : SHA256.HashStateAt s (stackPtr initial - 88#64) P256.Proofs.SHA256.initialHash
  position : s.external[stackPtr initial - 89#64]? = some 0
  count : loadBytes s.external (stackPtr initial - 56#64) 8 = .ok 1

theorem setup_writes [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    (pre : HashCalleePre initial boundary 0x100f10 168 672)
    (state : ScalarFrame.FrameState initial s 0 672 328) :
    WritesWithin (outerSetupEffect s).components #v[workRegion initial 672] := by
  intro c hc a covered
  simp only [outerSetupEffect, Effect.components, Write.component, List.map_cons,
    List.map_nil, List.append_nil, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, Operand.component] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
  all_goals try exact covered.elim
  all_goals exact ⟨_, by simp, local_work_contains pre state.rsp (by decide) covered⟩

theorem setup [Bindings] {initial : RamState} {boundary : ReturnBoundary}
    {key input : ByteArray} (pre : HmacFinalizePre initial boundary key input) :
    ∃ fuel s, Advances boundary fuel initial s ∧ Initialized initial s key input := by
  obtain ⟨a, runA, frameA, ripA, agreesA⟩ := prologue_frame pre.toHashCalleePre
  have rdiA : a.regValue .rdi = initial.regValue .rdi :=
    agreesA.read (n := 64) (r := 7) (by simp [saveFrame])
  have rsiA : a.regValue .rsi = initial.regValue .rsi :=
    agreesA.read (n := 64) (r := 6) (by simp [saveFrame])
  have stateA : HmacStateAt a (initial.regValue .rdi) key input := by
    apply pre.state.copy
    intro i hi
    apply agreesA.byte
    intro c hc covered
    have within := memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) hi
    apply pre.separation 1 2 (by decide) _ within
    simp only [saveFrame, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    all_goals try exact covered.elim
    all_goals exact ScalarFrame.stack_contains pre.toCalleePre (by decide) (by decide) covered
  have hp := outer_setup_pre pre.toHashCalleePre frameA ripA
  obtain ⟨fuel, s, runS, readyS, _, effectS⟩ :=
    outer_setup_correct boundary pre.outerBoundary a (readyToStep frameA.machine frameA.bindingsSupported)
      (outer_setup_code frameA.loaded) hp
  have writes := setup_writes pre.toHashCalleePre frameA
  have memory := effectS.agrees.memoryWriteFrame writes
  have frameS : ScalarFrame.FrameState initial s 0 672 328 := by
    apply frameA.after_effect (stackPre pre.toHashCalleePre) (by decide) readyS effectS.agrees
    · intro c hc a covered
      obtain ⟨region, member, contains⟩ := writes c hc a covered
      have eq : region = workRegion initial 672 := by simpa using member
      exact ⟨_, by simp [eq], contains⟩
    · simp [outerSetupEffect, Effect.components]
  have fields := effectS.writes
  simp only [outerSetupEffect, Write.AllHold, Operand.read] at fields
  refine ⟨7 + fuel, s, runA.trans runS, frameS, effectS.rip,
    fields.1.trans rsiA, fields.2.1.trans rdiA,
    fields.2.2.2.2.2.2.2.2.2.2.2.2.trans rdiA, ?_,
    fields.2.2.2.2.2.2.2.2.2.2.1,
    state_of_work_frame pre.toHashCalleePre stateA memory, ?_, ?_, ?_⟩
  · exact fields.2.2.2.2.2.2.2.2.2.2.2.1.trans
      (stack_address frameA.rsp (by decide : 240 ≤ 328))
  · have eq : stackPtr a + 240 = stackPtr initial - 88#64 := stack_address frameA.rsp (by decide : 240 ≤ 328)
    simpa only [eq] using outer_setup_hash hp effectS
  · have eq : stackPtr a + 239 = stackPtr initial - 89#64 := stack_address frameA.rsp (by decide : 239 ≤ 328)
    simpa only [eq] using outer_setup_position hp effectS
  · have eq : stackPtr a + 272 = stackPtr initial - 56#64 := stack_address frameA.rsp (by decide : 272 ≤ 328)
    simpa only [eq] using outer_setup_count hp effectS

end P256.Proofs.HMAC.Finalize.Prepare
