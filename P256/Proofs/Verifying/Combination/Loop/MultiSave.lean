import P256.Proofs.Verifying.Combination.Loop.MultiEntry
import P256.Proofs.Program.WrapperMemory
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Loop.Multi

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem save_count [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {tables digits : BitVec 64}
    (pre : MultiPre s boundary tables digits)
    (state : State s t) (rip : t.RIP = 0x10eff2) :
    ∃ u, Advances boundary 1 t u ∧ State s u ∧ u.RIP = 0x10eff7 ∧
      (Operand.mem (stackPtr s - 400) : Operand 64).read u = t.regValue .rcx ∧
      AgreesExcept [.mem (stackPtr s - 400) 8, .rip] t u := by
  let am : AddrMode := .sib 4 none 0 (.d8 8)
  have address : storeAddrAt 0x10eff2 am 5 t = stackPtr s - 400 :=
    scalar_stack_address state.rsp (offset := 8) (by decide) (by decide)
  have writable : MemWritable t (stackPtr s - 400) 8 :=
    writable_of_grow (stack_sub_writable8 pre.stack
      (fun a ha hp => pre.avoids (Stack.region s 1432) (by simp) a ha (.inr hp)) (offset := 400) (by decide) (by decide)) state.allocated
  obtain ⟨u, run, ready, effect⟩ :=
    (mov_m64_r64_effect_step 0x10eff2 0x48 (by simp [RexWPrefix]) 1 am
      (by constructor <;> decide +kernel) rfl rfl).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0xeff2 _ (by decide) (by decide +kernel))
      ⟨rip, address ▸ writable, address ▸
        (by
          have h := stack_code pre.toCalleePre state (offset := 8) (len := 8)
            (codeOffset := 0xeff2) (codeLen := 5) (by decide) (by decide) (by decide)
          rw [scalar_stack_address state.rsp (offset := 8) (by decide) (by decide)] at h
          exact h)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xeff7 (by decide)))
  have agrees : AgreesExcept [.mem (stackPtr s - 400) 8, .rip] t u := by
    have h := effect.agrees
    rw [movM64R64Effect_components] at h
    change AgreesExcept [.mem (storeAddrAt 0x10eff2 am 5 t) 8, .rip] t u at h
    rwa [address] at h
  refine ⟨u, run, FrameState.after_effect pre.toCalleePre (by decide) state ready agrees ?_ (by simp), effect.rip, ?_, agrees⟩
  · intro c hc a covered
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ⟨_, by simp, work_contains pre.toCalleePre (offset := 400) (by decide) (by decide) covered⟩
    · exact covered.elim
  · have h := effect.writes
    change (Operand.mem (storeAddrAt 0x10eff2 am 5 t) : Operand 64).read u = t.regValue .rcx at h
    rwa [address] at h

theorem save_output_pointer [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {tables digits : BitVec 64}
    (pre : MultiPre s boundary tables digits)
    (state : State s t) (rip : t.RIP = 0x10eff7) :
    ∃ u, Advances boundary 1 t u ∧ State s u ∧ u.RIP = 0x10effc ∧
      (Operand.mem (stackPtr s - 392) : Operand 64).read u = t.regValue .rdi ∧
      AgreesExcept [.mem (stackPtr s - 392) 8, .rip] t u := by
  let am : AddrMode := .sib 4 none 0 (.d8 16)
  have address : storeAddrAt 0x10eff7 am 5 t = stackPtr s - 392 :=
    scalar_stack_address state.rsp (offset := 16) (by decide) (by decide)
  have writable : MemWritable t (stackPtr s - 392) 8 :=
    writable_of_grow (stack_sub_writable8 pre.stack
      (fun a ha hp => pre.avoids (Stack.region s 1432) (by simp) a ha (.inr hp)) (offset := 392) (by decide) (by decide)) state.allocated
  obtain ⟨u, run, ready, effect⟩ :=
    (mov_m64_r64_effect_step 0x10eff7 0x48 (by simp [RexWPrefix]) 7 am
      (by constructor <;> decide +kernel) rfl rfl).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0xeff7 _ (by decide) (by decide +kernel))
      ⟨rip, address ▸ writable, address ▸
        (by
          have h := stack_code pre.toCalleePre state (offset := 16) (len := 8)
            (codeOffset := 0xeff7) (codeLen := 5) (by decide) (by decide) (by decide)
          rw [scalar_stack_address state.rsp (offset := 16) (by decide) (by decide)] at h
          exact h)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xeffc (by decide)))
  have agrees : AgreesExcept [.mem (stackPtr s - 392) 8, .rip] t u := by
    have h := effect.agrees
    rw [movM64R64Effect_components] at h
    change AgreesExcept [.mem (storeAddrAt 0x10eff7 am 5 t) 8, .rip] t u at h
    rwa [address] at h
  refine ⟨u, run, FrameState.after_effect pre.toCalleePre (by decide) state ready agrees ?_ (by simp), effect.rip, ?_, agrees⟩
  · intro c hc a covered
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ⟨_, by simp, work_contains pre.toCalleePre (offset := 392) (by decide) (by decide) covered⟩
    · exact covered.elim
  · have h := effect.writes
    change (Operand.mem (storeAddrAt 0x10eff7 am 5 t) : Operand 64).read u = t.regValue .rdi at h
    rwa [address] at h

theorem nonempty_branch [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {tables digits : BitVec 64} (pre : MultiPre s boundary tables digits)
    (state : State s t) (rip : t.RIP = 0x10effc)
    (cf : (StatusFlags.ofRFLAGS t.RFLAGS).CF = false)
    (zf : (StatusFlags.ofRFLAGS t.RFLAGS).ZF = false) :
    ∃ w, Advances boundary 1 t w ∧ State s w ∧ w.RIP = 0x10effe ∧
      AgreesExcept [.rip] t w := by
  have next : (jccEffect 0x10effc 2 6 ((0x37 : BitVec 8).signExtend 64) t).rip = 0x10effe := by
    simp only [jccEffect, branchEffect, condHolds, cf, zf]
    rfl
  obtain ⟨w, run, ready, effect⟩ :=
    (jcc_rel8_effect_step 0x10effc 6 0x37).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0xeffc _
        (by decide) (by decide +kernel))
      ⟨rip, by intro h; decide +kernel⟩
      (by
        rw [next]
        exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xeffe (by decide)))
  have agrees : AgreesExcept [.rip] t w := effect.agrees
  exact ⟨w, run, state.after_registers ready agrees (by simp [Component.Covers])
    (by simp), effect.rip.trans next, agrees⟩

theorem entry [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {tables digits : BitVec 64} (pre : MultiPre s boundary tables digits) :
    ∃ t, Advances boundary 15 s t ∧ State s t ∧ t.RIP = 0x10effe ∧
      t.regValue .rax = s.regValue .rsi ∧ t.regValue .rdx = 0 ∧ t.regValue .rsi = 2 ∧
      memLoad t.external (stackPtr s - 400) 64 = 2 ∧
      memLoad t.external (stackPtr s - 392) 64 = s.regValue .rdi := by
  obtain ⟨a, runA, stateA, ripA, frameA⟩ := prologue pre
  obtain ⟨b, runB, stateB, ripB, axB, dxB, siB, frameB⟩ :=
    read_indices pre stateA ripA (frameA.read (n := 64) (r := 6) (by simp [saveFrame]))
  obtain ⟨c, runC, stateC, ripC, countC, cfC, zfC, frameC⟩ :=
    compute_count pre stateB ripB dxB siB
  obtain ⟨d, runD, stateD, ripD, countD, frameD⟩ := save_count pre stateC ripC
  obtain ⟨e, runE, stateE, ripE, outputE, frameE⟩ := save_output_pointer pre stateD ripD
  have flags : StatusFlags.ofRFLAGS e.RFLAGS = StatusFlags.ofRFLAGS c.RFLAGS :=
    (frameE.statusFlags (by simp)).trans (frameD.statusFlags (by simp))
  obtain ⟨t, runT, stateT, ripT, frameT⟩ := nonempty_branch pre stateE ripE
    (by rw [flags]; exact cfC) (by rw [flags]; exact zfC)
  have stable : AgreesExcept [.mem (stackPtr s - 400) 8, .mem (stackPtr s - 392) 8, .rip] c t :=
    ((frameD.trans frameE).trans frameT).mono (by simp)
  refine ⟨t, ((((runA.trans runB).trans runC).trans runD).trans runE).trans runT,
    stateT, ripT, ?_, ?_, ?_, ?_, ?_⟩
  · exact (stable.read (n := 64) (r := 0) (by simp)).trans
      ((frameC.read (n := 64) (r := 0) (by simp)).trans axB)
  · exact (stable.read (n := 64) (r := 2) (by simp)).trans
      ((frameC.read (n := 64) (r := 2) (by simp)).trans dxB)
  · exact (stable.read (n := 64) (r := 6) (by simp)).trans
      ((frameC.read (n := 64) (r := 6) (by simp)).trans siB)
  · rw [frameT.external (by simp [Component.Covers])]
    have memory : memLoad e.external (stackPtr s - 400) 64 =
        memLoad d.external (stackPtr s - 400) 64 := by
      apply memLoad_congr
      intro i hi
      apply congrArg (fun x : Option UInt8 => x.getD 0)
      apply frameE.byte
      intro component hc covered
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · obtain ⟨j, hj, eq⟩ := covered
        exact stack_sub_apart pre.stack (by decide) (by decide)
          (by decide) (by decide) (Or.inr (by decide)) j hj i hi eq.symm
      · exact covered.elim
    exact memory.trans (countD.trans countC)
  · rw [frameT.external (by simp [Component.Covers])]
    exact outputE.trans ((frameD.read (n := 64) (r := 7) (by simp)).trans
      ((frameC.read (n := 64) (r := 7) (by simp)).trans
      ((frameB.read (n := 64) (r := 7) (by simp)).trans
      (frameA.read (n := 64) (r := 7) (by simp [saveFrame])))))

end P256.Proofs.Verifying.Combination.Loop.Multi
