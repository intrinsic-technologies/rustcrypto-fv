import P256.Proofs.Verifying.Combination.Loop.MultiEntry
import P256.Proofs.Program.WrapperMemory
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Loop.Multi

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem save_digit_cursor [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {tables digits : BitVec 64}
    (pre : MultiPre s boundary tables digits)
    (state : State s t) (rip : t.RIP = 0x10f1ad) :
    ∃ u, Advances boundary 1 t u ∧ State s u ∧ u.RIP = 0x10f1b2 ∧
      (Operand.mem (stackPtr s - 376) : Operand 64).read u = t.regValue .r13 ∧
      AgreesExcept [.mem (stackPtr s - 376) 8, .rip] t u := by
  let am : AddrMode := .sib 4 none 0 (.d8 32)
  have address : storeAddrAt 0x10f1ad am 5 t = stackPtr s - 376 :=
    scalar_stack_address state.rsp (offset := 32) (by decide) (by decide)
  have writable : MemWritable t (stackPtr s - 376) 8 :=
    writable_of_grow (stack_sub_writable8 pre.stack
      (fun a ha hp => pre.avoids (Stack.region s 1432) (by simp) a ha (.inr hp)) (offset := 376) (by decide) (by decide)) state.allocated
  obtain ⟨u, run, ready, effect⟩ :=
    (mov_m64_r64_effect_step 0x10f1ad 0x4c (by simp [RexWPrefix]) 5 am
      (by constructor <;> decide +kernel) rfl rfl).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0xf1ad _ (by decide) (by decide +kernel))
      ⟨rip, address ▸ writable, address ▸
        (by
          have h := stack_code pre.toCalleePre state (offset := 32) (len := 8)
            (codeOffset := 0xf1ad) (codeLen := 5) (by decide) (by decide) (by decide)
          rw [scalar_stack_address state.rsp (offset := 32) (by decide) (by decide)] at h
          exact h)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf1b2 (by decide)))
  have agrees : AgreesExcept [.mem (stackPtr s - 376) 8, .rip] t u := by
    have h := effect.agrees
    rw [movM64R64Effect_components] at h
    change AgreesExcept [.mem (storeAddrAt 0x10f1ad am 5 t) 8, .rip] t u at h
    rwa [address] at h
  refine ⟨u, run, FrameState.after_effect pre.toCalleePre (by decide) state ready agrees ?_ (by simp), effect.rip, ?_, agrees⟩
  · intro c hc a covered
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ⟨_, by simp, work_contains pre.toCalleePre (offset := 376) (by decide) (by decide) covered⟩
    · exact covered.elim
  · have h := effect.writes
    change (Operand.mem (storeAddrAt 0x10f1ad am 5 t) : Operand 64).read u = t.regValue .r13 at h
    rwa [address] at h

end P256.Proofs.Verifying.Combination.Loop.Multi
