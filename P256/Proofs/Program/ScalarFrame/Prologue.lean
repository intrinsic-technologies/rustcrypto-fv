import P256.Proofs.Program.ScalarFrame.Memory

set_option autoImplicit false

namespace P256.Proofs.Program.ScalarFrame

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

variable {entry stackOffset : BitVec 64} {inputBytes outputBytes stackReserve : Nat}

variable {inputRegister : Syntax.Reg}

theorem save_frame [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {cs : List Component} (pre : CalleePre s boundary entry inputBytes outputBytes stackReserve inputRegister)
    (hreserve : 48 ≤ stackReserve) (agrees : AgreesExcept (saveFrame s ++ cs) s t)
    (noMemory : ∀ c ∈ cs, ∀ a, ¬ c.Covers a) :
    MemoryWriteFrame s t #v[Stack.region s stackReserve] := by
  apply agrees.memoryWriteFrame
  intro c hc a hv
  simp only [List.mem_append] at hc
  rcases hc with hc | hc
  · simp only [saveFrame, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hv.elim
    all_goals refine ⟨Stack.region s stackReserve, by simp, ?_⟩
    · exact stack_contains pre (offset := 8) (by omega) (by decide) hv
    · exact stack_contains pre (offset := 16) (by omega) (by decide) hv
    · exact stack_contains pre (offset := 24) (by omega) (by decide) hv
    · exact stack_contains pre (offset := 32) (by omega) (by decide) hv
    · exact stack_contains pre (offset := 40) (by omega) (by decide) hv
    · exact stack_contains pre (offset := 48) (by omega) (by decide) hv
  · exact (noMemory c hc a hv).elim

theorem prologue_frame [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary entry inputBytes outputBytes stackReserve inputRegister)
    (hreserve : 48 ≤ stackReserve)
    (ready : ReadyToStep t) (loaded : ProgramLoaded t)
    (rsp : stackPtr t = stackPtr s - stackOffset) (memory : t.external = saveMemory s)
    (agrees : AgreesExcept (saveFrame s ++ [.flags]) s t) : FrameState s t outputBytes stackReserve stackOffset := by
  refine ⟨bindingsSupported_of_ready_agrees pre.bindingsSupported ready agrees,
    supportedMachine_of_ready_agrees pre.machine ready agrees, loaded,
    agrees.directionFlagClear (by simp [saveFrame]) pre.directionFlag,
    agrees.grow, ?_, rsp, ?_, ?_, agrees.mxcsr (by simp [saveFrame]),
    agrees.fcw (by simp [saveFrame])⟩
  · intro a ha
    apply save_frame pre hreserve agrees (by simp [Component.Covers]) a
    intro region member
    exact ha region (by simpa using Or.inr member)
  · intro entry he
    rw [memory]
    exact saveMemory_saved s entry he
  · change memLoad t.external (stackPtr s) 64 = memLoad s.external (stackPtr s) 64
    rw [memory]
    simp only [saveMemory, BitVec.sub_eq_add_neg]
    repeat rw [memLoad_memStore_apart_right _ _ _ _ 64
      (by unfold OffsetsApart; decide +kernel) (by decide) (by decide)]

end P256.Proofs.Program.ScalarFrame
