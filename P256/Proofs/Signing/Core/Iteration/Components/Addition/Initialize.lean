import P256.Proofs.Signing.Core.Iteration.Components.Addition.Memory
import P256.Proofs.Program.ScalarFrame.Prologue

set_option autoImplicit false

open P256.Proofs.Program

namespace P256.Proofs.Signing.Core.Iteration.Components.Addition

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem prologue_frame [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x113310 32 32 64)
    (ready : ReadyToStep t) (loaded : ProgramLoaded t)
    (rsp : stackPtr t = stackPtr s - 64)
    (memory : t.external = saveMemory s)
    (agrees : AgreesExcept (saveFrame s ++ [.reg 1, .flags]) s t) : FrameState s t := by
  refine ⟨bindingsSupported_of_ready_agrees pre.bindingsSupported ready agrees,
    supportedMachine_of_ready_agrees pre.machine ready agrees, loaded,
    agrees.directionFlagClear (by simp [saveFrame]) pre.directionFlag,
    agrees.grow, ?_, rsp, ?_, ?_, agrees.mxcsr (by simp [saveFrame]),
    agrees.fcw (by simp [saveFrame])⟩
  · intro a ha
    apply ScalarFrame.save_frame pre (by decide) agrees (by simp [Component.Covers]) a
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

end P256.Proofs.Signing.Core.Iteration.Components.Addition
