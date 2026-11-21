import P256.Proofs.Signing.Core.NextNonce.Memory
import P256.Proofs.Program.StackAllocate
import P256.Proofs.Program.ScalarFrame.Prologue

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Initialize

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program

theorem prologue [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : SignPre s boundary) :
    ∃ t, Advances boundary 7 s t ∧ Frame s t ∧ t.RIP = 0x10c9d1 ∧
      AgreesExcept (saveFrame s ++ [.flags]) s t := by
  obtain ⟨u, run, ready, loaded, rip, rsp, mem, ag⟩ := save_registers pre.stack
    (pre.avoids _ (by simp)) pre.outerBoundary
    (readyToStep pre.machine pre.bindingsSupported) pre.loaded (by decide)
    (codeOffset := 0xc9c0) pre.rip (by constructor <;> decide +kernel)
  obtain ⟨t, step, rt, lt, ip, sp, mt, agreed⟩ := stack_allocate32 0xc9ca 2232
    ready loaded pre.outerBoundary rip (by decide) (by decide +kernel)
  have sp' : stackPtr t = stackPtr s - 2280 := by
    rw [sp, rsp, BitVec.sub_sub]
    rfl
  have agrees : AgreesExcept (saveFrame s ++ [.flags]) s t := (ag.trans agreed).mono (by
    simp only [saveFrame, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    intro c hc
    rcases hc with h | (rfl | rfl | rfl)
    · exact Or.inl h
    all_goals simp)
  exact ⟨t, run.trans step,
    NextNonce.coreFrame (ScalarFrame.prologue_frame pre.toCalleePre (by decide) rt lt sp'
      (mt.trans mem) agrees), ip, agrees⟩

end P256.Proofs.Signing.Core.Initialize
