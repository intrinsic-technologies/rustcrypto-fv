import P256.Proofs.Program.SaveRegisters
import P256.Proofs.Program.StackAllocate
import P256.Proofs.Program.ScalarFrame.Prologue

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Loop

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program

theorem loop_prologue [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x103250 768 96 1400) :
    ∃ t, Advances boundary 7 s t ∧
      ScalarFrame.FrameState s t 96 1400 376 ∧ t.RIP = 0x103261 ∧
      t.external = saveMemory s ∧ AgreesExcept (saveFrame s ++ [.flags]) s t := by
  obtain ⟨u, run, ready, loaded, rip, rsp, memory, agrees⟩ :=
    save_registers pre.stack (pre.avoids (Stack.region s 1400) (by simp))
      pre.outerBoundary (readyToStep pre.machine pre.bindingsSupported) pre.loaded
      (by decide) (codeOffset := 0x3250) pre.rip (by constructor <;> decide +kernel)
  obtain ⟨t, step, readyT, loadedT, ripT, rspT, memoryT, agreesT⟩ :=
    stack_allocate32 0x325a 328 ready loaded pre.outerBoundary rip
      (by decide) (by decide +kernel)
  have stack : stackPtr t = stackPtr s - 376 := by
    rw [rspT, rsp, BitVec.sub_sub]
    rfl
  have mem : t.external = saveMemory s := memoryT.trans memory
  have frame : AgreesExcept (saveFrame s ++ [.flags]) s t := by
    apply (agrees.trans agreesT).mono
    intro c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with hc | (rfl | rfl | rfl)
    · exact List.mem_append_left _ hc
    · simp [saveFrame]
    · simp
    · simp [saveFrame]
  exact ⟨t, run.trans step, ScalarFrame.prologue_frame pre (by decide)
    readyT loadedT stack mem frame, ripT, mem, frame⟩

end P256.Proofs.Projective.Multiply.Machine.Loop
