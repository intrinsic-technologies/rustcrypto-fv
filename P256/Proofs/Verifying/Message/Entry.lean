import P256.Proofs.Verifying.Message.Interface
import P256.Proofs.Program.StackAllocate
import P256.Proofs.Program.ScalarFrame.Prologue

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message

open P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem entry [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10d570 72 24 9992) :
    ∃ t, Advances boundary 7 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = 0x10d581 ∧ stackPtr t = stackPtr s - 1176 ∧
      t.external = saveMemory s ∧ AgreesExcept (saveFrame s ++ [.flags]) s t := by
  obtain ⟨u, run, ready, loaded, rip, rsp, memory, agrees⟩ :=
    save_registers (codeOffset := 0xd570) pre.stack (pre.avoids _ (by simp))
      pre.outerBoundary (readyToStep pre.machine pre.bindingsSupported) pre.loaded
      (by decide) pre.rip (by constructor <;> decide +kernel)
  obtain ⟨t, allocate, readyT, loadedT, ripT, rspT, memoryT, frameT⟩ :=
    stack_allocate32 0xd57a 1128 ready loaded pre.outerBoundary rip
      (by decide) (by decide +kernel)
  refine ⟨t, run.trans allocate, readyT, loadedT, ripT, ?_, memoryT.trans memory, ?_⟩
  · rw [rspT, rsp, BitVec.sub_sub]
    rfl
  · apply (agrees.trans frameT).mono
    intro c hc
    simp only [List.mem_append] at hc
    rcases hc with h | h
    · exact List.mem_append.mpr (.inl h)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl <;> simp [saveFrame]

theorem entry_frame [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10d570 72 24 9992) :
    ∃ t, Advances boundary 7 s t ∧ Frame s t ∧ t.RIP = 0x10d581 ∧
      AgreesExcept (saveFrame s ++ [.flags]) s t := by
  obtain ⟨t, run, ready, loaded, rip, rsp, memory, agrees⟩ := entry pre
  exact ⟨t, run, ScalarFrame.prologue_frame pre (by decide)
    ready loaded rsp memory agrees, rip, agrees⟩

end P256.Proofs.Verifying.Message
