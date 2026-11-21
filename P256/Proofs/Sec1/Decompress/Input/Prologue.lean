import P256.Proofs.Sec1.Decompress.State
import P256.Proofs.Program.ScalarFrame.Prologue
import P256.Proofs.Program.StackAllocate

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decompress.Input

open P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem prologue [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} {odd : Bool} (pre : Pre s boundary bytes odd) :
    ∃ t, Advances boundary 7 s t ∧ Frame s t ∧ t.RIP = 0x10fc11 ∧
      AgreesExcept (saveFrame s ++ [.flags]) s t := by
  obtain ⟨u, runU, readyU, loadedU, ripU, rspU, memoryU, agreesU⟩ :=
    save_registers pre.stack (pre.avoids _ (by simp)) pre.outerBoundary
      (readyToStep pre.machine pre.bindingsSupported) pre.loaded (by decide) pre.rip
      (codeOffset := 0xfc00) ⟨by decide, by decide +kernel, by decide +kernel,
        by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
  obtain ⟨t, runT, readyT, loadedT, ripT, rspT, memoryT, agreesT⟩ :=
    stack_allocate32 0xfc0a 360 readyU loadedU pre.outerBoundary
      ripU (by decide) (by decide +kernel)
  have rsp : stackPtr t = stackPtr s - 408 := by
    rw [rspT, rspU, BitVec.sub_sub]
    rfl
  have agrees : AgreesExcept (saveFrame s ++ [.flags]) s t :=
    (agreesU.trans agreesT).mono (by simp [saveFrame])
  exact ⟨t, runU.trans runT,
    ScalarFrame.prologue_frame pre.toCalleePre (by decide) readyT loadedT rsp
      (memoryT.trans memoryU) agrees, ripT, agrees⟩

end P256.Proofs.Sec1.Decompress.Input
