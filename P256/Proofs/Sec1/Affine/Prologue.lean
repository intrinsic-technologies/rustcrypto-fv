import P256.Proofs.Sec1.EncodedPoint
import P256.Proofs.Program.SaveRegisters
import P256.Proofs.Program.ScalarFrame.Prologue
import P256.Proofs.Program.StackAllocate
import P256.Proofs.Program.State

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

abbrev savedMemory := saveMemory

abbrev saveComponents (s : RamState) := saveFrame s ++ [.flags]

abbrev Frame [Bindings] (initial s : RamState) :=
  ScalarFrame.FrameState initial s 80 3360 760

structure SavedEntry [Bindings] (initial s : RamState) (boundary : ReturnBoundary) : Prop where
  execution : Advances boundary 7 initial s
  ready : ReadyToStep s
  loaded : ProgramLoaded s
  rip : s.RIP = 0x1100e1
  rsp : stackPtr s = stackPtr initial - 760
  memory : s.external = savedMemory initial
  agrees : AgreesExcept (saveComponents initial) initial s

theorem prologue [Bindings] {s : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    (pre : AffineDecodePre s boundary bytes) : ∃ t, SavedEntry s t boundary := by
  obtain ⟨u, runU, readyU, loadedU, ripU, rspU, memoryU, agreesU⟩ :=
    save_registers pre.stack (pre.avoids _ (by simp)) pre.outerBoundary
      (readyToStep pre.machine pre.bindingsSupported) pre.loaded (by decide) pre.rip
      (codeOffset := 0x100d0) ⟨by decide, by decide +kernel, by decide +kernel,
        by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
  obtain ⟨t, runT, readyT, loadedT, ripT, rspT, memoryT, agreesT⟩ :=
    stack_allocate32 0x100da 712 readyU loadedU pre.outerBoundary
      ripU (by decide) (by decide +kernel)
  refine ⟨t, ⟨runU.trans runT, readyT, loadedT, ripT, ?_,
    memoryT.trans memoryU, (agreesU.trans agreesT).mono (by simp [saveComponents, saveFrame])⟩⟩
  rw [rspT, rspU, BitVec.sub_sub]
  rfl

theorem SavedEntry.frame [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} (pre : AffineDecodePre s boundary bytes)
    (entry : SavedEntry s t boundary) : Frame s t :=
  ScalarFrame.prologue_frame pre.toCalleePre (by decide) entry.ready entry.loaded entry.rsp
    entry.memory entry.agrees

end P256.Proofs.Sec1.Affine
