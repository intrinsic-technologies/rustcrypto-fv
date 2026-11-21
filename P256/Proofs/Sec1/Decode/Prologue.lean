import P256.Proofs.Sec1.Interface
import P256.Proofs.Program.PushSequence
import P256.Proofs.Program.StackAllocate
import P256.Proofs.Program.State

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decode

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def savedRegisters : List (BitVec 4) := [15, 14, 12, 3]

def savedMemory (s : RamState) : Ram := pushSequenceMemory s s.external 0 savedRegisters

def saveComponents (s : RamState) : List Component :=
  pushSequenceFrame s 0 savedRegisters ++ [.reg 4, .flags, .rip]

structure SavedEntry [Bindings] (initial s : RamState) (boundary : ReturnBoundary) : Prop where
  execution : Advances boundary 5 initial s
  ready : ReadyToStep s
  loaded : ProgramLoaded s
  rip : s.RIP = 0x10e4ee
  rsp : stackPtr s = stackPtr initial - 312
  memory : s.external = savedMemory initial
  agrees : AgreesExcept (saveComponents initial) initial s

theorem prologue [Bindings] {s : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    (pre : DecodePre s boundary bytes) : ∃ t, SavedEntry s t boundary := by
  obtain ⟨u, runU, readyU, loadedU, ripU, rspU, memoryU, agreesU⟩ :=
    push_sequence savedRegisters pre.stack (pre.avoids _ (by simp)) pre.outerBoundary
      (readyToStep pre.machine pre.bindingsSupported) pre.loaded (fun _ ha ↦ ha)
      (offset := 0) (codeOffset := 0xe4e0) (by simp) pre.rip
      (by decide) (by decide) (by decide) (fun _ _ ↦ rfl)
      (by simp only [savedRegisters, PushSequenceCode]; decide +kernel)
  obtain ⟨t, runT, readyT, loadedT, ripT, rspT, memoryT, agreesT⟩ :=
    stack_allocate32 0xe4e7 280 readyU loadedU pre.outerBoundary
      ripU (by decide) (by decide +kernel)
  refine ⟨t, ⟨runU.trans runT, readyT, loadedT, ripT, ?_,
    memoryT.trans memoryU, agreesU.trans agreesT⟩⟩
  rw [rspT, rspU, BitVec.sub_sub]
  rfl

end P256.Proofs.Sec1.Decode
