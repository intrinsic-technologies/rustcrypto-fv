import P256.Proofs.Signing.Core.Iteration.Components.Addition.Memory
import X86Proofs.Instructions.Mov.Triple
import P256.Proofs.Common.Encoding.Serialize.Tail.ByteOps.Store
import X86Proofs.Instructions.Movs.Execution
import X86Proofs.Instructions.Test.Generated.RR.Triple
import X86Proofs.Instructions.Dec.Generated.R.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple
import P256.Proofs.Common.Instructions.Setb.Triple
import P256.Proofs.Common.Instructions.ByteLogic.AndReg
import P256.Proofs.Common.Instructions.AddByte.Memory.Stack
import P256.Proofs.Common.Instructions.Sar.Triple
import P256.Proofs.Common.Instructions.Carry

set_option autoImplicit false

open P256.Proofs.Program

open P256.Proofs.Program (CalleePre boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice)

namespace P256.Proofs.Signing.Core.Iteration.Components.Addition.Choice

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def frame (s : RamState) : List Component :=
  [.reg 0, .reg 1, .reg 7, .flags, .rip,
    .mem (stackPtr s) 1, .mem (stackPtr s) 8, .mem (stackPtr s + 15) 1]

theorem writes [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x113310 32 32 64) (state : FrameState s t) :
    WritesWithin (frame t) #v[registerRegion s .rdi 32, workRegion s] := by
  intro c hc a ha
  simp only [frame, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  all_goals refine ⟨workRegion s, by simp, ?_⟩
  · rw [state.rsp] at ha
    exact work_contains pre (by decide) (by decide) ha
  · rw [state.rsp] at ha
    exact work_contains pre (by decide) (by decide) ha
  · change (Component.mem (stackPtr t + BitVec.ofNat 64 15) 1).Covers a at ha
    rw [scalar_stack_address state.rsp (offset := 15) (by decide)] at ha
    exact work_contains pre (by decide) (by decide) ha

theorem step [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {P : RamState → Prop} {E : RamState → Effect} {offset : Nat} {bytes : List UInt8}
    (pre : CalleePre s boundary 0x113310 32 32 64) (state : FrameState s t)
    (instruction : StepEffect P (codeRange (Extracted.textAddress + BitVec.ofNat 64 offset) bytes) E)
    (size : offset + bytes.length ≤ 118431)
    (code : Extracted.textBytes.toListFrom offset bytes.length = bytes)
    (hp : P t) (next : InProgram (E t).rip) (within : (E t).components ⊆ frame t) :
    ∃ u, Advances boundary 1 t u ∧ FrameState s u ∧ (E t).Holds t u := by
  obtain ⟨u,run,ready,effect⟩ := instruction.advances
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) offset bytes size code)
    hp (boundary_ne_program pre.outerBoundary next)
  have agrees := effect.agrees.mono within
  exact ⟨u,run,state.after_effect pre ready agrees (writes pre state) (by simp [frame]),effect⟩

theorem sum_eq {t u : RamState} (agrees : AgreesExcept (frame t) t u) :
    sumLimbs u = sumLimbs t := by
  unfold sumLimbs
  congr 1
  · exact agrees.read (n := 64) (r := 11) (by simp [frame])
  · exact agrees.read (n := 64) (r := 10) (by simp [frame])
  · exact agrees.read (n := 64) (r := 9) (by simp [frame])
  · exact agrees.read (n := 64) (r := 8) (by simp [frame])

theorem difference_eq {t u : RamState} (agrees : AgreesExcept (frame t) t u) :
    differenceLimbs u = differenceLimbs t := by
  unfold differenceLimbs
  congr 1
  · exact agrees.read (n := 64) (r := 2) (by simp [frame])
  · exact agrees.read (n := 64) (r := 6) (by simp [frame])
  · exact agrees.read (n := 64) (r := 14) (by simp [frame])
  · exact agrees.read (n := 64) (r := 15) (by simp [frame])

end P256.Proofs.Signing.Core.Iteration.Components.Addition.Choice
