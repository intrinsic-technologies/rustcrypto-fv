import P256.Proofs.Signing.Core.Iteration.Components.Addition.Subtract.Interface
import P256.Proofs.Signing.Core.Iteration.Components.Addition.Memory
import P256.Proofs.Scalar.Inverse.Parameters
import P256.Proofs.Common.Memory.Readable

set_option autoImplicit false

open P256.Proofs.Program

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (CalleePre programLoaded_codeIn programText_slice
)

namespace P256.Proofs.Signing.Core.Iteration.Components.Addition.Subtract

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def blockFrame (s : RamState) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 5, .reg 6, .reg 13, .reg 14, .reg 15,
    .flags, .rip, .mem (stackPtr s) 8]

theorem block_pre [Bindings] {s t : RamState} {boundary : ReturnBoundary} {p : BitVec 64}
    (pre : CalleePre s boundary 0x113310 32 32 64) (state : FrameState s t)
    (rcx : t.regValue .rcx = 0x2025e0) (rip : t.RIP = p) : BlockPre p t := by
  refine ⟨rip, ?_, ?_, ?_⟩
  · intro offset ho
    have bound : offset + 8 ≤ 32 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl <;> decide
    rw [rcx]
    apply P256.Proofs.Common.Memory.memReadable_sub (len := 32) _ offset 8 bound
    refine ⟨by decide, ?_⟩
    intro i hi
    rw [(P256.Proofs.Scalar.Inverse.parameters_modulus state.loaded).2 i hi]
    trivial
  · exact writable_word pre state
  · intro a ha
    apply pre.avoids (Stack.region s 64) (by simp) a _ ∘ Or.inl
    rw [state.rsp] at ha
    exact P256.Proofs.Program.ScalarFrame.stack_contains pre (by decide) (by decide) ha

theorem block_writes [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x113310 32 32 64) (state : FrameState s t) :
    WritesWithin (blockFrame t) #v[registerRegion s .rdi 32, workRegion s] := by
  intro c hc a ha
  simp only [blockFrame, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  refine ⟨workRegion s, by simp, ?_⟩
  rw [state.rsp] at ha
  exact work_contains pre (by decide) (by decide) ha

theorem block_run [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {p q : BitVec 64} {offset : Nat} {bytes : List UInt8} {E : RamState → Effect}
    (pre : CalleePre s boundary 0x113310 32 32 64) (state : FrameState s t)
    (rcx : t.regValue .rcx = 0x2025e0) (rip : t.RIP = p)
    (block : AdvanceTriple boundary (BlockPre p)
      (codeRange (Extracted.textAddress + BitVec.ofNat 64 offset) bytes) (Effect.post E))
    (size : offset + bytes.length ≤ 118431)
    (code : Extracted.textBytes.toListFrom offset bytes.length = bytes)
    (next : (E t).rip = q) (frame : (E t).components ⊆ blockFrame t) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u ∧ u.RIP = q ∧
      AgreesExcept (blockFrame t) t u ∧ (E t).Holds t u := by
  obtain ⟨fuel,u,run,ready,_,effect⟩ := block t (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) offset bytes size code)
    (block_pre pre state rcx rip)
  have agrees := effect.agrees.mono frame
  exact ⟨fuel,u,run,state.after_effect pre ready agrees (block_writes pre state)
      (by simp [blockFrame]), effect.rip.trans next, agrees, effect⟩

theorem sumLimbs_eq_of_agrees {t u : RamState} (h : AgreesExcept (blockFrame t) t u) :
    sumLimbs u = sumLimbs t := by
  unfold sumLimbs
  congr 1
  · exact h.read (n := 64) (r := 11) (by simp [blockFrame])
  · exact h.read (n := 64) (r := 10) (by simp [blockFrame])
  · exact h.read (n := 64) (r := 9) (by simp [blockFrame])
  · exact h.read (n := 64) (r := 8) (by simp [blockFrame])

end P256.Proofs.Signing.Core.Iteration.Components.Addition.Subtract
