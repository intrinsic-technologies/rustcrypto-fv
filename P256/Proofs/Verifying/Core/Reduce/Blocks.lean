import P256.Proofs.Verifying.Core.Reduce.Memory
import P256.Proofs.Verifying.Core.Reduce.Low
import P256.Proofs.Verifying.Core.Reduce.Second
import P256.Proofs.Verifying.Core.Reduce.Third
import P256.Proofs.Verifying.Core.Reduce.High
import P256.Proofs.Common.Memory.Readable

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (CalleePre programLoaded_codeIn programText_slice
  memoryRegion_memReadable readyToStep)

namespace P256.Proofs.Verifying.Core.Reduce

open P256.Proofs.Program
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def blockFrame (s : RamState) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 7, .reg 12, .reg 13, .reg 14, .reg 15,
    .flags, .rip, .mem (stackPtr s + 8) 8, .mem (stackPtr s + 16) 8,
    .mem (stackPtr s + 24) 8, .mem (stackPtr s + 32) 8]

theorem block_pre [Bindings] {s t : RamState} {boundary : ReturnBoundary} {p : BitVec 64}
    (pre : CalleePre s boundary 0x113120 32 32 104) (state : FrameState s t)
    (rsi : t.regValue .rsi = s.regValue .rsi) (rip : t.RIP = p) : BlockPre p t := by
  refine ⟨rip, ?_, ?_, ?_⟩
  · intro offset ho
    have bound : offset + 8 ≤ 32 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl <;> decide
    rw [rsi]
    apply readable_of_grow _ state.allocated
    apply P256.Proofs.Common.Memory.memReadable_sub (len := 32) _ offset 8 bound
    exact memoryRegion_memReadable pre.inputBounded pre.inputAllocated
      (Nat.le_refl _) (Nat.le_refl _)
  · intro offset ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl
    all_goals rw [scalar_stack_address state.rsp (by decide)]
    all_goals exact (writable_of_grow
      (stack_sub_writable8 pre.stack (fun a ha hpt => pre.avoids _ (by simp) a ha (.inr hpt))
        (by decide) (by decide)) state.allocated)
  · intro offset len bound a ha
    apply pre.avoids (Stack.region s 104) (by simp) a _ ∘ Or.inl
    rw [scalar_stack_address state.rsp (by omega)] at ha
    exact ScalarFrame.stack_contains pre (by omega) (by omega) ha

theorem block_writes [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x113120 32 32 104) (state : FrameState s t) :
    WritesWithin (blockFrame t) #v[registerRegion s .rdi 32, workRegion s] := by
  intro c hc a ha
  simp only [blockFrame, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  all_goals refine ⟨workRegion s, by simp, ?_⟩
  · change (Component.mem (stackPtr t + BitVec.ofNat 64 8) 8).Covers a at ha
    rw [scalar_stack_address state.rsp (by decide)] at ha
    exact work_contains pre (by decide) (by decide) ha
  · change (Component.mem (stackPtr t + BitVec.ofNat 64 16) 8).Covers a at ha
    rw [scalar_stack_address state.rsp (by decide)] at ha
    exact work_contains pre (by decide) (by decide) ha
  · change (Component.mem (stackPtr t + BitVec.ofNat 64 24) 8).Covers a at ha
    rw [scalar_stack_address state.rsp (by decide)] at ha
    exact work_contains pre (by decide) (by decide) ha
  · change (Component.mem (stackPtr t + BitVec.ofNat 64 32) 8).Covers a at ha
    rw [scalar_stack_address state.rsp (by decide)] at ha
    exact work_contains pre (by decide) (by decide) ha

theorem block_run [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {p q : BitVec 64} {offset : Nat} {bytes : List UInt8} {E : RamState → Effect}
    (pre : CalleePre s boundary 0x113120 32 32 104) (state : FrameState s t)
    (rsi : t.regValue .rsi = s.regValue .rsi) (rip : t.RIP = p)
    (block : AdvanceTriple boundary (BlockPre p)
      (codeRange (Extracted.textAddress + BitVec.ofNat 64 offset) bytes) (Effect.post E))
    (size : offset + bytes.length ≤ 118431)
    (code : Extracted.textBytes.toListFrom offset bytes.length = bytes)
    (next : (E t).rip = q) (frame : (E t).components ⊆ blockFrame t) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u ∧ u.RIP = q ∧
      u.regValue .rsi = s.regValue .rsi ∧ (E t).Holds t u := by
  obtain ⟨fuel,u,run,ready,_,effect⟩ := block t (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) offset bytes size code)
    (block_pre pre state rsi rip)
  have agrees := effect.agrees.mono frame
  exact ⟨fuel,u,run,state.after_effect pre (by decide) ready agrees (block_writes pre state)
      (by simp [blockFrame]), effect.rip.trans next,
    (agrees.read (n := 64) (r := 6) (by simp [blockFrame])).trans rsi, effect⟩

end P256.Proofs.Verifying.Core.Reduce
