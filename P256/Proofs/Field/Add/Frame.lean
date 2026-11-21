import P256.Proofs.Field.Add.Output
import P256.Proofs.Program.ScalarFrame.Memory
import X86Proofs.Program.ReadWrite.Bytes

set_option autoImplicit false

namespace P256.Proofs.Field.Add.Return

open P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [Bindings] {s t u v : RamState} {boundary : ReturnBoundary}

theorem work_frame (pre : BinaryFieldPre s boundary 0x113e10 16)
    (entry : Entry s t boundary) (body : AgreesExcept (bodyComponents t) t u)
    (stores : AgreesExcept [.mem (s.regValue .rdi) 32, .rip] u v) :
    MemoryWriteFrame t v #v[registerRegion s .rdi 32, ScalarFrame.Work.region s 16 8] := by
  apply (body.trans stores).memoryWriteFrame
  intro c hc a ha
  simp only [bodyComponents, bodyClobbers, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl) | (rfl | rfl)
  all_goals try exact ha.elim
  · refine ⟨ScalarFrame.Work.region s 16 8, by simp, ?_⟩
    rw [entry.rsp] at ha
    exact ScalarFrame.Work.contains pre.toCalleePre (offset := 16) (len := 8)
      (by decide) (by decide) ha
  · obtain ⟨i, hi, rfl⟩ := ha
    exact ⟨registerRegion s .rdi 32, by simp, output_contains pre.toCalleePre hi⟩

theorem whole_frame (pre : BinaryFieldPre s boundary 0x113e10 16)
    (entry : Entry s t boundary)
    (work : MemoryWriteFrame t v
      #v[registerRegion s .rdi 32, ScalarFrame.Work.region s 16 8]) :
    MemoryWriteFrame s v #v[registerRegion s .rdi 32, Stack.region s 16] := by
  apply memoryWriteFrame_trans (h₂ := ScalarFrame.Work.frame pre.toCalleePre work)
  have hf := entry.agrees.memoryWriteFrame (prologue_within pre.toCalleePre)
  intro a ha
  apply hf a
  intro r hr hin
  have he : r = Stack.region s 16 := by simpa using hr
  subst r
  exact ha _ (by simp) hin

theorem saved_slots (pre : BinaryFieldPre s boundary 0x113e10 16)
    (entry : Entry s t boundary)
    (work : MemoryWriteFrame t v
      #v[registerRegion s .rdi 32, ScalarFrame.Work.region s 16 8]) :
    (Operand.mem (stackPtr s - 8) : Operand 64).read v = s.regValue .rbx ∧
      (Operand.mem (stackPtr s) : Operand 64).read v = (returnBoundary s).rip := by
  have read (offset : Nat) (ho : offset ≤ 8) :
      memLoad v.external (stackPtr s - BitVec.ofNat 64 offset) 64 =
        memLoad t.external (stackPtr s - BitVec.ofNat 64 offset) 64 :=
    ScalarFrame.Work.read pre.toCalleePre (by decide) work ho (by omega)
  constructor
  · rw [show (Operand.mem (stackPtr s - 8) : Operand 64).read v =
        memLoad v.external (stackPtr s - BitVec.ofNat 64 8) 64 from rfl,
      read 8 (by decide), entry.memory]
    simp only [prologueMemory, BitVec.sub_eq_add_neg]
    rw [memLoad_memStore_apart _ (stackPtr s) _ _ _ 64
      (by unfold OffsetsApart; decide +kernel) (by decide) (by decide)]
    exact memLoad_memStore _ _ (by decide) (by decide) _
  · have he := read 0 (by decide)
    simp only [BitVec.sub_zero] at he
    change memLoad v.external (stackPtr s) 64 = _
    rw [he, entry.memory]
    simp only [prologueMemory, BitVec.sub_eq_add_neg]
    repeat rw [memLoad_memStore_apart_right _ (stackPtr s) _ _ 64
      (by unfold OffsetsApart; decide +kernel) (by decide) (by decide)]
    rfl

end P256.Proofs.Field.Add.Return
