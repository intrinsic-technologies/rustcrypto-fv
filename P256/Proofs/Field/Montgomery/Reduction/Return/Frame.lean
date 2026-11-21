import P256.Proofs.Field.Montgomery.Reduction.Output
import P256.Proofs.Program.ScalarFrame.Memory
import P256.Proofs.Common.Field.SquareRoot.Multiply.Prologue

set_option autoImplicit false

namespace P256.Proofs.Field.Montgomery.Reduction.Return

open P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [Bindings] {s t u v : RamState} {boundary : ReturnBoundary}

theorem work_frame (pre : BinaryFieldPre s boundary 0x113c10 56)
    (entry : Entry s t boundary) (body : AgreesExcept (scratchComponents t) t u)
    (stores : AgreesExcept [.mem (s.regValue .rdi) 32, .rip] u v) :
    MemoryWriteFrame t v #v[registerRegion s .rdi 32, ScalarFrame.Work.region s 56 48] := by
  apply (body.trans stores).memoryWriteFrame
  intro c hc a ha
  simp only [scratchComponents, registerClobbers, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl) | (rfl | rfl)
  all_goals try exact ha.elim
  · refine ⟨ScalarFrame.Work.region s 56 48, by simp, ?_⟩
    rw [entry.rsp] at ha
    exact ScalarFrame.Work.contains pre.toCalleePre (offset := 56) (len := 8)
      (by decide) (by decide) ha
  · obtain ⟨i, hi, rfl⟩ := ha
    exact ⟨registerRegion s .rdi 32, by simp, output_contains pre.toCalleePre hi⟩

theorem whole_frame (pre : BinaryFieldPre s boundary 0x113c10 56)
    (entry : Entry s t boundary)
    (work : MemoryWriteFrame t v
      #v[registerRegion s .rdi 32, ScalarFrame.Work.region s 56 48]) :
    MemoryWriteFrame s v #v[registerRegion s .rdi 32, Stack.region s 56] := by
  apply memoryWriteFrame_trans (h₂ := ScalarFrame.Work.frame pre.toCalleePre work)
  have hf := entry.agrees.memoryWriteFrame (prologue_within pre.toCalleePre)
  intro a ha
  apply hf a
  intro r hr hin
  have he : r = Stack.region s 56 := by simpa using hr
  subst r
  exact ha _ (by simp) hin

theorem entry_saved_word (entry : Entry s t boundary) {offset : Nat}
    (hoffset : offset ≤ 48) :
    memLoad t.external (stackPtr s - BitVec.ofNat 64 offset) 64 =
      memLoad (saveMemory s) (stackPtr s - BitVec.ofNat 64 offset) 64 := by
  have apart : OffsetsApart (-56 : BitVec 64) 8 (-(BitVec.ofNat 64 offset)) 8 := by
    change 8 ≤ (-(BitVec.ofNat 64 offset) - (-56 : BitVec 64)).toNat ∧
      8 ≤ ((-56 : BitVec 64) - -(BitVec.ofNat 64 offset)).toNat
    have bound : offset < 2^64 := by omega
    have value : (BitVec.ofNat 64 offset).toNat = offset := Nat.mod_eq_of_lt bound
    have negative : (-56 : BitVec 64).toNat = 18446744073709551560 := by decide +kernel
    rw [BitVec.toNat_sub', BitVec.toNat_sub', negative, BitVec.toNat_neg, value]
    omega
  rw [entry.memory]
  simpa only [BitVec.sub_eq_add_neg] using
    memLoad_memStore_apart (saveMemory s) (stackPtr s) (-56) (-(BitVec.ofNat 64 offset))
      (s.regValue .rax) 64 apart (by decide) (by decide)

theorem saved_slots (pre : BinaryFieldPre s boundary 0x113c10 56)
    (entry : Entry s t boundary)
    (work : MemoryWriteFrame t v
      #v[registerRegion s .rdi 32, ScalarFrame.Work.region s 56 48]) :
    (∀ item ∈ savedRegisters,
      (Operand.mem (stackPtr s - BitVec.ofNat 64 item.2) : Operand 64).read v =
        s.regValue item.1) ∧
      (Operand.mem (stackPtr s) : Operand 64).read v = (returnBoundary s).rip := by
  have read (offset : Nat) (ho : offset ≤ 48) :
      memLoad v.external (stackPtr s - BitVec.ofNat 64 offset) 64 =
        memLoad (saveMemory s) (stackPtr s - BitVec.ofNat 64 offset) 64 :=
    (ScalarFrame.Work.read pre.toCalleePre (by decide) work ho (by omega)).trans
      (entry_saved_word entry ho)
  constructor
  · intro item hi
    have ho : item.2 ≤ 48 := by
      simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (read item.2 ho).trans (saveMemory_saved s item hi)
  · have he := read 0 (by decide)
    simp only [BitVec.sub_zero] at he
    exact he.trans (P256.Proofs.Common.Field.SquareRoot.Multiply.savedMemory_return s)

end P256.Proofs.Field.Montgomery.Reduction.Return
