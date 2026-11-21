import P256.Proofs.ReadBe.Loop.Copy
import P256.Proofs.ReadBe.Loop.Tail
import P256.Proofs.ReadBe.CopyValue

set_option autoImplicit false

open P256.Proofs.Program

namespace P256.Proofs.ReadBe

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem loop_step [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {input : ByteArray} {k : Nat} (pre : Pre s boundary)
    (state : LoopState s t input k) (hk : k < 4) :
    ∃ u fuel, Advances boundary fuel t u ∧ LoopState s u input (k+1) := by
  obtain ⟨u, copy⟩ := loop_copy pre state hk
  have same (r : BitVec 5) (hr : Component.reg r ∉ loopCopyComponents s) :
      (Operand.reg r : Operand 64).read u = (Operand.reg r : Operand 64).read t :=
    copy.agrees.read hr
  have output : u.regValue .r14 = s.regValue .rdx := (same 14 (by simp [loopCopyComponents])).trans state.output
  have offset : u.regValue .r15 = BitVec.ofNat 64 (8*k) := (same 15 (by simp [loopCopyComponents])).trans state.offset
  have size : u.regValue .rbp = 32 := (same 5 (by simp [loopCopyComponents])).trans state.size
  have addr : u.regValue .r14 + u.regValue .r15 = s.regValue .rdx + BitVec.ofNat 64 (8*k) := by rw [output, offset]
  have stack : stackPtr u + 16 = stackPtr s - 56 := by rw [copy.frame.rsp, frameBase_add16]
  have hp : LoopTailPre u k := by
    refine ⟨copy.rip, size, offset, ?_, ?_, ?_⟩
    · rw [stack]
      exact readable_of_grow (stack_sub_readable pre.stack (offset := 56) (len := 8) (by decide) (by decide)) copy.frame.allocated
    · rw [addr]
      have write := pre.output_writable (offset := 8*k) (len := 8) (by omega) (by decide)
      exact ⟨readable_of_grow write.toMemReadable copy.frame.allocated, write.tables⟩
    · intro a ha code
      rw [addr] at ha
      obtain ⟨i, hi, rfl⟩ := ha
      apply pre.avoids (registerRegion s .rdx 32) (by simp) _ ?_ (.inl code)
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact pre.output_contains (by omega)
  obtain ⟨v, tail⟩ := loop_tail (readyToStep copy.frame.machine copy.frame.bindingsSupported) copy.frame.loaded hp hk pre.outerBoundary
  have writes : WritesWithin (loopTailComponents u) #v[registerRegion s .rdx 32, scratchRegion s] := by
    intro c hc a ha
    simp only [loopTailComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try exact ha.elim
    rw [addr] at ha
    obtain ⟨i, hi, rfl⟩ := ha
    refine ⟨registerRegion s .rdx 32, by simp, ?_⟩
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact pre.output_contains (by omega)
  have rsp : stackPtr v = frameBase s :=
    (tail.agrees.read (n := 64) (r := 4) (by simp [loopTailComponents])).trans copy.frame.rsp
  have frame := copy.frame.of_agrees pre tail.ready tail.agrees rsp writes
  have copyFrame := copy.agrees.memoryWriteFrame pre.loop_copy_writes
  have bytes := pre.scratch_input_bytes copyFrame state.inputBytes
  obtain ⟨fuel, run⟩ := copy.execution
  refine ⟨v, fuel+8, run.trans tail.execution, frame, tail.rip, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (tail.agrees.read (n := 64) (r := 3) (by simp [loopTailComponents])).trans
      ((same 3 (by simp [loopCopyComponents])).trans state.bits)
  · exact (tail.agrees.read (n := 64) (r := 5) (by simp [loopTailComponents])).trans size
  · exact (tail.agrees.read (n := 64) (r := 14) (by simp [loopTailComponents])).trans output
  · rw [tail.offset, offset, show 8*(k+1) = 8*k+8 by omega, BitVec.ofNat_add]
    rfl
  · have eq13 : u.regValue .r13 = t.regValue .r13 := same 13 (by simp [loopCopyComponents])
    rw [tail.remaining, eq13, state.remaining]
    have cases : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases cases with rfl | rfl | rfl | rfl <;> decide +kernel
  · have eq12 : u.regValue .r12 = t.regValue .r12 := same 12 (by simp [loopCopyComponents])
    rw [tail.source, eq12, state.source]
    rw [show 32-8*k = (32-8*(k+1))+8 by omega, BitVec.ofNat_add, ← BitVec.add_assoc]
    exact BitVec.add_sub_cancel _ _
  · refine ⟨bytes.1, ?_⟩
    intro i
    have bi := bytes.2 i
    change v.external[BitVec.ofNat 64 ((s.regValue .rdi).toNat+i.val)]? = _
    change u.external[BitVec.ofNat 64 ((s.regValue .rdi).toNat+i.val)]? = _ at bi
    simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at bi ⊢
    apply Eq.trans (tail.agrees.byte ?_) bi
    intro c hc ha
    simp only [loopTailComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try exact ha.elim
    rw [addr] at ha
    obtain ⟨j, hj, he⟩ := ha
    have inputContains := memoryRegion_contains_add pre.inputBounded (Nat.le_refl _) (Nat.le_refl _)
      (show i.val < 32 by have := bytes.1; change input.size = 32 at this; omega)
    apply pre.separation (0 : Fin 3) (1 : Fin 3) (by decide) _ inputContains
    rw [he, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact pre.output_contains (by omega)
  · intro j hj
    by_cases equal : j = k
    · subst j
      have value := tail.word
      rw [addr, copy.frame.rsp] at value
      exact value.trans copy.value
    · have earlier : j < k := by omega
      apply Eq.trans _ ((pre.scratch_output_word copyFrame (by omega)).trans (state.words j earlier))
      apply memLoad_congr
      intro i hi
      change v.external[s.regValue .rdx + BitVec.ofNat 64 (8*j) + BitVec.ofNat 64 i]?.getD 0 =
        u.external[s.regValue .rdx + BitVec.ofNat 64 (8*j) + BitVec.ofNat 64 i]?.getD 0
      congr 1
      apply tail.agrees.byte
      intro c hc ha
      simp only [loopTailComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try exact ha.elim
      rw [addr] at ha
      obtain ⟨l, hl, he⟩ := ha
      exact (RangeApart.offsets (s.regValue .rdx) (a := 8*k) (len := 8) (b := 8*j) (count := 8)
        (by omega) (by omega) (.inr (by omega))) l hl i hi he.symm

end P256.Proofs.ReadBe
