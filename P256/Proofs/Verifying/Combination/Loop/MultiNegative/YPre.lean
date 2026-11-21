import P256.Proofs.Verifying.Combination.Loop.MultiNegative.Frame
import P256.Proofs.Verifying.Combination.Loop.MultiNegative.YCopy
import P256.Proofs.Sec1Serialize.Tail.Selection.Memory

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Loop.Multi.Negative

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open P256.Proofs.Program.ScalarFrame
open P256.Proofs.Sec1Serialize.Selection (sub_add_index)
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def ySource (t : RamState) : BitVec 64 := t.regValue .rbp + t.regValue .rax + 32

def yDestination (t : RamState) : BitVec 64 := stackPtr t + 40

theorem y_pre [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {tables digits : BitVec 64} {p q point : Projective} {u v k : Nat} {left : Bool}
    (pre : MultiPre s boundary tables digits)
    (state : DigitData s t tables digits p q u v k point left)
    (i : Fin 8) (rip : t.RIP = 0x10f204)
    (stride : t.regValue .rax = BitVec.ofNat 64 (96*i.val)) :
    Copy32.Pre 0x10f204 ySource yDestination t := by
  let index : Nat := (if left then 0 else 768) + 96*i.val + 32
  have hi : index + 32 ≤ 1536 := by have := i.isLt; cases left <;> dsimp [index] <;> omega
  have source : ySource t = tables + BitVec.ofNat 64 index := by
    simp only [ySource, state.tableCursor, stride]
    cases left <;> simp [index, BitVec.ofNat_add, BitVec.add_assoc]
  have tb : tables.toNat + 1536 < 2^32 := pre.tablesBounded
  have srcNat : (ySource t).toNat = tables.toNat + index := by
    rw [source, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have dst : yDestination t = stackPtr s - 368 :=
    scalar_stack_address state.rsp (offset := 40) (by decide) (by decide)
  have dstAt (n : Nat) (hn : n ≤ 24) :
      yDestination t + BitVec.ofNat 64 n = stackPtr s - BitVec.ofNat 64 (368-n) := by
    rw [dst]; exact sub_add_index _ (offset := 368) (by omega) (by decide)
  refine ⟨rip, ?_, ?_, ?_, ?_⟩
  · intro a ha
    have hn : a.toNat ≤ 24 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl <;> decide
    have an : (ySource t+a).toNat = tables.toNat + index + a.toNat := by
      rw [BitVec.toNat_add, srcNat]; omega
    apply readable_of_grow (s := s) _ state.allocated
    apply memoryRegion_memReadable pre.tablesBounded pre.tablesAllocated
    · change tables.toNat ≤ _; rw [an]; omega
    · change _ + 8 ≤ tables.toNat + 1536; rw [an]; omega
  · intro a ha
    have hn : a.toNat ≤ 24 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl <;> decide
    have halign : (368-a.toNat)%8=0 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl <;> decide
    have da : yDestination t + a = stackPtr s - BitVec.ofNat 64 (368-a.toNat) := by
      simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using dstAt a.toNat hn
    rw [da]
    apply P256.Proofs.Common.Instructions.CrossPageStore.Writable.of_memWritable
    exact writable_of_grow (stack_sub_writable8 pre.stack
      (fun a ha hp => pre.avoids (Stack.region s 1432) (by simp) a ha (.inr hp))
      (by omega) halign) state.allocated
  · rw [dst]
    intro j hj l hl he
    apply pre.tablesStack (ySource t + BitVec.ofNat 64 l).toNat
    · rw [source, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact memoryRegion_contains_add pre.tablesBounded (Nat.le_refl _) (Nat.le_refl _) (show index+l<1536 by omega)
    · rw [← he]
      exact stack_contains pre.toCalleePre (offset := 368) (len := 32)
        (by decide) (by decide) ⟨j,hj,rfl⟩
  · intro a ha off len hb
    have hn : a.toNat ≤ 24 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl <;> decide
    have da : yDestination t + a = stackPtr s - BitVec.ofNat 64 (368-a.toNat) := by
      simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using dstAt a.toNat hn
    rw [da]
    intro j hj l hl he
    apply pre.avoids (Stack.region s 1432) (by simp) _
      (stack_contains pre.toCalleePre (offset := 368-a.toNat) (len := 8)
        (by omega) (by omega) ⟨j,hj,rfl⟩) (.inl ?_)
    change InProgram (stackPtr s - BitVec.ofNat 64 (368-a.toNat) + BitVec.ofNat 64 j)
    rw [he, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact inProgram_of_textOffset _ (by omega)

end P256.Proofs.Verifying.Combination.Loop.Multi.Negative
