import P256.Proofs.Field.Interface
import P256.Proofs.Field.Schoolbook.Prologue
import P256.Proofs.Field.Schoolbook.Products
import P256.Proofs.Field.Schoolbook.Preservation

set_option autoImplicit false

open P256.Proofs.Common.Field.SquareRoot.Multiply (prologueComponents)
open P256.Proofs.Program (CalleePre inProgram_of_textOffset memoryRegion_contains_add memoryRegion_memReadable stack_region_end)

namespace P256.Proofs.Field.Schoolbook

open P256.Proofs.Program P256.Proofs.Common.Field
open P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Spec.Program.Routines

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem stack_contains [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : SchoolbookPre s boundary)
    {offset len i : Nat} (hoffset : offset ≤ 136) (hlen : len ≤ offset+8) (hi : i < len) :
    (Stack.region s 136).Contains (stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 i).toNat := by
  apply memoryRegion_contains_add pre.stack.1 (len := len) _ _ hi
  · rw [stack_sub_toNat pre.stack hoffset]
    change (stackPtr s).toNat-136 ≤ (stackPtr s).toNat-offset
    omega
  · rw [stack_region_end, stack_sub_toNat pre.stack hoffset]
    have := (stack_bounds pre.stack).1
    omega

theorem prologue_within [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : SchoolbookPre s boundary) :
    WritesWithin (prologueComponents s) #v[registerRegion s .rdi 64, Stack.region s 136] := by
  intro c hc a ha
  simp only [prologueComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact False.elim ha
  all_goals obtain ⟨i, hi, rfl⟩ := ha
  all_goals refine ⟨Stack.region s 136, by simp, ?_⟩
  · exact stack_contains pre (offset := 8) (by decide) (by decide) hi
  · exact stack_contains pre (offset := 16) (by decide) (by decide) hi
  · exact stack_contains pre (offset := 24) (by decide) (by decide) hi
  · exact stack_contains pre (offset := 32) (by decide) (by decide) hi
  · exact stack_contains pre (offset := 40) (by decide) (by decide) hi
  · exact stack_contains pre (offset := 48) (by decide) (by decide) hi

theorem scratch_apart_region [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {address : BitVec 64} (pre : SchoolbookPre s boundary)
    (hsp : rspOf t = stackPtr s-136)
    (bounded : (MemoryRegion.mk address.toNat 32).Bounded)
    (apart : (MemoryRegion.mk address.toNat 32).Disjoint (Stack.region s 136)) :
    RangeApart (rspOf t) 88 address 32 := by
  intro i hi j hj he
  have hinput := memoryRegion_contains_add bounded (len := 32) (Nat.le_refl _)
    (Nat.le_refl (address.toNat+32)) hj
  have hstack := stack_contains pre (offset := 136) (len := 88) (by decide) (by decide) hi
  change (Stack.region s 136).Contains (stackPtr s-136+BitVec.ofNat 64 i).toNat at hstack
  rw [← hsp, he] at hstack
  exact apart _ hinput hstack

theorem products_pre [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : SchoolbookPre s boundary) (rip : t.RIP = 0x11c982)
    (rsp : stackPtr t = stackPtr s-136)
    (frame : AgreesExcept (prologueComponents s) s t) : ProductsPre t := by
  have left : (Operand.reg 6 : Operand 64).read t = s.regValue .rsi :=
    frame.read (by simp [prologueComponents])
  have right : (Operand.reg 1 : Operand 64).read t = s.regValue .rcx :=
    frame.read (by simp [prologueComponents])
  refine ⟨scratchPre_of_callee pre rip rsp frame.grow ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    change InProgram ((Extracted.textAddress+BitVec.ofNat 64 0x1c982)+BitVec.ofNat 64 j)
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact inProgram_of_textOffset (0x1c982+j) (by change j < 116 at hj; omega)
  · rw [left]
    exact readable_of_grow
      (memoryRegion_memReadable pre.inputBounded pre.inputAllocated (Nat.le_refl _) (Nat.le_refl _)) frame.grow
  · rw [right]
    exact readable_of_grow
      (memoryRegion_memReadable pre.rightBounded pre.rightAllocated (Nat.le_refl _) (Nat.le_refl _)) frame.grow
  · rw [left]
    exact scratch_apart_region pre rsp pre.inputBounded
      (pre.separation (0 : Fin 3) 2 (by decide))
  · rw [right]
    exact scratch_apart_region pre rsp pre.rightBounded pre.rightStack

theorem products_scratch {s t : RamState} (h : (productsEffect s).Holds s t) :
    AgreesExcept (scratchComponents (rspOf s)) s t := by
  apply h.agrees.widen
  · intro c hc hm
    simp only [productsEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, or_assoc, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [scratchComponents, Component.isMem]
  · intro a c hc ha
    simp only [productsEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, or_assoc, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact False.elim ha
    all_goals refine ⟨.mem (rspOf s) 88, by simp [scratchComponents], ?_⟩
    · apply scratch_slot_covers (c := 0#64) (by decide +kernel)
      simpa only [BitVec.add_zero] using ha
    all_goals exact scratch_slot_covers (by decide +kernel) ha

end P256.Proofs.Field.Schoolbook
