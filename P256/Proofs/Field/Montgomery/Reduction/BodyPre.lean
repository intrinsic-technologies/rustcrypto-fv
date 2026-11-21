import P256.Proofs.Field.Montgomery.Reduction.Entry
import P256.Proofs.Field.Montgomery.Reduction.Body
import P256.Proofs.Field.Representation
import P256.Proofs.Common.Memory.Readable

set_option autoImplicit false

namespace P256.Proofs.Field.Montgomery.Reduction

open P256.Spec.Program.Routines P256.Proofs.Program
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [Bindings] {s t : RamState} {boundary : ReturnBoundary}

omit [Bindings] in
theorem stack_contains (stack : Stack.Valid s 56) {offset len i : Nat}
    (hoff : offset ≤ 56) (hlen : len ≤ offset + 8) (hi : i < len) :
    (Stack.region s 56).Contains (stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat := by
  apply memoryRegion_contains_add stack.1 (len := len) _ _ hi
  · rw [stack_sub_toNat stack hoff]
    change (stackPtr s).toNat - 56 ≤ (stackPtr s).toNat - offset
    omega
  · rw [stack_region_end, stack_sub_toNat stack hoff]
    have := (stack_bounds stack).1
    omega

theorem prologue_within (pre : CalleePre s boundary 0x113c10 32 32 56) :
    WritesWithin (prologueComponents s) #v[Stack.region s 56] := by
  intro c hc a ha
  simp only [prologueComponents, saveFrame, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
  all_goals try exact ha.elim
  all_goals
    obtain ⟨i, hi, rfl⟩ := ha
    exact ⟨Stack.region s 56, by simp,
      stack_contains pre.stack (by decide) (by decide) hi⟩

theorem prologue_nat256 (pre : CalleePre s boundary 0x113c10 32 32 56)
    (agrees : AgreesExcept (prologueComponents s) s t) {address : BitVec 64} {value : Nat}
    (bounded : (MemoryRegion.mk address.toNat 32).Bounded)
    (apart : (MemoryRegion.mk address.toNat 32).Disjoint (Stack.region s 56))
    (initial : Nat256At s address value) : Nat256At t address value := by
  have frame := agrees.memoryWriteFrame (prologue_within pre)
  refine ⟨initial.1, ?_⟩
  intro i hi
  rw [frame _]
  · exact initial.2 i hi
  · intro region hr hin
    have he : region = Stack.region s 56 := by simpa using hr
    subst region
    exact apart _ (memoryRegion_contains_add bounded (len := 32)
      (Nat.le_refl _) (Nat.le_refl _) hi) hin

theorem body_pre (pre : BinaryFieldPre s boundary 0x113c10 56)
    (agrees : AgreesExcept (prologueComponents s) s t)
    (rip : t.RIP = 0x113c1b) (rsp : stackPtr t = stackPtr s - 56) : BodyPre t := by
  have low : (Operand.reg 6 : Operand 64).read t = s.regValue .rsi :=
    agrees.read (by simp [prologueComponents, saveFrame])
  have high : (Operand.reg 2 : Operand 64).read t = s.regValue .rdx :=
    agrees.read (by simp [prologueComponents, saveFrame])
  have lowRead : MemReadable s (s.regValue .rsi) 32 :=
    memoryRegion_memReadable pre.inputBounded pre.inputAllocated (Nat.le_refl _) (Nat.le_refl _)
  have highRead : MemReadable s (s.regValue .rdx) 32 :=
    memoryRegion_memReadable pre.rightBounded pre.rightAllocated (Nat.le_refl _) (Nat.le_refl _)
  refine ⟨rip, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [low]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    all_goals exact readable_of_grow (P256.Proofs.Common.Memory.memReadable_sub lowRead _ 8 (by decide)) agrees.grow
  · intro i hi
    rw [high]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    all_goals exact readable_of_grow (P256.Proofs.Common.Memory.memReadable_sub highRead _ 8 (by decide)) agrees.grow
  · rw [rsp]
    exact writable_of_grow (stack_sub_writable8 pre.stack (fun a ha hp => pre.avoids _ (by simp) a ha (.inr hp)) (by decide) (by decide)) agrees.grow
  · rw [rsp]
    intro a ha hin
    obtain ⟨i, hi, rfl⟩ := ha
    exact pre.avoids (Stack.region s 56) (by simp) _
      (stack_contains pre.stack (offset := 56) (by decide) (by decide) hi) (.inl hin)


end P256.Proofs.Field.Montgomery.Reduction
