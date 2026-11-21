import P256.Proofs.Common.Encoding.Serialize.Convert.SavePointer
import P256.Proofs.Verifying.Core.Reduce.Blocks
import P256.Proofs.Verifying.Core.Reduce.Arithmetic
import P256.Proofs.Field.Representation

set_option autoImplicit false

open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)
open P256.Proofs.SecretKeyFromBytes.Scalar (Limbs)
open P256.Proofs.Program (CalleePre memoryRegion_contains_add)

namespace P256.Proofs.Verifying.Core.Reduce

open P256.Proofs.Program
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem input_word [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x113120 32 32 104) (state : FrameState s t)
    {offset : Nat} (bound : offset + 8 ≤ 32) :
    (Operand.mem (s.regValue .rsi + BitVec.ofNat 64 offset) : Operand 64).read t =
      (Operand.mem (s.regValue .rsi + BitVec.ofNat 64 offset) : Operand 64).read s := by
  apply memLoad_congr
  intro i hi
  change (t.external[s.regValue .rsi + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?).getD 0 =
    (s.external[s.regValue .rsi + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?).getD 0
  rw [state.frame _]
  intro region hr hin
  have member := memoryRegion_contains_add pre.inputBounded
    (Nat.le_refl _) (Nat.le_refl _) (show offset+i < 32 by omega)
  rw [BitVec.ofNat_add, ← BitVec.add_assoc] at member
  have cases : region = registerRegion s .rdi 32 ∨ region = Stack.region s 104 := by
    simpa using hr
  rcases cases with rfl | rfl
  · exact pre.separation (0 : Fin 3) (1 : Fin 3) (by decide) _ member hin
  · exact pre.separation (0 : Fin 3) (2 : Fin 3) (by decide) _ member hin

def borrowFrame (s : RamState) : List Component :=
  [.reg 1, .reg 3, .reg 5, .reg 7, .reg 12, .reg 13, .reg 14, .reg 15,
    .flags, .rip, .mem (stackPtr s + 8) 8]

theorem borrow_slot {s t : RamState} (agrees : AgreesExcept (borrowFrame s) s t)
    {offset : Nat} (ho : offset = 16 ∨ offset = 24 ∨ offset = 32) :
    (Operand.mem (stackPtr s + BitVec.ofNat 64 offset) : Operand 64).read t =
      (Operand.mem (stackPtr s + BitVec.ofNat 64 offset) : Operand 64).read s := by
  apply P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees agrees
  intro i hi c hc ha
  simp only [borrowFrame, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  obtain ⟨j,hj,he⟩ := ha
  rcases ho with rfl | rfl | rfl
  · exact OffsetsApart.ne (c₁ := 8) (c₂ := 16) (len₁ := 8) (len₂ := 8)
      (by unfold OffsetsApart; decide +kernel) (stackPtr s) hj hi (by decide) he.symm
  · exact OffsetsApart.ne (c₁ := 8) (c₂ := 24) (len₁ := 8) (len₂ := 8)
      (by unfold OffsetsApart; decide +kernel) (stackPtr s) hj hi (by decide) he.symm
  · exact OffsetsApart.ne (c₁ := 8) (c₂ := 32) (len₁ := 8) (len₂ := 8)
      (by unfold OffsetsApart; decide +kernel) (stackPtr s) hj hi (by decide) he.symm

structure Subtracted [Bindings] (s t : RamState) (a : Limbs) : Prop extends FrameState s t where
  rip : t.RIP = 0x1131f3
  original0 : (Operand.mem (stackPtr t + 24) : Operand 64).read t = a.l0
  original1 : t.regValue .r12 = a.l1
  original2 : t.regValue .rbp = a.l2
  original3 : t.regValue .rbx = a.l3
  difference0 : (Operand.mem (stackPtr t + 16) : Operand 64).read t = (subtractOrder a).l0
  difference1 : t.regValue .r13 = (subtractOrder a).l1
  difference2 : t.regValue .r15 = (subtractOrder a).l2
  difference3 : t.regValue .r14 = (subtractOrder a).l3
  borrow : t.regValue .rdi = (-SecretKeyFromBytes.Scalar.orderBorrow a) >>> 63
  outputPointer : (Operand.mem (stackPtr t + 32) : Operand 64).read t = s.regValue .rdi

end P256.Proofs.Verifying.Core.Reduce
