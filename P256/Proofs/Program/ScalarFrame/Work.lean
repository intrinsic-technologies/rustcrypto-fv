import P256.Proofs.Program.Stack
import P256.Proofs.Program.Interface

set_option autoImplicit false

namespace P256.Proofs.Program.ScalarFrame.Work

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable {entry : BitVec 64} {inputBytes outputBytes stackReserve savedBytes : Nat}

def region (s : RamState) (stackReserve savedBytes : Nat) : MemoryRegion :=
  ⟨(stackPtr s).toNat - stackReserve, stackReserve - savedBytes⟩

variable {inputRegister : Syntax.Reg}

theorem contains [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary entry inputBytes outputBytes stackReserve inputRegister) {offset len : Nat} {a : BitVec 64}
    (ho : offset ≤ stackReserve) (hl : len + savedBytes ≤ offset)
    (covered : (Component.mem (stackPtr s - BitVec.ofNat 64 offset) len).Covers a) :
    (Work.region s stackReserve savedBytes).Contains a.toNat := by
  obtain ⟨i, hi, rfl⟩ := covered
  have bounds := stack_bounds pre.stack
  have low := stack_sub_toNat pre.stack ho
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 2^64), Nat.mod_eq_of_lt (by rw [low]; omega), low]
  change (stackPtr s).toNat - stackReserve ≤ _ ∧ _ < (stackPtr s).toNat - stackReserve + (stackReserve - savedBytes)
  constructor <;> omega

theorem frame [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary entry inputBytes outputBytes stackReserve inputRegister)
    (memory : MemoryWriteFrame t u #v[registerRegion s .rdi outputBytes, Work.region s stackReserve savedBytes]) :
    MemoryWriteFrame t u #v[registerRegion s .rdi outputBytes, Stack.region s stackReserve] := by
  intro a ha
  apply memory a
  intro region hr hin
  have hr' : region = registerRegion s .rdi outputBytes ∨ region = Work.region s stackReserve savedBytes := by simpa using hr
  rcases hr' with rfl | rfl
  · exact ha _ (by simp) hin
  · apply ha (Stack.region s stackReserve) (by simp)
    have bounds := stack_bounds pre.stack
    change (stackPtr s).toNat - stackReserve ≤ a.toNat ∧ a.toNat < (stackPtr s).toNat - stackReserve + (stackReserve - savedBytes) at hin
    change (stackPtr s).toNat - stackReserve ≤ a.toNat ∧
      a.toNat < (Stack.region s stackReserve).start + (Stack.region s stackReserve).size
    rw [stack_region_end]
    constructor <;> omega

theorem read [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary entry inputBytes outputBytes stackReserve inputRegister)
    (hreserve : savedBytes ≤ stackReserve)
    (memory : MemoryWriteFrame t u #v[registerRegion s .rdi outputBytes, Work.region s stackReserve savedBytes])
    {offset n : Nat} (ho : offset ≤ savedBytes) (hl : n/8 ≤ offset+8) :
    (Operand.mem (stackPtr s - BitVec.ofNat 64 offset) : Operand n).read u =
      (Operand.mem (stackPtr s - BitVec.ofNat 64 offset) : Operand n).read t := by
  have bounds := stack_bounds pre.stack
  have low := stack_sub_toNat pre.stack (offset := offset) (by omega)
  apply memLoad_congr
  intro i hi
  change (u.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?).getD 0 =
    (t.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?).getD 0
  rw [memory _]
  intro region hr hin
  have hr' : region = registerRegion s .rdi outputBytes ∨ region = Work.region s stackReserve savedBytes := by simpa using hr
  rcases hr' with rfl | rfl
  · apply pre.separation (1 : Fin 3) (2 : Fin 3) (by decide) _ hin
    change (stackPtr s).toNat - stackReserve ≤ _ ∧
      (stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat <
        (Stack.region s stackReserve).start + (Stack.region s stackReserve).size
    rw [stack_region_end, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 2^64), Nat.mod_eq_of_lt (by rw [low]; omega), low]
    constructor <;> omega
  · change (stackPtr s).toNat - stackReserve ≤ _ ∧
      (stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat <
        (stackPtr s).toNat - stackReserve + (stackReserve - savedBytes) at hin
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 2^64), Nat.mod_eq_of_lt (by rw [low]; omega), low] at hin
    omega

end P256.Proofs.Program.ScalarFrame.Work
