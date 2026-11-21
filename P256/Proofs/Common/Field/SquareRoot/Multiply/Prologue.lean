import X86Proofs.Instructions.Sub.Generated.Imm8.Triple
import X86Proofs.Instructions.Push.Triple
import X86Proofs.Program.ReadWrite.Bytes

set_option autoImplicit false

namespace P256.Proofs.Common.Encoding.Serialize
open X86
def savedRegisters : List (Syntax.Reg × Nat) :=
  [(.rbp, 8), (.r15, 16), (.r14, 24), (.r13, 32), (.r12, 40), (.rbx, 48)]
end P256.Proofs.Common.Encoding.Serialize

namespace P256.Proofs.Common.Field.SquareRoot.Multiply

open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def savedMemory (s : RamState) : Ram :=
  memStore (memStore (memStore (memStore (memStore (memStore s.external
    (stackPtr s - 8) (s.regValue .rbp))
    (stackPtr s - 16) (s.regValue .r15))
    (stackPtr s - 24) (s.regValue .r14))
    (stackPtr s - 32) (s.regValue .r13))
    (stackPtr s - 40) (s.regValue .r12))
    (stackPtr s - 48) (s.regValue .rbx)

def prologueComponents (s : RamState) : List Component :=
  [.reg 4, .flags, .rip, .mem (stackPtr s - 8) 8, .mem (stackPtr s - 16) 8,
    .mem (stackPtr s - 24) 8, .mem (stackPtr s - 32) 8,
    .mem (stackPtr s - 40) 8, .mem (stackPtr s - 48) 8]

theorem pushAfter_read_ne (s : RamState) (src : BitVec 4) (r : BitVec 5)
    (hr : r ≠ 4) :
    (Operand.reg r : Operand 64).read (pushAfter s src) =
      (Operand.reg r : Operand 64).read s := by
  exact (AgreesExcept.afterStep_push s (encodePushR64 src).length _ _).read
    (by simpa using hr)

theorem pushAfter_external (s : RamState) (src : BitVec 4) :
    (pushAfter s src).external = memStore s.external (pushAddr s)
      ((Operand.reg (src.setWidth 5) : Operand 64).read s) := rfl

theorem savedMemory_registers (s : RamState) :
    ∀ entry ∈ P256.Proofs.Common.Encoding.Serialize.savedRegisters,
      memLoad (savedMemory s) (stackPtr s - BitVec.ofNat 64 entry.2) 64 =
        s.regValue entry.1 := by
  intro entry hentry
  simp only [P256.Proofs.Common.Encoding.Serialize.savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at hentry
  rcases hentry with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [savedMemory, BitVec.sub_eq_add_neg]
    repeat first
      | rw [memLoad_memStore_apart _ (stackPtr s) _ _ _ 64
          (by unfold OffsetsApart; decide +kernel) (by decide) (by decide)]
    exact memLoad_memStore _ _ (by decide) (by decide) _

theorem savedMemory_return (s : RamState) :
    memLoad (savedMemory s) (stackPtr s) 64 = memLoad s.external (stackPtr s) 64 := by
  simp only [savedMemory, BitVec.sub_eq_add_neg]
  repeat rw [memLoad_memStore_apart_right _ (stackPtr s) _ _ 64
    (by unfold OffsetsApart; decide +kernel) (by decide) (by decide)]

end P256.Proofs.Common.Field.SquareRoot.Multiply
