import P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.First.Support
import P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Correction.Difference
import P256.Proofs.Common.Field.Operations.Neg.Borrow.Or
import P256.Proofs.Common.Field.Operations.Neg.SubLoad
import P256.Proofs.Common.Instructions.Sar.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Correction.Borrow

open P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def changes (s : RamState) (regs : List (BitVec 5)) : List Component :=
  regs.map Component.reg ++ [.flags, .rip, .mem (stackPtr s - 112 + 8) 8]

theorem slot_preserved {s t u : RamState} {regs : List (BitVec 5)}
    (ag : AgreesExcept (changes s regs) t u) {offset : Nat}
    (apart : OffsetsApart offset 8 8 8) : slot s u offset = slot s t offset := by
  apply P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees ag
  intro i hi c hc
  simp only [changes, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  rcases hc with ⟨r, _, rfl⟩ | rfl | rfl | rfl
  · exact id
  · exact id
  · exact id
  · rintro ⟨j, hj, he⟩
    exact OffsetsApart.ne (base := stackPtr s - 112) (hi := hi) (hj := hj)
      (hl := by decide) apart he

end P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Correction.Borrow
