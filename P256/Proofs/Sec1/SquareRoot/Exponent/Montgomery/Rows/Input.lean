import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Rows.Memory

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Montgomery.Rows

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem input_word_preserved {s t : RamState} {ptr : BitVec 64}
    (ag : AgreesExcept (Reduction.scratchComponents s) s t)
    (apart : RangeApart (stackPtr s) 112 ptr 32) (index : Fin 4) :
    (Operand.mem (ptr+BitVec.ofNat 64 (8*index.val)) : Operand 64).read t =
      (Operand.mem (ptr+BitVec.ofNat 64 (8*index.val)) : Operand 64).read s := by
  apply memLoad_congr
  intro i hi
  apply congrArg (fun x : Option UInt8 => x.getD 0)
  apply ag.memory
  intro c hc hv
  simp only [Reduction.scratchComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  all_goals try exact hv.elim
  obtain ⟨j, hj, he⟩ := hv
  apply apart j hj (8*index.val+i) (by have := index.isLt; omega)
  simpa only [BitVec.add_assoc, ← BitVec.ofNat_add] using he.symm

end P256.Proofs.Sec1.SquareRoot.Montgomery.Rows
