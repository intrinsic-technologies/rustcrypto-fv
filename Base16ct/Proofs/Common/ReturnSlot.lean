import Base16ct.Spec.Program
import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Setup
import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.Memory
import Base16ct.Proofs.Base16ctUpperEncodeCorrect.Machine
import Base16ct.Proofs.Copied.Md5.Proofs.Block.Preconditions

namespace Base16ct.Proofs.Common

open Base16ct.Spec Base16ct.Spec.Program
open Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem length_store_return_byte_preserved [Bindings] {routine : Routine} {lengthWritten : Prop}
    {initial t : RamState} {byteLength : Nat}
    (hCall : ValidLengthCall routine initial byteLength lengthWritten)
    (hlengthWritten : lengthWritten)
    (hFrame : AgreesExcept [.mem (initial.regValue .rdx) 8, .rip] initial t)
    {i : Nat} (hi : i < 8) :
    t.external[stackPtr initial + BitVec.ofNat 64 i]? =
      initial.external[stackPtr initial + BitVec.ofNat 64 i]? := by
  rw [hFrame.byte]
  intro c hc hcov
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · obtain ⟨j, hj, heq⟩ := hcov
    have hLen := region_offset_contains
      (hCall.lengthOutputInMemoryIfLengthWritten hlengthWritten).1 (i := j) hj
    obtain ⟨hs, he⟩ := Base16ct.Proofs.Copied.Md5.Proofs.Block.stack_subrange_bounds hCall.stack
      (used := 0) (by omega)
    have hStack := Base16ct.Proofs.Base16ctUpperEncodeCorrect.contains_offset_of_subrange
      hCall.stack.1 hs he i hi
    have hStack' : (Stack.region initial routine.minStackBytes).Contains
        (stackPtr initial + BitVec.ofNat 64 i).toNat := by
      simpa only [BitVec.sub_zero] using hStack
    have hLen' : (lengthOutputRegion initial).Contains
        (initial.regValue .rdx + BitVec.ofNat 64 j).toNat := by
      simpa [lengthOutputRegion, registerRegion] using hLen
    rw [heq] at hStack'
    exact (hCall.separation.2 hlengthWritten).1 _ hLen' hStack'
  · exact hcov

theorem length_store_return_readable [Bindings] {routine : Routine} {lengthWritten : Prop}
    {initial t : RamState} {byteLength : Nat}
    (hCall : ValidLengthCall routine initial byteLength lengthWritten)
    (hlengthWritten : lengthWritten)
    (hFrame : AgreesExcept [.mem (initial.regValue .rdx) 8, .rip] initial t) :
    MemReadable t (stackPtr initial) 8 := by
  have hInitial := Base16ct.Proofs.Copied.Md5.Proofs.stack_return_readable hCall.stack
  refine ⟨hInitial.low, ?_⟩
  intro i hi
  rw [length_store_return_byte_preserved hCall hlengthWritten hFrame hi]
  exact hInitial.mem i hi

theorem length_store_return_top [Bindings] {routine : Routine} {lengthWritten : Prop}
    {initial t : RamState} {byteLength : Nat}
    (hCall : ValidLengthCall routine initial byteLength lengthWritten)
    (hlengthWritten : lengthWritten)
    (hFrame : AgreesExcept [.mem (initial.regValue .rdx) 8, .rip] initial t)
    (hRsp : stackPtr t = stackPtr initial) :
    stackTop t = (returnBoundary initial).rip := by
  unfold stackTop returnBoundary
  rw [hRsp]
  apply memLoad_congr
  intro i hi
  change (t.external[stackPtr initial + BitVec.ofNat 64 i]?).getD 0 =
    (initial.external[stackPtr initial + BitVec.ofNat 64 i]?).getD 0
  rw [length_store_return_byte_preserved hCall hlengthWritten hFrame hi]

end Base16ct.Proofs.Common
