import Sha2.Proofs.Wrapper512.Hash.Finalize.State

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Hash.Finalize

open Sha2.Spec Sha2.Proofs.Program Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.SHA512

theorem paddedBuffer_prefix (message : ByteArray) (small : message.size % 128 < 112) :
    (paddedBuffer message).extract 0 112 = finalPrefix message := by
  have count : 127 - message.size % 128 = (111 - message.size % 128) + 16 := by
    omega
  have split : (⟨Array.replicate (127 - message.size % 128) 0⟩ : ByteArray) =
      ⟨Array.replicate (111 - message.size % 128) 0⟩ ++ ⟨Array.replicate 16 0⟩ := by
    apply ByteArray.ext
    simp only [ByteArray.data_append, Array.replicate_append_replicate, count]
  have size : (finalPrefix message).size = 112 := finalPrefix_size message
  have padded : paddedBuffer message = finalPrefix message ++ ⟨Array.replicate 16 0⟩ := by
    simp only [paddedBuffer, finalPrefix, small, ite_true, split, ByteArray.append_assoc]
  rw [padded]
  exact ByteArray.extract_append_eq_left size.symm

theorem finalBlock_eq_tailFirst (message : ByteArray)
    (small : message.size % 128 < 112) :
    finalBlock message = tailFirst message := by
  simp only [finalBlock, finalPrefix, tailFirst, small, ite_true]

theorem finalBlock_eq_tailLast (message : ByteArray)
    (large : ¬ message.size % 128 < 112) :
    finalBlock message = tailLast message := by
  simp only [finalBlock, finalPrefix, tailLast, large, ite_false]

end Sha2.Proofs.Wrapper512.Hash.Finalize
