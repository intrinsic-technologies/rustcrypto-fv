import P256.Proofs.SignatureFromDer.Decode.Save
import X86Proofs.Program.ReadWrite.Bytes

set_option autoImplicit false

namespace P256.Proofs.SignatureFromDer.Decode

open P256.Spec.Program.Routines X86 X86.Machine X86.UserProcess X86Proofs

theorem savedMemory_words (s : RamState) :
    memLoad (savedMemory s) (stackPtr s - 24) 64 = s.regValue .rbx ∧
    memLoad (savedMemory s) (stackPtr s - 16) 64 = s.regValue .r14 ∧
    memLoad (savedMemory s) (stackPtr s - 8) 64 = s.regValue .r15 ∧
    memLoad (savedMemory s) (stackPtr s) 64 = memLoad s.external (stackPtr s) 64 := by
  constructor
  · exact memLoad_memStore _ _ (by decide) (by decide) _
  constructor
  · simp only [savedMemory, BitVec.sub_eq_add_neg]
    rw [memLoad_memStore_apart _ _ _ _ _ 64
      (by unfold OffsetsApart; decide +kernel) (by decide) (by decide)]
    exact memLoad_memStore _ _ (by decide) (by decide) _
  constructor
  · simp only [savedMemory, BitVec.sub_eq_add_neg]
    repeat rw [memLoad_memStore_apart _ _ _ _ _ 64
      (by unfold OffsetsApart; decide +kernel) (by decide) (by decide)]
    exact memLoad_memStore _ _ (by decide) (by decide) _
  · simp only [savedMemory, BitVec.sub_eq_add_neg]
    repeat rw [memLoad_memStore_apart_right _ (stackPtr s) _ _ 64
      (by unfold OffsetsApart; decide +kernel) (by decide) (by decide)]

end P256.Proofs.SignatureFromDer.Decode
