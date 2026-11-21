import P256.Spec.Program.Functions
import P256.Proofs.Program.PushSequenceFrame
import P256.Proofs.Program.StackAllocate
import P256.Proofs.Program.WrapperMemory

set_option autoImplicit false

namespace P256.Proofs.Pkcs8

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program Prelude
open X86 X86.Machine X86.UserProcess X86Proofs

def saveMemory (s : RamState) : Ram :=
  memStore (memStore (memStore s.external (stackPtr s-8) (s.regValue .r15))
    (stackPtr s-16) (s.regValue .r14)) (stackPtr s-24) (s.regValue .rbx)

def saveComponents (s : RamState) : List Component :=
  [.reg 4, .flags, .rip, .mem (stackPtr s-8) 8,
    .mem (stackPtr s-16) 8, .mem (stackPtr s-24) 8]

theorem saveMemory_words (s : RamState) :
    memLoad (saveMemory s) (stackPtr s-24) 64 = s.regValue .rbx ∧
    memLoad (saveMemory s) (stackPtr s-16) 64 = s.regValue .r14 ∧
    memLoad (saveMemory s) (stackPtr s-8) 64 = s.regValue .r15 ∧
    memLoad (saveMemory s) (stackPtr s) 64 = (returnBoundary s).rip := by
  constructor
  · exact memLoad_memStore _ _ (by decide) (by decide) _
  constructor
  · simp only [saveMemory, BitVec.sub_eq_add_neg]
    rw [memLoad_memStore_apart _ _ _ _ _ 64
      (by unfold OffsetsApart; decide +kernel) (by decide) (by decide)]
    exact memLoad_memStore _ _ (by decide) (by decide) _
  constructor
  · simp only [saveMemory, BitVec.sub_eq_add_neg]
    rw [memLoad_memStore_apart _ _ _ _ _ 64
      (by unfold OffsetsApart; decide +kernel) (by decide) (by decide)]
    rw [memLoad_memStore_apart _ _ _ _ _ 64
      (by unfold OffsetsApart; decide +kernel) (by decide) (by decide)]
    exact memLoad_memStore _ _ (by decide) (by decide) _
  · change memLoad (saveMemory s) (stackPtr s) 64 = memLoad s.external (stackPtr s) 64
    simp only [saveMemory, BitVec.sub_eq_add_neg]
    repeat rw [memLoad_memStore_apart_right _ (stackPtr s) _ _ 64
      (by unfold OffsetsApart; decide +kernel) (by decide) (by decide)]

theorem saveMemory_heapLength (s : RamState) :
    memLoad (saveMemory s) (stackPtr s+8) 64 = memLoad s.external (stackPtr s+8) 64 := by
  simp only [saveMemory, BitVec.sub_eq_add_neg]
  repeat rw [memLoad_memStore_apart _ (stackPtr s) _ _ _ 64
    (by unfold OffsetsApart; decide +kernel) (by decide) (by decide)]

end P256.Proofs.Pkcs8
