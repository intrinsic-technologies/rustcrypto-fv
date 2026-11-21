import P256.Proofs.Signing.Wrapper.Entry.Decode.Memory

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Entry.Decode

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program Prelude
open X86 X86.Machine X86.UserProcess X86Proofs

structure Saved (initial s : RamState) : Prop where
  pointers : s.regValue .r12 = initial.regValue .rdi
  count : s.regValue .r13 = 2
  lengths : memLoad s.external (stackPtr initial-192) 64 = initial.regValue .rdx
  output : memLoad s.external (stackPtr initial-208) 64 = initial.regValue .rcx
  capacity : memLoad s.external (stackPtr initial-200) 64 = initial.regValue .r8

theorem Saved.preserve [Bindings] {initial s t : RamState} {cs : List Component}
    (saved : Saved initial s) (state : State initial s 520) (agrees : AgreesExcept cs s t)
    (pointers : .reg 12 ∉ cs) (count : .reg 13 ∉ cs)
    (memory : ∀ target ∈ ([312,320,328] : List Nat), ∀ p n, Component.mem p n ∈ cs →
      ∃ off, off+n ≤ 472 ∧ (off+n ≤ target ∨ target+8 ≤ off) ∧
        p = stackPtr s+BitVec.ofNat 64 off) : Saved initial t := by
  refine ⟨(agrees.read (n:=64) pointers).trans saved.pointers,
    (agrees.read (n:=64) count).trans saved.count,?_,?_,?_⟩
  · have h := stack_memLoad_preserved (target:=328) (width:=64) agrees
      (by decide) (memory 328 (by simp))
    rw [stack_address state (by decide)] at h
    exact h.trans saved.lengths
  · have h := stack_memLoad_preserved (target:=312) (width:=64) agrees
      (by decide) (memory 312 (by simp))
    rw [stack_address state (by decide)] at h
    exact h.trans saved.output
  · have h := stack_memLoad_preserved (target:=320) (width:=64) agrees
      (by decide) (memory 320 (by simp))
    rw [stack_address state (by decide)] at h
    exact h.trans saved.capacity

end P256.Proofs.Signing.Wrapper.Entry.Decode
