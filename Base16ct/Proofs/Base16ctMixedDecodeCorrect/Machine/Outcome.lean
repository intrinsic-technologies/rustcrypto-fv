import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.Memory

namespace Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine

open Base16ct.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

def mixedCallChanges (initial : RamState) (length : Nat) (writesLength : Bool) : List Component :=
  [.reg 0, .reg 6, .reg 3, .reg 4, .reg 5, .reg 8, .reg 9, .reg 10, .reg 11, .reg 14,
    .flags, .rip, .mem (initial.regValue .rcx) length,
    .mem (initial.regValue .rdx) (if writesLength then 8 else 0), .mem (stackPtr initial - 24) 24]

theorem mixedCallChanges_calleeSaved {initial final : RamState} {length : Nat} {writesLength : Bool}
    (h : AgreesExcept (mixedCallChanges initial length writesLength) initial final)
    (hRbx : final.regValue .rbx = initial.regValue .rbx)
    (hRbp : final.regValue .rbp = initial.regValue .rbp)
    (hR14 : final.regValue .r14 = initial.regValue .r14) :
    CalleeSavedRegistersUnchanged initial final := by
  intro register hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hRbx
  · exact hRbp
  · exact h.read (r := 12) (n := 64) (by simp [mixedCallChanges])
  · exact h.read (r := 13) (n := 64) (by simp [mixedCallChanges])
  · exact hR14
  · exact h.read (r := 15) (n := 64) (by simp [mixedCallChanges])

end Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine
