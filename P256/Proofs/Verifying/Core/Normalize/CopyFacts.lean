import P256.Proofs.Verifying.Core.Normalize.CopyYRun

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Normalize

open Prelude X86 X86.Machine X86Proofs Program ScalarFrame

theorem copied_bytes {s t u : RamState}
    (agrees : AgreesExcept (Copy32.components (stackPtr s-1048)) t u)
    (offset len : Nat) (bound : offset ≤ 1176) (length : len ≤ 1176)
    (apart : offset+32 ≤ 1048 ∨ 1048+len ≤ offset) :
    ∀ i < len, u.external[stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? =
      t.external[stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? := by
  intro i hi
  apply agrees.byte
  intro c hc covered
  simp only [Copy32.components,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl
  all_goals try exact covered.elim
  obtain ⟨j,hj,eq⟩ := covered
  bv_omega


theorem copied_regs {s t u : RamState}
    (agrees : AgreesExcept (Copy32.components (stackPtr s-1048)) t u) :
    ∀ r ∈ [Syntax.Reg.rbx,.rbp,.r14,.r15], u.regValue r = t.regValue r := by
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl
  · exact agrees.read (n := 64) (r := 3) (by simp [Copy32.components])
  · exact agrees.read (n := 64) (r := 5) (by simp [Copy32.components])
  · exact agrees.read (n := 64) (r := 14) (by simp [Copy32.components])
  · exact agrees.read (n := 64) (r := 15) (by simp [Copy32.components])

end P256.Proofs.Verifying.Core.Normalize
