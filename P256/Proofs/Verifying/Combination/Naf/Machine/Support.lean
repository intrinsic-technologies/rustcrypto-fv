import P256.Proofs.Program.ScalarFrame.Memory
import P256.Proofs.Program.SaveRegisters
import P256.Proofs.Common.EffectCompose.Memory

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Machine

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem stack_code_apart [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {entry : BitVec 64} {inputBytes outputBytes reserve offset len codeOffset codeLen : Nat}
    (pre : CalleePre s boundary entry inputBytes outputBytes reserve)
    (ho : offset ≤ reserve) (hl : len ≤ offset) (hc : codeOffset + codeLen ≤ 118431) :
    RangeApart (stackPtr s - BitVec.ofNat 64 offset) len
      (Extracted.textAddress + BitVec.ofNat 64 codeOffset) codeLen := by
  intro i hi j hj he
  apply pre.avoids (Stack.region s reserve) (by simp) _
    (ScalarFrame.stack_contains pre ho (by omega) ⟨i, hi, rfl⟩)
  left
  rw [he, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact inProgram_of_textOffset (codeOffset + j) (by omega)

theorem saveMemory_return (s : RamState) :
    memLoad (saveMemory s) (stackPtr s) 64 = memLoad s.external (stackPtr s) 64 := by
  simp only [saveMemory, BitVec.sub_eq_add_neg]
  repeat rw [memLoad_memStore_apart_right _ (stackPtr s) _ _ 64
    (by unfold OffsetsApart; decide +kernel) (by decide) (by decide)]

end P256.Proofs.Verifying.Combination.Naf.Machine
