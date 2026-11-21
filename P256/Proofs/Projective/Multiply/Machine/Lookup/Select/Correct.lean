import P256.Proofs.Projective.Multiply.Machine.Lookup.Select.Setup
import P256.Proofs.Projective.Multiply.Machine.Lookup.Select.Return
import P256.Proofs.Projective.Multiply.Machine.Lookup.Select.Finish
import P256.Proofs.Field.Preserve

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Lookup.Select

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Program Field

theorem field_select_bytes_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {select : Bool} (pre : BinaryFieldPre s boundary 0x114380 128)
    (choice : (s.regValue .rcx).setWidth 8 = if select then 1 else 0) :
    ∃ t, CalleeResult s t boundary 32 128 ∧
      ∀ i < 32, t.external[s.regValue .rdi + BitVec.ofNat 64 i]? = outputBytes s select i := by
  obtain ⟨n,t,run,state⟩ := setup pre choice
  obtain ⟨m,u,called,returned⟩ := call_correct pre state
  exact finish pre returned (run.trans called)

theorem field_select_low8_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {x y : Nat} {select : Bool} (pre : BinaryFieldPre s boundary 0x114380 128)
    (left : MontgomeryAt s (s.regValue .rsi) x)
    (right : MontgomeryAt s (s.regValue .rdx) y)
    (choice : (s.regValue .rcx).setWidth 8 = if select then 1 else 0) :
    ∃ t, CalleeResult s t boundary 32 128 ∧
      MontgomeryAt t (s.regValue .rdi) (if select then y else x) := by
  obtain ⟨t,result,bytes⟩ := field_select_bytes_correct pre choice
  refine ⟨t,result,?_⟩
  cases select
  · exact left.of_bytes_eq bytes
  · exact right.of_bytes_eq bytes

theorem field_select_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {x y : Nat} {select : Bool} (pre : BinaryFieldPre s boundary 0x114380 128)
    (left : MontgomeryAt s (s.regValue .rsi) x)
    (right : MontgomeryAt s (s.regValue .rdx) y)
    (choice : s.regValue .rcx = if select then 1 else 0) :
    ∃ t, CalleeResult s t boundary 32 128 ∧
      MontgomeryAt t (s.regValue .rdi) (if select then y else x) := by
  apply field_select_low8_correct pre left right
  rw [choice]
  cases select <;> rfl

end P256.Proofs.Projective.Multiply.Machine.Lookup.Select
