import P256.Proofs.Projective.Double.Values
import P256.Proofs.Program.FieldCall.Unary
import P256.Proofs.Program.FieldCall.Binary
import P256.Proofs.Field.Double
import P256.Proofs.Field.Montgomery
import P256.Proofs.Field.Add
import P256.Proofs.Field.Subtract
import P256.Proofs.Projective.Double.CrossTerms.Memory
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false


namespace P256.Proofs.Projective.Double.Combinations

variable {inputRegister : X86.Syntax.Reg}

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Program.FieldCall P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

open CrossTerms (slot_add store_writes)

theorem store_read {s t u : RamState} {offset target : Nat}
    (frame : AgreesExcept [.mem (stackSlot s offset) 8, .rip] t u)
    (hb₁ : offset + 8 ≤ 2^64) (hb₂ : target + 8 ≤ 2^64)
    (apart : offset + 8 ≤ target ∨ target + 8 ≤ offset) :
    memLoad u.external (stackSlot s target) 64 =
      memLoad t.external (stackSlot s target) 64 :=
  read_of_store frame (RangeApart.offsets _ hb₁ hb₂ apart)

theorem montgomery_of_store {t u : RamState} {a b : BitVec 64} {value : Nat}
    (frame : AgreesExcept [.mem a 8, .rip] t u) (apart : RangeApart a 8 b 32)
    (input : MontgomeryAt t b value) : MontgomeryAt u b value := by
  apply input.of_bytes_eq
  intro i hi
  apply frame.byte
  intro c hc hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · obtain ⟨j, hj, he⟩ := hv
    exact apart j hj i hi he.symm
  · exact hv.elim

theorem store_montgomery {s t u : RamState} {offset target value : Nat}
    (frame : AgreesExcept [.mem (stackSlot s offset) 8, .rip] t u)
    (hb₁ : offset + 8 ≤ 2^64) (hb₂ : target + 32 ≤ 2^64)
    (apart : offset + 8 ≤ target ∨ target + 32 ≤ offset)
    (input : MontgomeryAt t (stackSlot s target) value) :
    MontgomeryAt u (stackSlot s target) value :=
  montgomery_of_store frame (RangeApart.offsets _ hb₁ hb₂ apart) input

theorem store_point [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {offset : Nat} {point : Projective} (pre : CalleePre s boundary 0x105d80 0 96 1016 inputRegister)
    (frame : AgreesExcept [.mem (stackSlot s offset) 8, .rip] t u)
    (bound : offset + 8 ≤ 728) (input : ProjectiveAt t (s.regValue .rdi) point) :
    ProjectiveAt u (s.regValue .rdi) point := by
  refine ⟨?_, ?_, ?_⟩
  · have h := montgomery_of_store frame
      (stack_point_apart pre bound (poffset := 0) (plen := 32) (by decide))
      (by simpa only [BitVec.add_zero] using input.1)
    simpa only [BitVec.add_zero] using h
  · exact montgomery_of_store frame (stack_point_apart pre bound
      (poffset := 32) (plen := 32) (by decide)) input.2.1
  · exact montgomery_of_store frame (stack_point_apart pre bound
      (poffset := 64) (plen := 32) (by decide)) input.2.2

end P256.Proofs.Projective.Double.Combinations
