import Sha2.Proofs.Wrapper512.Dispatch.Initialize
import Sha2.Proofs.Wrapper512.State

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Machine.Stages

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.Encoding.Serialize (writable_of_grow)
open Sha2.Proofs.Wrapper512

 theorem stack_slot_writable [Bindings] {v : Variant} {form : Form} {initial s : RamState}
    {inputs : Array Input} (ctx : Context v initial inputs form) (state : State v initial s form)
    {offset : Nat} (bound : offset ≤ (v.routine form).minStackBytes) (align : offset % 8 = 0) :
    MemWritable s (stackPtr initial - BitVec.ofNat 64 offset) 8 := by
  exact writable_of_grow
    (Sha2.Proofs.Wrapper512.Dispatch.stack_sub_writable8_512 ctx bound align)
    state.allocated

 theorem stack_slot_codeApart [Bindings] {v : Variant} {form : Form} {initial : RamState}
    {inputs : Array Input} (ctx : Context v initial inputs form)
    {offset len codeOffset codeLen : Nat}
    (bound : offset ≤ (v.routine form).minStackBytes) (length : len ≤ offset)
    (code : codeOffset + codeLen ≤ 71757) :
    RangeApart (stackPtr initial - BitVec.ofNat 64 offset) len
      (Extracted.textAddress + BitVec.ofNat 64 codeOffset) codeLen := by
  intro j hj k hk eq
  have contains := stackRegion_contains_sub ctx.stack.2.2.1 bound length ⟨j, hj, rfl⟩
  apply (ctx.separation.2 (Stack.region initial (v.routine form).minStackBytes) (by cases form <;> simp [Variant.writeRegions, Variant.routine, Vector.toList, Form.writeRegionCount])).2 _ contains
  left
  rw [eq, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact inProgram_of_textOffset (codeOffset + k) (by omega)

end Sha2.Proofs.Wrapper512.Machine.Stages
