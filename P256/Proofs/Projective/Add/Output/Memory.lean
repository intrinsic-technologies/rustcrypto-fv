import P256.Proofs.Projective.Add.Copy.Preservation
import P256.Proofs.Program.ScalarFrame.Output
import P256.Proofs.Program.WrapperMemory

set_option autoImplicit false


namespace P256.Proofs.Projective.Add.Output

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [Bindings] {s t u : RamState} {boundary : ReturnBoundary}

theorem stack_apart (pre : CalleePre s boundary 0x1051f0 96 96 920)
    {off len stackOff stackLen : Nat} (hn : off + len ≤ 96)
    (hs : stackOff ≤ 920) (hl : stackLen ≤ stackOff + 8) :
    RangeApart (s.regValue .rdi + BitVec.ofNat 64 off) len
      (stackPtr s - BitVec.ofNat 64 stackOff) stackLen := by
  intro i hi j hj he
  apply pre.separation (1 : Fin 3) (2 : Fin 3) (by decide) _ _
    (stack_contains pre hs hl ⟨j, hj, rfl⟩)
  rw [← he]
  exact output_contains pre hn ⟨i, hi, rfl⟩

theorem preserve_output_work (pre : CalleePre s boundary 0x1051f0 96 96 920)
    (frame : MemoryWriteFrame t u #v[workRegion s 920]) {off value : Nat}
    (ho : off + 32 ≤ 96) (input : MontgomeryAt t (s.regValue .rdi + BitVec.ofNat 64 off) value) :
    MontgomeryAt u (s.regValue .rdi + BitVec.ofNat 64 off) value := by
  refine input.of_bytes_eq ?_
  intro i hi
  apply frame _
  intro region hr hin
  have he : region = workRegion s 920 := by simpa using hr
  subst region
  apply pre.separation (1 : Fin 3) (2 : Fin 3) (by decide) _ (output_contains pre ho ⟨i, hi, rfl⟩)
  have hb := stack_bounds pre.stack
  change (stackPtr s).toNat - 920 ≤ _ ∧ _ < (stackPtr s).toNat - 920 + 872 at hin
  change (stackPtr s).toNat - 920 ≤ _ ∧ _ < (Stack.region s 920).start + (Stack.region s 920).size
  rw [stack_region_end]
  constructor <;> omega

end P256.Proofs.Projective.Add.Output
