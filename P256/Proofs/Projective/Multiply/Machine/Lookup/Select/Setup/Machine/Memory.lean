import P256.Proofs.Projective.Multiply.Machine.Lookup.Select.Setup.Effect
import P256.Proofs.Program.Code

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)

open P256.Proofs.Program (CalleePre inProgram_of_textOffset memoryRegion_contains_add memoryRegion_memReadable stack_region_end)

namespace P256.Proofs.Projective.Multiply.Machine.Lookup.Select

open P256.Proofs.Field P256.Proofs.Program P256.Spec.Program.Routines
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [Bindings] {s : RamState} {boundary : ReturnBoundary}

theorem setup_stack_contains (pre : CalleePre s boundary 0x114380 32 32 128)
    {offset len i : Nat} (hoffset : offset ≤ 128) (hlen : len ≤ offset + 8) (hi : i < len) :
    (Stack.region s 128).Contains
      (stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat := by
  apply memoryRegion_contains_add pre.stack.1 (len := len) _ _ hi
  · rw [P256.Proofs.Program.stack_sub_toNat pre.stack hoffset]
    change (stackPtr s).toNat - 128 ≤ (stackPtr s).toNat - offset
    omega
  · rw [stack_region_end, P256.Proofs.Program.stack_sub_toNat pre.stack hoffset]
    have := (P256.Proofs.Program.stack_bounds pre.stack).1
    omega

theorem setup_stack_codeApart (pre : CalleePre s boundary 0x114380 32 32 128)
    {offset len codeOffset codeLen : Nat}
    (hoffset : offset ≤ 128) (hlen : len ≤ offset + 8) (hcode : codeOffset + codeLen ≤ 118431) :
    RangeApart (stackPtr s - BitVec.ofNat 64 offset) len
      (Extracted.textAddress + BitVec.ofNat 64 codeOffset) codeLen := by
  intro i hi j hj he
  apply pre.avoids (Stack.region s 128) (by simp) _
    (setup_stack_contains pre hoffset hlen hi) (.inl ?_)
  rw [he, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact inProgram_of_textOffset (codeOffset + j) (by omega)

theorem setup_stack_sourceApart (pre : CalleePre s boundary 0x114380 32 32 128)
    {offset len sourceOffset sourceLen : Nat}
    (hoffset : offset ≤ 128) (hlen : len ≤ offset + 8)
    (hsource : sourceOffset + sourceLen ≤ 32) :
    RangeApart (stackPtr s - BitVec.ofNat 64 offset) len
      (s.regValue .rsi + BitVec.ofNat 64 sourceOffset) sourceLen := by
  intro i hi j hj he
  have hin : (registerRegion s .rsi 32).Contains
      (s.regValue .rsi + BitVec.ofNat 64 sourceOffset + BitVec.ofNat 64 j).toNat := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact memoryRegion_contains_add pre.inputBounded (Nat.le_refl _) (Nat.le_refl _) (show sourceOffset + j < 32 by omega)
  exact pre.separation (0 : Fin 3) (2 : Fin 3) (by decide) _ hin
    (he ▸ setup_stack_contains pre hoffset hlen hi)

theorem setup_input_readable (pre : CalleePre s boundary 0x114380 32 32 128)
    {offset len : Nat} (h : offset + len ≤ 32) :
    MemReadable s (s.regValue .rsi + BitVec.ofNat 64 offset) len := by
  have hb : (s.regValue .rsi).toNat + 32 < 2^32 := pre.inputBounded
  have ho : (s.regValue .rsi + BitVec.ofNat 64 offset).toNat =
      (s.regValue .rsi).toNat + offset := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show offset < 2^64 by omega),
      Nat.mod_eq_of_lt (by omega)]
  apply memoryRegion_memReadable pre.inputBounded pre.inputAllocated
  · rw [ho]
    change (s.regValue .rsi).toNat ≤ (s.regValue .rsi).toNat + offset
    omega
  · rw [ho]
    change (s.regValue .rsi).toNat + offset + len ≤ (s.regValue .rsi).toNat + 32
    omega

end P256.Proofs.Projective.Multiply.Machine.Lookup.Select
