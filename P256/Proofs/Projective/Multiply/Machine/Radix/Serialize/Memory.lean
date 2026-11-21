import P256.Proofs.Program.Code
import P256.Proofs.Projective.Multiply.Machine.Radix.Serialize.Load
import P256.Proofs.Projective.Multiply.Machine.Radix.Serialize.Store
import P256.Proofs.Program.Copy.Return
import P256.Proofs.Projective.Multiply.Machine.Radix.Serialize.Encoding
import P256.Proofs.SecretKeyFromBytes.Scalar.Representation

set_option autoImplicit false

open P256.Proofs.Program (CalleePre inProgram_of_textOffset memoryRegion_contains_add)

namespace P256.Proofs.Projective.Multiply.Machine.Radix.Serialize

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [Bindings] {s t : RamState} {boundary : ReturnBoundary} {reserve : Nat}

theorem input_readable (pre : CalleePre s boundary 0x112ea0 32 32 reserve)
    {off len : Nat} (within : off + len ≤ 32) :
    MemReadable s (s.regValue .rsi + BitVec.ofNat 64 off) len := by
  have low : (s.regValue .rsi).toNat + 32 < 2^32 := pre.inputBounded
  refine ⟨?_, ?_⟩
  · rw [toNat_add_ofNat _ _ (by omega)]
    omega
  · intro i hi
    rw [add_ofNat_add_ofNat]
    exact Option.isSome_iff_exists.mpr (pre.inputAllocated _
      (memoryRegion_contains_add (len := 32) (i := off + i) pre.inputBounded
        (Nat.le_refl _) (Nat.le_refl _) (by omega)))

theorem load_pre (pre : CalleePre s boundary 0x112ea0 32 32 reserve) : LoadPre s := by
  refine ⟨pre.rip, ?_⟩
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  all_goals exact input_readable pre (by decide)

theorem output_contains (pre : CalleePre s boundary 0x112ea0 32 32 reserve)
    {i : Nat} (hi : i < 32) :
    (registerRegion s .rdi 32).Contains (s.regValue .rdi + BitVec.ofNat 64 i).toNat :=
  memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) hi

theorem output_readable (pre : CalleePre s boundary 0x112ea0 32 32 reserve)
    (allocated : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome)
    {off len : Nat} (within : off + len ≤ 32) :
    MemReadable t (s.regValue .rdi + BitVec.ofNat 64 off) len := by
  have low : (s.regValue .rdi).toNat + 32 < 2^32 := pre.outputBounded
  refine ⟨?_, ?_⟩
  · rw [toNat_add_ofNat _ _ (by omega)]
    omega
  · intro i hi
    rw [add_ofNat_add_ofNat]
    exact allocated _ (Option.isSome_iff_exists.mpr
      (pre.outputAllocated _ (output_contains pre (by omega))))

theorem output_writable (pre : CalleePre s boundary 0x112ea0 32 32 reserve)
    (allocated : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome)
    {off len : Nat} (within : off + len ≤ 32) (positive : 0 < len) :
    P256.Proofs.Common.Instructions.CrossPageStore.Writable t (s.regValue .rdi + BitVec.ofNat 64 off) len := by
  refine ⟨output_readable pre allocated within,
    tables_of_not_reserved positive (output_readable pre allocated within).low ?_⟩
  intro i hi hin
  apply pre.avoids (registerRegion s .rdi 32) (by simp) _ _ (.inr hin)
  rw [add_ofNat_add_ofNat]
  exact output_contains pre (by omega)

theorem output_code_apart (pre : CalleePre s boundary 0x112ea0 32 32 reserve)
    {off len pc n : Nat} (within : off + len ≤ 32) (code : pc + n ≤ 118431) :
    RangeApart (s.regValue .rdi + BitVec.ofNat 64 off) len
      (Extracted.textAddress + BitVec.ofNat 64 pc) n := by
  intro i hi j hj he
  apply pre.avoids (registerRegion s .rdi 32) (by simp)
    (s.regValue .rdi + BitVec.ofNat 64 off + BitVec.ofNat 64 i) _ (.inl ?_)
  · rw [add_ofNat_add_ofNat]
    exact output_contains pre (by omega)
  · rw [he, add_ofNat_add_ofNat]
    exact inProgram_of_textOffset (pc + j) (by omega)

theorem store_pre (pre : CalleePre s boundary 0x112ea0 32 32 reserve)
    (loaded : (loadEffect s).Holds s t) : StorePre t := by
  have pointer : t.regValue .rax = s.regValue .rdi := loaded.writes.2.2.1
  refine ⟨loaded.rip, ?_, ?_⟩
  · intro i hi
    change P256.Proofs.Common.Instructions.CrossPageStore.Writable t (t.regValue .rax + i) 8
    rw [pointer]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    all_goals exact output_writable pre loaded.agrees.grow (by decide) (by decide)
  · intro i hi pc n code
    change RangeApart (t.regValue .rax + i) 8 _ n
    rw [pointer]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    all_goals exact output_code_apart pre (by decide) code

end P256.Proofs.Projective.Multiply.Machine.Radix.Serialize
