import P256.Proofs.Field.Inverse.Setup.Parameters
import P256.Proofs.Field.Inverse.Interface
import P256.Proofs.Program.ScalarFrame.Memory

set_option autoImplicit false

namespace P256.Proofs.Field.Inverse

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program

abbrev parameterSource (i : Fin 8) : BitVec 64 :=
  Extracted.textAddress + BitVec.ofNat 64 parameterWords[i].1 + 7 +
    parameterWords[i].2.1.signExtend 64

abbrev parameterOffset (i : Fin 8) : Nat := parameterWords[i].2.2.toNat

theorem parameter_source_inProgram (i : Fin 8) (j : Nat) (bound : j < 8) :
    InProgram (parameterSource i + BitVec.ofNat 64 j) := by
  have mapped : ∀ i : Fin 8, ∀ j : Fin 8,
      (Extracted.programSections.fetchByte (parameterSource i + BitVec.ofNat 64 j.val)).isSome := by
    decide +kernel
  exact Option.isSome_iff_exists.mp (mapped i ⟨j, bound⟩)

theorem parameter_source_readable {t : RamState} (loaded : ProgramLoaded t) (i : Fin 8) :
    MemReadable t (parameterSource i) 8 := by
  refine ⟨?_, ?_⟩
  · have bound : ∀ i : Fin 8, (parameterSource i).toNat + 8 < 2^32 := by decide +kernel
    exact Nat.le_of_lt (bound i)
  · intro j hj
    obtain ⟨b, hb⟩ := parameter_source_inProgram i j hj
    rw [loaded _ _ hb]
    rfl

theorem parameter_stack_writable [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (sp : stackPtr t = stackPtr s - 168)
    (grow : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome)
    {offset : Nat} (bound : offset ≤ 168) (aligned : offset % 8 = 0) :
    MemWritable t (stackPtr t + BitVec.ofNat 64 offset) 8 := by
  rw [ScalarFrame.scalar_stack_address (frameOffset := 168) sp (by decide) bound]
  apply writable_of_grow (stack_sub_writable8 pre.stack ?_ (by omega) ?_) grow
  · intro a ha ht
    exact pre.avoids _ (by simp) a ha (.inr ht)
  · omega

theorem parameter_stack_code [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (sp : stackPtr t = stackPtr s - 168)
    {offset codeOffset len : Nat} (bound : offset ≤ 168)
    (codeBound : codeOffset + len ≤ 118431) :
    RangeApart (stackPtr t + BitVec.ofNat 64 offset) 8
      (Extracted.textAddress + BitVec.ofNat 64 codeOffset) len := by
  intro i hi j hj he
  apply pre.avoids (Stack.region s 880) (by simp)
    (stackPtr t + BitVec.ofNat 64 offset + BitVec.ofNat 64 i)
  · rw [ScalarFrame.scalar_stack_address (frameOffset := 168) sp (by decide) bound]
    exact ScalarFrame.stack_contains pre (by omega) (by omega) ⟨i, hi, rfl⟩
  · apply Or.inl
    rw [he, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact inProgram_of_textOffset (codeOffset+j) (by omega)

theorem parameter_word_pre [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (loaded : ProgramLoaded t)
    (sp : stackPtr t = stackPtr s - 168)
    (grow : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome)
    (i : Fin 8) (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 parameterWords[i].1) :
    RipCopy.Pre (Extracted.textAddress + BitVec.ofNat 64 parameterWords[i].1)
      parameterWords[i].2.1 parameterWords[i].2.2 t := by
  have facts : ∀ i : Fin 8,
      parameterWords[i].2.2.signExtend 64 = BitVec.ofNat 64 (parameterOffset i) ∧
      parameterOffset i ≤ 168 ∧ parameterOffset i % 8 = 0 ∧
      parameterWords[i].1 + 12 ≤ 118431 := by decide +kernel
  refine ⟨rip, parameter_source_readable loaded i, ?_, ?_⟩
  · change MemWritable t (stackPtr t + parameterWords[i].2.2.signExtend 64) 8
    rw [(facts i).1]
    exact parameter_stack_writable pre sp grow (facts i).2.1 (facts i).2.2.1
  · change RangeApart (stackPtr t + parameterWords[i].2.2.signExtend 64) 8 _ 12
    rw [(facts i).1]
    exact parameter_stack_code pre sp (facts i).2.1 (facts i).2.2.2

end P256.Proofs.Field.Inverse
