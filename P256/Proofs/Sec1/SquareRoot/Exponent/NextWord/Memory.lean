import P256.Proofs.Sec1.SquareRoot.Exponent.ReadDigit.State
import P256.Proofs.Program.ScalarFrame.Input
import P256.Proofs.Field.Preserve

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open P256.Proofs.Program X86 X86.Machine X86.UserProcess X86Proofs

namespace NextWord

theorem byte_of_store {t u : RamState} {base : BitVec 64} {offset len i : Nat}
    (ha : AgreesExcept [.mem (base + 0x2c0) 8, .rip] t u)
    (hapart : RangeApart (base + 0x2c0) 8 (base + BitVec.ofNat 64 offset) len)
    (hi : i < len) :
    u.external[base + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      t.external[base + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  apply ha.memory
  intro c hc hcover
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · obtain ⟨j, hj, he⟩ := hcover
    exact hapart j hj i hi he.symm
  · exact hcover

theorem word_of_store {s t u : RamState} {offset n : Nat} {value : BitVec n}
    (ha : AgreesExcept [.mem (exponentFrameBase s + 0x2c0) 8, .rip] t u)
    (hv : (Operand.mem (exponentFrameBase s + BitVec.ofNat 64 offset) : Operand n).read t = value)
    (hbound : offset + n / 8 ≤ 2^64) (hapart : offset + n / 8 ≤ 0x2c0 ∨ 0x2c8 ≤ offset) :
    (Operand.mem (exponentFrameBase s + BitVec.ofNat 64 offset) : Operand n).read u = value := by
  apply Eq.trans _ hv
  apply memLoad_congr
  intro i hi
  exact congrArg (fun a : Option UInt8 => a.getD 0)
    (byte_of_store ha (RangeApart.offsets _ (by decide) hbound hapart.symm) hi)

theorem frame_of_store [Bindings] {s t u : RamState} {boundary : ReturnBoundary} {x : Nat}
    (ctx : ExponentPre s boundary x) (hf : ExponentFrame s t) (hr : ReadyToStep u)
    (ha : AgreesExcept [.mem (exponentFrameBase s + 0x2c0) 8, .rip] t u) :
    ExponentFrame s u := by
  apply ExponentFrame.of_scalarFrame
  · apply hf.scalarFrame.after_effect ctx.toCalleePre (by decide) hr ha _ (by simp)
    intro c hc a hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · refine ⟨ScalarFrame.workRegion s 1584, by simp, ?_⟩
      have haddr : exponentFrameBase s + 0x2c0 = stackPtr s - 712 := by
        simp only [exponentFrameBase, stackPtr, BitVec.sub_eq_add_neg, BitVec.add_assoc]
        rfl
      rw [haddr] at hin
      exact ScalarFrame.work_contains ctx.toCalleePre (by decide) (by decide) hin
    · exact hin.elim
  · exact word_of_store ha hf.outputPointer (by decide) (.inl (by decide))

end NextWord

theorem ExponentConstants.of_savedWord_store [Bindings] {s t u : RamState}
    {boundary : ReturnBoundary} {x : Nat}
    (ctx : ExponentPre s boundary x) (hc : ExponentConstants s t x)
    (hf : ExponentFrame s u)
    (ha : AgreesExcept [.mem (exponentFrameBase s + 0x2c0) 8, .rip] t u) :
    ExponentConstants s u x := by
  have inputBytes {i : Nat} (hi : i < 144) :
      u.external[s.regValue .rsi + BitVec.ofNat 64 i]? =
        s.external[s.regValue .rsi + BitVec.ofNat 64 i]? := by
    apply frame_read hf.frame _
      (memoryRegion_contains_add ctx.inputBounded (Nat.le_refl _) (Nat.le_refl _) hi)
    intro region hr
    have cases : region = registerRegion s .rdi 32 ∨ region = Stack.region s 1584 := by
      simpa using hr
    rcases cases with rfl | rfl
    · exact ctx.separation (0 : Fin 3) (1 : Fin 3) (by decide)
    · exact ctx.separation (0 : Fin 3) (2 : Fin 3) (by decide)
  refine ⟨?_, ?_, ?_, ?_,
    NextWord.word_of_store ha hc.modulus0 (by decide) (.inl (by decide)),
    NextWord.word_of_store ha hc.modulus1 (by decide) (.inl (by decide)),
    NextWord.word_of_store ha hc.modulus2 (by decide) (.inl (by decide)),
    NextWord.word_of_store ha hc.modulus3 (by decide) (.inl (by decide)),
    NextWord.word_of_store ha hc.firstWindow (by decide) (.inl (by decide)),
    NextWord.word_of_store ha hc.parameterPointer (by decide) (.inl (by decide)),
    NextWord.word_of_store ha hc.firstWord (by decide) (.inl (by decide)),
    NextWord.word_of_store ha hc.inverse (by decide) (.inr (by decide)),
    NextWord.word_of_store ha hc.initialMask (by decide) (.inr (by decide)),
    NextWord.word_of_store ha hc.negativeInverse (by decide) (.inr (by decide))⟩
  · constructor
    · exact ctx.residue.1.of_bytes_eq (fun i hi => inputBytes (by omega))
    · intro i hi
      have he : s.regValue .rsi + 32 + BitVec.ofNat 64 i =
          s.regValue .rsi + BitVec.ofNat 64 (32+i) := by
        rw [BitVec.ofNat_add, ← BitVec.add_assoc]
        rfl
      change u.external[s.regValue .rsi + 32 + BitVec.ofNat 64 i]? = _
      rw [he, inputBytes (by omega), ← he]
      exact ctx.residue.2 i hi
  · intro i hi
    apply (hc.table i hi).of_bytes_eq
    intro j hj
    have he := NextWord.byte_of_store ha (offset := 0x338 + 32*i) (len := 32)
      (RangeApart.offsets _ (a := 0x2c0) (b := 0x338 + 32*i)
        (by decide) (by omega) (.inl (by omega))) hj
    simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using he
  · refine ⟨hc.exponent.1, ?_⟩
    intro i hi
    exact (NextWord.byte_of_store ha (offset := 0x538) (len := 32)
      (RangeApart.offsets _ (by decide) (by decide) (.inl (by decide))) hi).trans
        (hc.exponent.2 i hi)
  · exact NextWord.word_of_store ha hc.initialWindow (by decide) (.inl (by decide))

theorem NextWord.accumulator_of_store {s t u : RamState} {value : Nat}
    (ha : AgreesExcept [.mem (exponentFrameBase s + 0x2c0) 8, .rip] t u)
    (hv : Field.MontgomeryAt t (exponentFrameBase s + 0x30) value) :
    Field.MontgomeryAt u (exponentFrameBase s + 0x30) value := by
  apply hv.of_bytes_eq
  intro i hi
  exact NextWord.byte_of_store ha
    (RangeApart.offsets _ (by decide) (by decide) (.inr (by decide))) hi

end P256.Proofs.Sec1.SquareRoot
