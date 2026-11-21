import P256.Proofs.HMAC.Key.State
import P256.Proofs.Program.ScalarFrame.Memory
import P256.Proofs.Program.Entry
import X86Proofs.Program.Compose

set_option autoImplicit false

namespace P256.Proofs.HMAC.Key

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

variable [Bindings] {s t : RamState} {boundary : ReturnBoundary} {key : ByteArray}

theorem stack_writes (pre : Pre s boundary key) :
    WritesWithin (stackComponents s) #v[Stack.region s 384] := by
  intro c hc address cover
  simp only [stackComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact cover.elim
  exact ⟨Stack.region s 384, by simp,
    ScalarFrame.stack_contains pre.toCalleePre (offset := 384) (by decide) (by decide) cover⟩

theorem stack_loaded (pre : Pre s boundary key)
    (agrees : AgreesExcept (stackComponents s) s t) : ProgramLoaded t := by
  have memory := agrees.memoryWriteFrame (stack_writes pre)
  intro a b fetch
  rw [memory a]
  · exact pre.loaded a b fetch
  · intro region hr ha
    have eq : region = Stack.region s 384 := by simpa using hr
    subst region
    exact pre.avoids _ (by simp) a ha (.inl ⟨b, fetch⟩)

theorem stack_input (pre : Pre s boundary key)
    (agrees : AgreesExcept (stackComponents s) s t) :
    (registerRegion s .rsi key.size).HasBytes t.external key := by
  refine ⟨pre.input.1, ?_⟩
  intro i
  have hb := pre.input.2 i
  change t.external[BitVec.ofNat 64 ((s.regValue .rsi).toNat + i.val)]? = _
  change s.external[BitVec.ofNat 64 ((s.regValue .rsi).toNat + i.val)]? = _ at hb
  simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hb ⊢
  refine (agrees.memoryWriteFrame (stack_writes pre) _ ?_).trans hb
  intro region hr
  have eq : region = Stack.region s 384 := by simpa using hr
  subst region
  exact pre.separation 0 2 (by decide) _
    (memoryRegion_contains_add pre.inputBounded (Nat.le_refl _) (Nat.le_refl _) i.isLt)

omit [Bindings] in
theorem stack_return_word (agrees : AgreesExcept (stackComponents s) s t) :
    memLoad t.external (stackPtr s) 64 = memLoad s.external (stackPtr s) 64 := by
  apply memLoad_congr
  intro i hi
  change (t.external[_]?).getD 0 = (s.external[_]?).getD 0
  congr 1
  apply agrees.byte
  intro c hc cover
  simp only [stackComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact cover.elim
  obtain ⟨j, hj, eq⟩ := cover
  apply OffsetsApart.ne (c₁ := -384) (c₂ := 0#64) (len₁ := 384) (len₂ := 8)
    (by unfold OffsetsApart; decide +kernel) (stackPtr s) hj hi (by decide)
  simpa only [BitVec.sub_eq_add_neg, BitVec.add_zero] using eq.symm

theorem stack_code_apart {entry : BitVec 64} {inputBytes outputBytes reserve : Nat}
    (pre : CalleePre s boundary entry inputBytes outputBytes reserve)
    {offset len codeOffset codeLen : Nat}
    (hoff : offset ≤ reserve) (hlen : len ≤ offset + 8)
    (hcode : codeOffset + codeLen ≤ 118431) :
    RangeApart (stackPtr s - BitVec.ofNat 64 offset) len
      (Extracted.textAddress + BitVec.ofNat 64 codeOffset) codeLen := by
  intro i hi j hj he
  apply pre.avoids (Stack.region s reserve) (by simp) _
    (ScalarFrame.stack_contains pre hoff hlen ⟨i, hi, rfl⟩) (.inl ?_)
  rw [he, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact inProgram_of_textOffset (codeOffset + j) (by omega)

end P256.Proofs.HMAC.Key
