import P256.Proofs.Sec1.SquareRoot.Exponent.SquareFour.RoundPrepare
import P256.Proofs.Sec1.SquareRoot.Exponent.SquareFour.RoundSemantics

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.SquareFour

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem prepare_agrees_broad {s t : RamState} {base : BitVec 64}
    (h : AgreesExcept (roundPrepareComponents base) s t) :
    AgreesExcept (components base) s t := by
  refine ⟨?_, ?_, h.rest, h.grow⟩
  · intro c hn hm
    apply h.agree c _ hm
    intro hc
    apply hn
    simp only [roundPrepareComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    all_goals try contradiction
    all_goals simp [components]
  · intro address hn
    apply h.memory address
    intro c hc hcover
    simp only [roundPrepareComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    all_goals try exact False.elim hcover
    all_goals obtain ⟨i, hi, rfl⟩ := hcover
    all_goals rw [BitVec.add_assoc, BitVec.ofNat_eq_ofNat, ← BitVec.ofNat_add] at hn
    · obtain ⟨d, hd, hv⟩ := offset_covers (base := base) (i := 0x10+i) (by unfold scratchOffset; omega)
      exact hn d hd hv
    · obtain ⟨d, hd, hv⟩ := offset_covers (base := base) (i := 0x18+i) (by unfold scratchOffset; omega)
      exact hn d hd hv
    · obtain ⟨d, hd, hv⟩ := offset_covers (base := base) (i := 0x20+i) (by unfold scratchOffset; omega)
      exact hn d hd hv
    · obtain ⟨d, hd, hv⟩ := offset_covers (base := base) (i := 0x28+i) (by unfold scratchOffset; omega)
      exact hn d hd hv

theorem prepare_read {s t : RamState} {base : BitVec 64} {offset n : Nat}
    (h : AgreesExcept (roundPrepareComponents base) s t)
    (hbound : offset + n/8 ≤ 2^64)
    (hapart : offset + n/8 ≤ 0x10 ∨ 0x30 ≤ offset) :
    (Operand.mem (base + BitVec.ofNat 64 offset) : Operand n).read t =
      (Operand.mem (base + BitVec.ofNat 64 offset) : Operand n).read s := by
  apply P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees h
  intro i hi c hc hcover
  simp only [roundPrepareComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  all_goals try exact False.elim hcover
  all_goals obtain ⟨j, hj, he⟩ := hcover
  · exact (RangeApart.offsets base (a := 0x10) (b := offset) (by decide) hbound
      (by omega)) j hj i hi he.symm
  · exact (RangeApart.offsets base (a := 0x18) (b := offset) (by decide) hbound
      (by omega)) j hj i hi he.symm
  · exact (RangeApart.offsets base (a := 0x20) (b := offset) (by decide) hbound
      (by omega)) j hj i hi he.symm
  · exact (RangeApart.offsets base (a := 0x28) (b := offset) (by decide) hbound
      (by omega)) j hj i hi he.symm

theorem prepare_square [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {x k : Nat} {a : Vector (BitVec 64) 4}
    (ctx : ExponentPre s boundary x) (frame : ExponentFrame s t)
    (constants : ExponentConstants s t x) (hip : t.RIP = 0x115510)
    (hcounter : t.regValue .rax = BitVec.ofNat 64 k)
    (hwords : ReverseWordsAt t (exponentFrameBase s) a) :
    ∃ u, Advances boundary 17 t u ∧ ExponentFrame s u ∧ ExponentConstants s u x ∧
      u.RIP = 0x115550 ∧ AccumulatorAt u ⟨0, 0, ⟨0, 0, 0, 0, false⟩⟩ ∧
      u.regValue .r13 = 0 ∧ u.regValue .r14 = 0 ∧
      u.regValue .r11 = t.regValue .r11 ∧ u.regValue .rbx = t.regValue .rbx ∧ u.regValue .r12 = t.regValue .r12 ∧
      (∀ i : Fin 4, (Operand.mem (exponentFrameBase s + 0x10 +
        BitVec.ofNat 64 (8*i.val)) : Operand 64).read u = a[i]) ∧
      ReverseWordsAt u (exponentFrameBase s) a ∧
      (Operand.mem (exponentFrameBase s + 0x7c) : Operand 32).read u = BitVec.ofNat 32 k ∧
      (Operand.mem (exponentFrameBase s + 0x2d0) : Operand 64).read u =
        (Operand.mem (exponentFrameBase s + 0x2d0) : Operand 64).read t ∧
      AgreesExcept (components (exponentFrameBase s)) t u := by
  obtain ⟨v, ha1, hf1, hi1, hcounter1, hs1⟩ := save_counter ctx frame hip
  have hb1 := store_agrees (offset := 0x7c) hs1 (by unfold scratchOffset; omega)
  have hc1 := constants_of_agrees ctx constants hb1
  have hw1 : ReverseWordsAt v (exponentFrameBase s) a := by
    refine ⟨?_,?_,?_,?_⟩
    · have keep := word_of_store32_apart (base := exponentFrameBase s)
        (a := 0x7c) (b := 0x68) hs1 (by unfold OffsetsApart; decide +kernel)
      exact keep.trans hwords.1
    · have keep := word_of_store32_apart (base := exponentFrameBase s)
        (a := 0x7c) (b := 0x60) hs1 (by unfold OffsetsApart; decide +kernel)
      exact keep.trans hwords.2.1
    · have keep := word_of_store32_apart (base := exponentFrameBase s)
        (a := 0x7c) (b := 0x58) hs1 (by unfold OffsetsApart; decide +kernel)
      exact keep.trans hwords.2.2.1
    · have keep := word_of_store32_apart (base := exponentFrameBase s)
        (a := 0x7c) (b := 0x50) hs1 (by unfold OffsetsApart; decide +kernel)
      exact keep.trans hwords.2.2.2
  obtain ⟨u, ha2, hf2, hi2, hz2, h0, h1, h2, h3, hs2⟩ := prepare_round ctx hf1 hi1
  have hb2 := prepare_agrees_broad hs2
  have hlow : (Operand.reg 0 : Operand 32).read t = BitVec.ofNat 32 k := by
    change (t.regValue .rax).setWidth 32 = _
    rw [hcounter, BitVec.setWidth_ofNat_of_le (by decide)]
  refine ⟨u, ha1.trans ha2, hf2, constants_of_agrees ctx hc1 hb2, hi2,
    ⟨hz2 1 (by simp), hz2 5 (by simp), hz2 8 (by simp), hz2 9 (by simp), hz2 15 (by simp)⟩,
    hz2 13 (by simp), hz2 14 (by simp), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hs2.read (n := 64) (r := 11) (by simp [roundPrepareComponents])).trans
      (hs1.read (n := 64) (r := 11) (by simp))
  · exact (hs2.read (n := 64) (r := 3) (by simp [roundPrepareComponents])).trans
      (hs1.read (n := 64) (r := 3) (by simp))
  · exact (hs2.read (n := 64) (r := 12) (by simp [roundPrepareComponents])).trans
      (hs1.read (n := 64) (r := 12) (by simp))
  · intro i
    have hi : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by omega
    rcases hi with hi | hi | hi | hi
    · have he : i = 0 := Fin.ext hi
      subst i
      change (Operand.mem (exponentFrameBase s + 0x10 + 0#64) : Operand 64).read u = _
      rw [BitVec.add_zero]
      exact h0.trans hw1.1
    · have he : i = 1 := Fin.ext hi
      subst i
      change (Operand.mem (exponentFrameBase s + 0x10 + 8) : Operand 64).read u = _
      rw [BitVec.add_assoc]
      exact h1.trans hw1.2.1
    · have he : i = 2 := Fin.ext hi
      subst i
      change (Operand.mem (exponentFrameBase s + 0x10 + 16) : Operand 64).read u = _
      rw [BitVec.add_assoc]
      exact h2.trans hw1.2.2.1
    · have he : i = 3 := Fin.ext hi
      subst i
      change (Operand.mem (exponentFrameBase s + 0x10 + 24) : Operand 64).read u = _
      rw [BitVec.add_assoc]
      exact h3.trans hw1.2.2.2
  · rcases hw1 with ⟨hw0, hw1, hw2, hw3⟩
    exact ⟨(prepare_read hs2 (offset := 0x68) (by decide) (.inr (by decide))).trans hw0,
      (prepare_read hs2 (offset := 0x60) (by decide) (.inr (by decide))).trans hw1,
      (prepare_read hs2 (offset := 0x58) (by decide) (.inr (by decide))).trans hw2,
      (prepare_read hs2 (offset := 0x50) (by decide) (.inr (by decide))).trans hw3⟩
  · exact (prepare_read hs2 (offset := 0x7c) (n := 32) (by decide) (.inr (by decide))).trans
      (hcounter1.trans hlow)
  · exact (prepare_read hs2 (offset := 0x2d0) (n := 64) (by decide) (.inr (by decide))).trans
      (word_of_store32_apart hs1 (by unfold OffsetsApart; decide +kernel))
  · exact (hb1.trans hb2).mono (fun _ hc => (List.mem_append.mp hc).elim id id)

end P256.Proofs.Sec1.SquareRoot.SquareFour
