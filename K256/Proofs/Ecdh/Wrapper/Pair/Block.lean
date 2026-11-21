import K256.Proofs.Ecdh.Wrapper.AffineCall
import K256.Proofs.Generate.Generator.Multiply.Prepare.Bases.Negate.Machine
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Ecdh.Wrapper.Pair

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine Ecdh.LIR
  Generate.Generator.Multiply.Prepare.Bases.Negate

set_option maxRecDepth 4096 in
set_option maxHeartbeats 850000 in
theorem setup {a : Values Value Reg.count} {m : Ram} {sp : BitVec 64} {w : Vector (BitVec 64) 4}
    (rsp : a[4].get 64 = sp) (src : a[15].get 64 = sp + 344)
    (win : Writable Extracted.programImage m (sp - 3936) 10088)
    (words : WordsAt m (sp + 16) 64 w)
    (push : StoreOk Extracted.programImage (storeFour m (sp + 464) w) (sp - 8) 8 0x1018ad 3)
    (r8 : a[8].width = 64) (r9 : a[9].width = 64) :
    ∃ b : Values Value Reg.count, program.runBlock (dialect Extracted.programImage) ⟨.l10185f, a, m⟩ =
      .call ⟨.l12a820, b, memStore (storeFour m (sp + 464) w) (sp - 8) (0x1018b0 : BitVec 64)⟩
        (callFrame .l1018b0 0x1018b0) ∧ b[4].get 64 = sp - 8 ∧ b[7].get 64 = sp + 192 ∧
      b[6].get 64 = sp + 344 ∧ b[2].get 64 = 152 ∧ b[13] = ⟨64, 0x12a820⟩ ∧
      b[14] = ⟨64, sp + 192⟩ ∧ ParseSignature.ArgumentWidths b ∧
      ∀ i : Fin Reg.count, i.val ∈ [3, 5, 8, 9, 12, 15, 22, 39, 50, 51] → b[i] = a[i] := by
  have w0 := words 0 (by decide)
  have w1 := words 1 (by decide)
  have w2 := words 2 (by decide)
  have w3 := words 3 (by decide)
  simp only [wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
    BitVec.reduceAdd] at w0 w1 w2 w3
  change memLoad m (sp + 16) 64 = w[0] at w0
  change memLoad m (sp + 24) 64 = w[1] at w1
  change memLoad m (sp + 32) 64 = w[2] at w2
  change memLoad m (sp + 40) 64 = w[3] at w3
  simp only [storeFour, BitVec.add_assoc, BitVec.reduceAdd] at push ⊢
  refine ⟨?_, ?run, ?post⟩
  case run =>
    cfg_eval [rsp, src]
    segment_words [w0, w1, w2, w3]
    iterate 8 (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l10185f)
    refine Eq.trans (ite_eq_left push) ?_
    rfl
  case post =>
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
    · rintro ⟨i, hi⟩ h
      simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> first | rfl | exact r8 | exact r9
    · rintro ⟨i, hi⟩ h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

end K256.Proofs.Ecdh.Wrapper.Pair
