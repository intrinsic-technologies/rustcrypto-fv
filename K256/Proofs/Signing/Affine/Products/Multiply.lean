import K256.Proofs.Signing.Affine.Products.Schedule
import K256.Proofs.Generate.Generator.Affine.Products.Multiply.Return
import K256.Proofs.Signing.Affine.Products.Frame

namespace K256.Proofs.Signing.Affine

open K256.Proofs.Generate.Generator.Affine
open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Generate.LIR
open Standards.SECG.ECC

local macro "product_outside" : tactic =>
  `(tactic| (simp (disch := decide) only [Outside, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Nat.reduceDiv, Nat.reduceMul, $(Lean.mkIdent `sub):ident,
    $(Lean.mkIdent `add):ident, BitVec.reduceToNat] <;> omega))

local macro "product_within" : tactic =>
  `(tactic| (simp (disch := decide) [RegionsWithin, List.mem_cons,
    $(Lean.mkIdent `sub):ident, $(Lean.mkIdent `add):ident, BitVec.reduceToNat] <;> omega))

theorem finishCoordinateProducts {fr : Activation} {a b : Registers} {m n : Ram} {x y z : Fin modulus}
    {xl yl w : Limbs} (h : ProductInput fr a m x y z) (nz : z.val ≠ 0)
    (productsIn : ProductNormalizeInput (fr.rsp - 520) b n (mulWords xl w) (mulWords yl w))
    (slots : ProductSlots (fr.rsp - 520) n fr.rdi (fr.rsp - 520 + 376) fr.rsi 1)
    (kept : ∀ j : Fin Reg.count, j.val ∈ [22,39,50,51] → b[j] = a[j])
    (frame : RamWriteFrame m n [⟨(fr.rsp - 520 - 8).toNat, 288⟩])
    (hx : FieldRepr xl x 8) (hy : FieldRepr yl y 8) (hw : FieldRepr w (inverse z) 8) :
    ∃ o, program.Exec (dialect Extracted.programImage)
        ⟨⟨.l114930, b, n⟩, [productNormalizeReturn .l10ecb2 0x10ecb2]⟩ o ∧
      o.tag = some ⟨64, 0x10ee37⟩ ∧ CallState .l10ee37 fr o.values o.store ∧
      Products fr o.values o.store (toAffine x y z) := by
  let sp := fr.rsp - 520
  change ProductNormalizeInput sp b n _ _ at productsIn
  change ProductSlots sp n _ (sp + 376) _ _ at slots
  change RamWriteFrame m n [⟨(sp - 8).toNat, 288⟩] at frame
  have parent := h.parent
  obtain ⟨r4, df, bx, r14, mx, ft, fc, _, _, _, _, _, _, _, _, _, win, size, align, _⟩ := parent.atoms
  change Writable Extracted.programImage m (fr.rsp - 976) 976 at win
  change fr.low.toNat + 976 ≤ fr.rsp.toNat at size
  change fr.rsp.toNat % 16 = 8 at align
  have low : sp.toNat = fr.rsp.toNat - 520 := BitVec.toNat_sub_of_le (by change 520 ≤ fr.rsp.toNat; omega)
  have highFr := parent.source.low
  have srcAbove := parent.srcAbove
  have room : 121 ≤ sp.toNat := by omega
  have high : sp.toNat + 464 ≤ 2^32 := by omega
  have asp : sp.toNat % 16 = 0 := by omega
  have sub (k : Word) (hk : k.toNat ≤ 121) : (sp - k).toNat = sp.toNat - k.toNat :=
    BitVec.toNat_sub_of_le (by change k.toNat ≤ sp.toNat; omega)
  have add (k : Word) (hk : k.toNat ≤ 464) : (sp + k).toNat = sp.toNat + k.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have winLow : (fr.rsp - 976).toNat = fr.rsp.toNat - 976 :=
    BitVec.toNat_sub_of_le (by change 976 ≤ fr.rsp.toNat; omega)
  have winN : Writable Extracted.programImage n (sp - 121) 585 := (win.of_frame frame).sub
    (by rw [sub _ (by decide)]; change _ ≤ sp.toNat - 121; omega)
    (by rw [sub _ (by decide)]; change sp.toNat - 121 + 585 ≤ _; omega)
  obtain ⟨o₁, run₁, tag₁, sp₁, kept₁, wr₁, xAt⟩ := normalizeProductAt
    (i := 0) (Or.inl rfl) winN room high asp productsIn.rsp productsIn.src productsIn.dst
    productsIn.df productsIn.saved productsIn.slot (by decide) productsIn.xAt
  change RamWriteFrame n o₁.store [⟨(sp - 121).toNat, 113⟩, ⟨(sp + 376).toNat, 40⟩] at wr₁
  change WordsAt o₁.store (sp + 376) 64 _ at xAt
  have bx₁ := (kept₁ 3 (by decide)).trans productsIn.base
  have win₁ := winN.of_frame wr₁
  obtain ⟨c, call₂, sp₂, src₂, dst₂, keptC⟩ := secondNormalizeEntry (sp := sp) (m := o₁.store)
    (congrArg (Value.get 64) sp₁) (congrArg (Value.get 64) bx₁) (by slot_state region)
  let n₂ := memStore o₁.store (sp - 8) (0x10ecc3 : Word)
  have push : RamWriteFrame o₁.store n₂ [⟨(sp - 8).toNat, 8⟩] :=
    (RamWriteFrame.refl _ _).memStore _ ⟨_, List.mem_singleton_self _, Nat.le_refl _, Nat.le_refl _,
      by change (sp - 8).toNat + 8 ≤ 2^64; rw [sub _ (by decide)]; change sp.toNat - 8 + 8 ≤ _; omega⟩
  have y₁ := productsIn.yAt.of_frame wr₁ (by decide) (by product_outside)
  have y₂ := y₁.of_frame push (by decide) (by product_outside)
  have saved₂ (j : Fin Reg.count) (hj : j.val ∈ [3,5,12,13,14,15]) :
      c[j] = ⟨64, c[j].get 64⟩ := by
    have incl : j.val ∈ [3,5,12,13,14,15,22,39,50,51] :=
      (by decide : [3,5,12,13,14,15] ⊆ [3,5,12,13,14,15,22,39,50,51]) hj
    rw [keptC j incl, kept₁ j incl]
    exact productsIn.saved j hj
  have win₂ := win₁.of_frame push
  obtain ⟨o₂, run₂, tag₂, sp₃, kept₂, wr₂, yAt⟩ := normalizeProductAt (i := 40)
    (Or.inr rfl) win₂ room high asp sp₂ src₂ dst₂
    ((keptC 22 (by decide)).trans ((kept₁ 22 (by decide)).trans productsIn.df)) saved₂
    (memLoad_memStore_same o₁.store (sp - 8) (0x10ecc3 : Word) (by decide) (by decide))
    (by decide) y₂
  change RamWriteFrame n₂ o₂.store [⟨(sp - 121).toNat, 113⟩, ⟨(sp + 416).toNat, 40⟩] at wr₂
  change WordsAt o₂.store (sp + 416) 64 _ at yAt
  let rs : List MemoryRegion := [⟨(sp - 121).toNat, 121⟩, ⟨(sp + 376).toNat, 81⟩]
  have wrote : RamWriteFrame n o₂.store rs := (((RamWriteFrame.refl n rs).trans wr₁
    (by dsimp only [rs]; product_within)).trans push (by dsimp only [rs]; product_within)).trans wr₂ (by dsimp only [rs]; product_within)
  have same (k : Word) (lo : 232 ≤ k.toNat) (hi : k.toNat ≤ 280) :
      memLoad o₂.store (sp + k) 64 = memLoad n (sp + k) 64 := by
    apply wrote.memLoad_eq
    dsimp only [rs]
    simp only [Outside, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      Nat.reduceDiv, add _ (by decide : (376 : Word).toNat ≤ 464),
      sub _ (by decide : (121 : Word).toNat ≤ 121), add k (by omega), BitVec.reduceToNat]
    omega
  have bx₂ := (kept₂ 3 (by decide)).trans ((keptC 3 (by decide)).trans bx₁)
  have win₃ := win₂.of_frame wr₂
  obtain ⟨o, finish, tag, st, spOut, bxOut, r12Out, r14Out, r15Out, keptOut⟩ := productReturnBlock (sp := sp) (m := o₂.store)
    (congrArg (Value.get 64) sp₃) (congrArg (Value.get 64) bx₂)
    (by slot_state region) ((same _ (by decide) (by decide)).trans slots.retAt)
  have flagWrite : RamWriteFrame o₂.store o.store [⟨(sp + 456).toNat, 1⟩] := by
    rw [st]
    exact (RamWriteFrame.refl _ _).memStore _ ⟨_, List.mem_singleton_self _, Nat.le_refl _, Nat.le_refl _,
      by rw [add _ (by decide)]; change sp.toNat + 456 + 1 ≤ _; omega⟩
  have wsX := ((xAt.of_frame push (by decide) (by product_outside)).of_frame wr₂ (by decide)
    (by product_outside)).of_frame flagWrite (by decide) (by product_outside)
  have wsY := yAt.of_frame flagWrite (by decide) (by product_outside)
  have flag : memLoad o.store (sp + 456) 8 = 0 := by
    rw [st, memLoad_memStore_same _ _ _ (by decide) (by decide)]
  have addr : sp + 376 = fr.rsp - 144 := by dsimp [sp]; bv_omega
  have key := publicKeyAt_of_products (point := toAffine x y z) (x := x) (y := y) (z := z)
    rfl (by simp [toAffine, nz]) (base := sp + 376) wsX
    (by simpa only [Lift.reduceAddOffset] using wsY)
    (by simpa only [Lift.reduceAddOffset] using flag)
    (normalizedProduct_repr hx hw) (normalizedProduct_repr hy hw)
  rw [addr] at key
  let total : List MemoryRegion := [⟨(sp - 121).toNat, 578⟩]
  have broad : RamWriteFrame m o.store total :=
    (((RamWriteFrame.refl m total).trans frame (by dsimp only [total]; product_within)).trans wrote
      (by dsimp only [total, rs]; product_within)).trans flagWrite (by dsimp only [total]; product_within)
  have preserved (j : Fin Reg.count) (hj : j.val ∈ [22,39,50,51]) :
      o.values[j] = (a.set 4 ⟨64, fr.rsp - 232⟩)[j] := by
    have incl : j.val ∈ [3,5,12,13,14,15,22,39,50,51] :=
      (by decide : [22,39,50,51] ⊆ [3,5,12,13,14,15,22,39,50,51]) hj
    have ne : 4 ≠ j.val := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      omega
    simp only [Fin.getElem_fin, Vector.getElem_set_ne _ _ ne]
    exact (keptOut j hj).trans ((kept₂ j incl).trans ((keptC j incl).trans
      ((kept₁ j incl).trans (kept j hj))))
  have state := parent.afterProductScratch (b := o.values) (show Atom.All Extracted.programImage _ _ (Fn10fe50.frameAt .l10eda1 fr) from parent.atoms) (l' := .l10ee37) rfl broad (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    dsimp only
    rw [sub _ (by decide)]
    change fr.rsp.toNat - 976 ≤ sp.toNat - 121 ∧ sp.toNat - 121 + 578 ≤ fr.rsp.toNat - 48
    omega) (by
    intro j hj
    rcases j with ⟨j, hj'⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · change o.values[4] = _
      rw [spOut]
      simp only [Fin.getElem_fin, Vector.getElem_set_self]
      change (⟨64, sp + 288⟩ : Value) = ⟨64, fr.rsp - 232⟩
      congr 1
      dsimp [sp]
      bv_omega
    · exact preserved 22 (by decide)
    · exact bxOut.trans ((congrArg (Value.mk 64) ((same 232 (by decide) (by decide)).trans slots.rbxAt)).trans bx.symm)
    · exact r14Out.trans ((congrArg (Value.mk 64) ((same 256 (by decide) (by decide)).trans slots.r14At)).trans r14.symm)
    · exact preserved 39 (by decide)
    · exact preserved 50 (by decide)
    · exact preserved 51 (by decide))
  refine ⟨o, ?_, tag, state, ?_, ?_, key⟩
  · have first := ParseSignature.exec_reaches_resume run₁ (productNormalizeReturn .l10ecb2 0x10ecb2) []
      (by rw [tag₁]; rfl)
    apply Program.Exec.of_sem
    apply first.exec
    apply Program.Exec.sem
    apply ParseSignature.exec_call call₂ run₂ (by rw [tag₂]; rfl)
    exact finish
  · rw [r12Out, same 240 (by decide) (by decide), slots.r12At, addr]
  · rw [r15Out, same 264 (by decide) (by decide), slots.r15At]

theorem multiplyPoint {fr : Activation} {a : Registers} {m : Ram} {x y z : Fin modulus}
    (h : ProductInput fr a m x y z) (nz : z.val ≠ 0) :
    ∃ o, program.Exec (dialect Extracted.programImage) ⟨⟨.l10e4c0, a, m⟩, []⟩ o ∧
      o.tag = some ⟨64, 0x10ee37⟩ ∧ CallState .l10ee37 fr o.values o.store ∧
      Products fr o.values o.store (toAffine x y z) := by
  obtain ⟨b, n, xl, yl, w, call, productsIn, slots, kept, frame, hx, hy, hw⟩ := coordinateProductBlock h
  obtain ⟨o, finish, post⟩ := finishCoordinateProducts h nz productsIn slots kept frame hx hy hw
  exact ⟨o, .next (by simp only [Program.step, call, Transfer.next]) finish, post⟩

end K256.Proofs.Signing.Affine
