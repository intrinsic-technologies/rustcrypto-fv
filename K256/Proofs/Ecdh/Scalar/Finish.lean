import K256.Proofs.Ecdh.LIR.Program
import K256.Proofs.Common.Tactic
import K256.Proofs.Ecdh.Decode.Convert.Barrier
import K256.Proofs.Sec1.Serialize.Assemble.Memory

namespace K256.Proofs.Ecdh.Scalar

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open CFG Lift Refine Ecdh.LIR
open Sec1.Serialize.Assemble (wordsAtOffset fourWordsAt)

private abbrev Regs := Values Value Reg.count
private abbrev code := Extracted.programImage

private def resume (label : Label) (ret : BitVec 64) : StackFrame Value Label signature Reg.count :=
  ⟨label, #v[], rfl, some ⟨64, ret⟩⟩

private def saved := [3, 5, 8, 9, 12, 13, 14, 15, 22, 39, 50, 51]

private def Keeps (a b : Regs) :=
  (∀ j : Fin Reg.count, j.val ∈ saved → b[j] = a[j]) ∧
  (a[1].width = 64 → b[1].width = 64) ∧ (a[2].width = 64 → b[2].width = 64)

local macro "preserves_saved" : tactic =>
  `(tactic| (
    refine ⟨?_, by intro h; first | exact h | rfl, by intro h; first | exact h | rfl⟩
    intro ⟨j, hj⟩ h
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h <;> subst j <;> rfl))

private theorem complement {a : Regs} {m : Ram} {sp : BitVec 64}
    (rsp : a[4].get 64 = sp) (al : a[0].get 8 = 0)
    (slot : Writable code m (sp - 8) 8) :
    ∃ b : Regs, program.runBlock (dialect code) ⟨.l101752, a, m⟩ =
        .call ⟨.l127d50, b, memStore m (sp - 8) (0x10175e : BitVec 64)⟩ (resume .l10175e 0x10175e) ∧
      b[4].get 64 = sp - 8 ∧ b[7] = ⟨64, 1⟩ ∧ Keeps a b := by
  have push : StoreOk code m (sp - 8) 8 0x101759 5 :=
    ParseSignature.storeOk_of_codeRange (off := 7) slot
      (fun x hx => Common.fnCode_subset_programImage x (code_l101752 x hx)) (by decide)
  have lo : (a[0].get 64).setWidth 8 = 0 :=
    (BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64)).trans al
  refine ⟨?_, ?run, ?post⟩
  case run =>
    cfg_eval [b_l101752, rsp, push]
    rfl
  case post =>
    refine ⟨rfl, ?_, ?_⟩
    · change Value.mk 64 ((mergeGPR 8 _ _).setWidth 8 |>.setWidth 64) = _
      simp only [setWidth_mergeGPR8, lo]
      rfl
    · preserves_saved

private theorem branch {a : Regs} {m : Ram} (al : a[0] = ⟨64, 1⟩) :
    ∃ b : Regs, program.runBlock (dialect code) ⟨.l1017a9, a, m⟩ =
      .jump ⟨.l1017b1, b, m⟩ ∧ b[4] = a[4] ∧ Keeps a b := by
  refine ⟨?_, ?run, ?post⟩
  case run =>
    cfg_eval [b_l1017a9]
    rw [al]
    rfl
  case post =>
    refine ⟨rfl, ?_⟩
    preserves_saved

private theorem returnChoice {l next : Label} {a b : Regs} {m n : Ram} {sp ret : BitVec 64}
    (call : program.runBlock (dialect code) ⟨l, a, m⟩ =
      .call ⟨.l127d50, b, memStore n (sp - 8) ret⟩ (resume next ret))
    (rsp : b[4].get 64 = sp - 8) (arg : b[7] = ⟨64, 1⟩)
    (win : Writable code n (sp - 9) 9) (low : ret.toNat < 2^32)
    (stack : List (StackFrame Value Label signature Reg.count)) :
    ∃ (c : Regs) (p : Ram), (program.sem (dialect code)).Reaches ⟨⟨l, a, m⟩, stack⟩ ⟨⟨next, c, p⟩, stack⟩ ∧
      c[4] = ⟨64, sp⟩ ∧ c[0] = ⟨64, 1⟩ ∧ Keeps b c ∧
      RamWriteFrame n p [⟨(sp - 9).toNat, 9⟩] := by
  have adj : sp - 8 - 1 = sp - 9 := by bv_omega
  have tmp : Writable code n (sp - 8 - 1) 1 := by
    rw [adj]
    exact win.of_offsets (addr_sub sp 9) (addr_sub sp 9) (by decide)
  have slot : Readable n (sp - 8) 8 := win.readable.of_offsets (addr_sub sp 8) (addr_sub sp 9) (by decide)
  have tag := memLoad_memStore_same n (sp - 8) ret (by decide) (by decide)
  obtain ⟨out, exec, outTag, osp, ax, frame, keep⟩ :=
    Decode.Convert.convertBarrier rsp (tmp.memStore _ ret) (slot.memStore _ ret) tag low
  refine ⟨out.values, out.store, .step (b := ⟨⟨.l127d50, b, memStore n (sp - 8) ret⟩, resume next ret :: stack⟩) ?_ ?_,
    by simpa only [BitVec.sub_add_cancel] using osp, by rw [ax, arg]; rfl, ?_, ?_⟩
  · simp only [Program.sem, Program.step, call, Transfer.next]
  · exact ParseSignature.exec_reaches_resume exec _ stack (by
      rw [outTag]; exact decide_eq_true (rfl : Value.mk 64 ret = Value.mk 64 ret))
  · refine ⟨?_, fun h => (congrArg Value.width (keep 1 (by decide))).trans h,
      fun h => (congrArg Value.width (keep 2 (by decide))).trans h⟩
    intro j hj
    exact keep j (by simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; grind)
  · have lowWin := win.readable.low
    have hf : RamWriteFrame n (memStore n (sp - 8) ret) [⟨(sp - 9).toNat, 9⟩] := by
      apply (RamWriteFrame.refl _ _).memStore
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      change (sp - 9).toNat ≤ (sp - 8).toNat ∧ (sp - 8).toNat + 8 ≤ (sp - 9).toNat + 9 ∧ _
      bv_omega
    apply hf.trans frame
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    rw [adj]
    exact ⟨_, List.mem_singleton_self _, Nat.le_refl _, by dsimp; omega⟩

private theorem copyScalar {a : Regs} {m : Ram} {sp : BitVec 64} {words : Vector (BitVec 64) 4}
    (rsp : a[4].get 64 = sp) (al : a[0] = ⟨64, 1⟩) (bp : a[5].get 8 = 1)
    (win : Writable code m (sp - 9) 3265) (src : WordsAt m (sp + 3224) 64 words) :
    ∃ (b : Regs) (n : Ram), program.runBlock (dialect code) ⟨.l10175e, a, m⟩ =
        .call ⟨.l127d50, b, memStore n (sp - 8) (0x1017a9 : BitVec 64)⟩ (resume .l1017a9 0x1017a9) ∧
      b[4].get 64 = sp - 8 ∧ b[7] = ⟨64, 1⟩ ∧ Keeps a b ∧
      RamWriteFrame m n [⟨(sp + 192).toNat, 32⟩] ∧ WordsAt n (sp + 192) 64 words := by
  have bp' : (a[5].get 64).setWidth 8 = 1 :=
    (BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64)).trans bp
  have x0 : memLoad m (sp + 3224) 64 = words[0] := wordsAtOffset (offset := 3224) src 0 (by decide)
  have x1 : memLoad m (sp + 3232) 64 = words[1] := wordsAtOffset (offset := 3224) src 1 (by decide)
  have x2 : memLoad m (sp + 3240) 64 = words[2] := wordsAtOffset (offset := 3224) src 2 (by decide)
  have x3 : memLoad m (sp + 3248) 64 = words[3] := wordsAtOffset (offset := 3224) src 3 (by decide)

  refine ⟨?_, ?_, ?run, ?post⟩
  case run =>
    cfg_eval [b_l10175e, rsp]
    repeat' (refine (ite_eq_left ?_).trans ?_; slot_guard using code_l10175e)
    rfl
  case post =>
    refine ⟨rfl, ?_, ?_, ?_, ?_⟩
    · change Value.mk 64 ((mergeGPR 8 _ _).setWidth 8 |>.setWidth 64) = _
      simp only [setWidth_mergeGPR8, bp', al]
      rfl
    · preserves_saved
    · have window : Writable code m (sp - 8) 288 :=
        win.of_offsets (addr_sub sp 8) (addr_sub sp 9) (by decide)
      iterate 4
        apply RamWriteFrame.memStore
        case hin =>
          refine ⟨_, List.mem_singleton_self _, ?_⟩
          apply Sec1.Serialize.Assemble.inStackRegionOffsets window rfl rfl <;> decide
      exact RamWriteFrame.refl _ _
    · apply fourWordsAt <;>
        simp (disch := first | decide | (apply RangeApart.of_offsets rfl rfl; decide))
          only [Lift.reduceAddOffset, memLoad_memStore_same, memLoad_memStore_of_rangeApart, x0, x1, x2, x3]

theorem finishScalar {a : Values Value Reg.count} {m : Ram} {sp : BitVec 64}
    {words : Vector (BitVec 64) 4} (rsp : a[4].get 64 = sp) (al : a[0].get 8 = 0)
    (bp : a[5].get 8 = 1) (win : Writable Extracted.programImage m (sp - 9) 3265)
    (src : WordsAt m (sp + 0xc98) 64 words)
    (stack : List (StackFrame Value Label signature Reg.count)) :
    ∃ (b : Values Value Reg.count) (n : Ram),
      (program.sem (dialect Extracted.programImage)).Reaches
        ⟨⟨.l101752, a, m⟩, stack⟩ ⟨⟨.l1017b1, b, n⟩, stack⟩ ∧
      b[4] = ⟨64, sp⟩ ∧ WordsAt n (sp + 0xc0) 64 words ∧
      RamWriteFrame m n [⟨(sp - 9).toNat, 9⟩, ⟨(sp + 0xc0).toNat, 32⟩] ∧
      (∀ j : Fin Reg.count, j.val ∈ [3, 5, 8, 9, 12, 13, 14, 15, 22, 39, 50, 51] → b[j] = a[j]) ∧
      (a[1].width = 64 → b[1].width = 64) ∧ (a[2].width = 64 → b[2].width = 64) := by
  have slot : Writable code m (sp - 8) 8 := win.of_offsets (addr_sub sp 8) (addr_sub sp 9) (by decide)
  have area : Writable code m (sp - 9) 9 := win.of_offsets (addr_sub sp 9) (addr_sub sp 9) (by decide)
  have disj (off : BitVec 64) (small : off.toNat ≤ 3224) :
      Outside [⟨(sp - 9).toNat, 9⟩] (sp + off) 32 := by
    have bound := win.readable.low
    simp only [Outside, List.mem_singleton, forall_eq]
    bv_omega
  obtain ⟨b, call₁, bsp, di₁, keep₁⟩ := complement rsp al slot
  obtain ⟨c, p, reach₁, csp, flag₁, keep₂, frame₁⟩ := returnChoice call₁ bsp di₁ area (by decide) stack
  have cbp : c[5].get 8 = 1 :=
    (congrArg (Value.get 8) ((keep₂.1 5 (by decide)).trans (keep₁.1 5 (by decide)))).trans bp
  have inputs := WordsAt.of_frame src frame₁ (by decide) (disj 3224 (by decide))
  obtain ⟨d, q, call₂, dsp, di₂, keep₃, copy, limbs⟩ :=
    copyScalar (congrArg (Value.get 64) csp) flag₁ cbp (win.of_frame frame₁) inputs
  obtain ⟨e, t, reach₂, esp, flag₂, keep₄, frame₂⟩ :=
    returnChoice call₂ dsp di₂ ((area.of_frame frame₁).of_frame copy) (by decide) stack
  obtain ⟨g, jump, gsp, keep₅⟩ := branch (m := t) flag₂
  have reach₃ : (program.sem (dialect code)).Reaches ⟨⟨.l1017a9, e, t⟩, stack⟩ ⟨⟨.l1017b1, g, t⟩, stack⟩ :=
    .single (by simp only [Program.sem, Program.step, jump, Transfer.next])
  let regions : List MemoryRegion := [⟨(sp - 9).toNat, 9⟩, ⟨(sp + 192).toNat, 32⟩]
  have tmpWithin : RegionsWithin [⟨(sp - 9).toNat, 9⟩] regions := by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, List.mem_cons_self, Nat.le_refl _, Nat.le_refl _⟩
  have copyWithin : RegionsWithin [⟨(sp + 192).toNat, 32⟩] regions :=
    fun r hr => ⟨r, List.mem_cons_of_mem _ hr, Nat.le_refl _, Nat.le_refl _⟩
  refine ⟨g, t, reach₁.trans (reach₂.trans reach₃), gsp.trans esp,
    WordsAt.of_frame limbs frame₂ (by decide) (disj 192 (by decide)),
    (((RamWriteFrame.refl m regions).trans frame₁ tmpWithin).trans copy copyWithin).trans frame₂ tmpWithin, ?_⟩
  refine ⟨?_, fun h => keep₅.2.1 (keep₄.2.1 (keep₃.2.1 (keep₂.2.1 (keep₁.2.1 h)))),
    fun h => keep₅.2.2 (keep₄.2.2 (keep₃.2.2 (keep₂.2.2 (keep₁.2.2 h))))⟩
  intro j hj
  exact (keep₅.1 j hj).trans ((keep₄.1 j hj).trans ((keep₃.1 j hj).trans ((keep₂.1 j hj).trans (keep₁.1 j hj))))

end K256.Proofs.Ecdh.Scalar
