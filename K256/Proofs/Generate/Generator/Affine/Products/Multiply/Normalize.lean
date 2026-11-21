import K256.Proofs.Generate.Generator.Affine.NormalizeCall
import K256.Proofs.Common.Tactic
import K256.Proofs.Generate.Generator.Affine.Products.Input

namespace K256.Proofs.Generate.Generator.Affine

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Generate.LIR

def productNormalizeReturn (l : Label) (ret : Word) : StackFrame Value Label signature Reg.count :=
  ⟨l, #v[], rfl, some ⟨64, ret⟩⟩

theorem secondNormalizeEntry {sp : Word} {a : Registers} {m : Ram}
    (rsp : a[4].get 64 = sp) (rbx : a[3].get 64 = sp + 376)
    (win : Writable Extracted.programImage m (sp - 8) 8) :
    ∃ b : Registers, program.runBlock (dialect Extracted.programImage) ⟨.l10ecb2, a, m⟩ =
      .call ⟨.l114930, b, memStore m (sp - 8) (0x10ecc3 : Word)⟩
        (productNormalizeReturn .l10ecc3 0x10ecc3) ∧
      b[4] = ⟨64, sp - 8⟩ ∧ b[6] = ⟨64, sp + 192⟩ ∧ b[7] = ⟨64, sp + 416⟩ ∧
      ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15,22,39,50,51] → b[i] = a[i] := by
  refine ⟨?b, ?entry, ?post⟩
  case entry =>
    cfg_eval
    simp only [rbx, rsp, Lift.reduceAddOffset]
    refine (ite_eq_left (by slot_guard using code_l10ecb2)).trans ?_
    rfl
  case post =>
    refine ⟨rfl, rfl, rfl, ?_⟩
    intro ⟨i, hi⟩ hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem normalizeProductAt {sp ret : Word} {a : Registers} {m : Ram}
    {v : Limbs} {i : Word} (idx : i = 0 ∨ i = 40)
    (win : Writable Extracted.programImage m (sp - 121) 585)
    (room : 121 ≤ sp.toNat) (high : sp.toNat + 464 ≤ 2^32) (align : sp.toNat % 16 = 0)
    (rsp : a[4] = ⟨64, sp - 8⟩) (src : a[6] = ⟨64, sp + (152 + i)⟩)
    (dst : a[7] = ⟨64, sp + (376 + i)⟩) (df : a[22] = ⟨1, 0⟩)
    (saved : ∀ j : Fin Reg.count, j.val ∈ [3,5,12,13,14,15] → a[j] = ⟨64, a[j].get 64⟩)
    (slot : memLoad m (sp - 8) 64 = ret) (lowRet : ret.toNat < 2^32)
    (input : WordsAt m (sp + (152 + i)) 64 v) :
    ∃ o, program.Exec (dialect Extracted.programImage) ⟨⟨.l114930, a, m⟩, []⟩ o ∧
      o.tag = some ⟨64, ret⟩ ∧ o.values[4] = ⟨64, sp⟩ ∧
      (∀ j : Fin Reg.count, j.val ∈ [3,5,12,13,14,15,22,39,50,51] → o.values[j] = a[j]) ∧
      RamWriteFrame m o.store [⟨(sp - 121).toNat, 113⟩, ⟨(sp + (376 + i)).toNat, 40⟩] ∧
      WordsAt o.store (sp + (376 + i)) 64 (Sec1.Serialize.Normalize.normalize v) := by
  have lower : (sp - 8).toNat = sp.toNat - 8 :=
    BitVec.toNat_sub_of_le (by change 8 ≤ sp.toNat; omega)
  have add (k : Word) (h : k.toNat ≤ 464) : (sp + k).toNat = sp.toNat + k.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have callee : sp - 8 - 113 = sp - 121 := by bv_omega
  have mem : Writable Extracted.programImage m (sp - 8 - 113) 121 := by
    rw [callee]
    exact win.sub (Nat.le_refl _) (by omega)
  rcases idx with rfl|rfl <;> (
    simp only [BitVec.reduceAdd] at src dst input ⊢
    obtain ⟨o, run, tag, r4, kept, frame, vals⟩ := normalizeCall rsp src dst df saved mem
      (by slot_state region) (by slot_state region)
      (by rw [lower, add _ (by decide)]; simp only [BitVec.reduceToNat]; omega) (by rw [lower, add _ (by decide)]; simp only [BitVec.reduceToNat]; omega)
      (by right; rw [add _ (by decide), add _ (by decide)]; simp only [BitVec.reduceToNat]; omega)
      (by rw [add _ (by decide)]; simp only [BitVec.reduceToNat]; omega) (by rw [lower]; omega) (by omega) slot lowRet input
    rw [callee] at frame
    rw [BitVec.sub_add_cancel] at r4
    exact ⟨o, run, tag, r4, kept, frame, vals⟩)

end K256.Proofs.Generate.Generator.Affine
