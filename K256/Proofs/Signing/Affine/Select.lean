import K256.Proofs.Signing.Affine.Select.Setup
import K256.Proofs.Signing.Affine.Select.Child
import K256.Proofs.Generate.Generator.Affine.Select.Return
import K256.Proofs.ParseSignature.Call

namespace K256.Proofs.Signing.Affine

open K256.Proofs.Generate.Generator.Affine

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Generate.LIR
open Standards.SECG.ECC

theorem selectPoint {fr : Activation} {a : Registers} {m : Ram} {point : Curve.Point}
    (s : CallState .l10ee37 fr a m)
    (h : Products fr a m point) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l10ee37, a, m⟩, []⟩ out ∧
      out.tag = some ⟨64, fr.ret⟩ ∧ Atom.All Extracted.programImage out.values out.store
        (Fn10fe50.doneAt fr) ∧ RamWriteFrame fr.original out.store (writes fr) ∧
      Sec1.Parser.PublicKeyAt out.store fr.rdi point := by
  obtain ⟨b, call, args, setupFrame⟩ := setupSelection s h
  have atoms : Atom.All Extracted.programImage a m (Fn10fe50.frameAt .l10ee37 fr) := s.atoms
  simp only [Fn10fe50.frameAt, Fn10fe50.frameAtG1, Atom.All, Atom.Holds] at atoms
  obtain ⟨_, df, bx, r14, mx, ftw, fcw, save3, save12, save13, save14, save15, save5, retRead,
    retWord, retLow, stack, lower, align, _⟩ := atoms
  let m₁ := setupMemory fr m
  change RamWriteFrame m m₁ (setupWrites fr) at setupFrame
  have stack₁ := stack.of_frame setupFrame
  have low : 296 ≤ fr.rsp.toNat := by omega
  have dstAbove := s.dstAbove
  have high := retRead.low
  have scratch : Writable Extracted.programImage m₁ (fr.rsp - 296) 64 := by slot_state region
  have source : Readable m₁ (fr.rsp - 144) 81 := by slot_state region
  have fallback : Readable m₁ (fr.rsp - 232) 81 := by slot_state region
  have dest : Writable Extracted.programImage m₁ fr.rdi 81 := by
    have w := s.dest.of_frame setupFrame
    slot_state region
  have ret : memLoad m₁ (fr.rsp - 240) 64 = 0x10ee65 :=
    memLoad_memStore_same _ _ _ (by decide) (by decide)
  have hb3 := (args.kept 3 (by decide)).trans bx
  have hb14 := (args.kept 14 (by decide)).trans r14
  obtain ⟨mid, run, tag, sp, kept, childFrame, wordCopy, flagCopy⟩ :=
    runSelection args.rsp args.rdx args.rsi args.rdi args.rcx hb3 hb14 scratch source fallback dest ret low dstAbove
  have reg (i : Fin Reg.count) (hi : i.val ∈ [3, 14, 22, 39, 50, 51]) :
      mid.values[i] = a[i] := (kept i hi).trans (args.kept i hi)
  have sub (k : Nat) (hk : k ≤ 976) : (fr.rsp - BitVec.ofNat 64 k).toNat = fr.rsp.toNat - k :=
    stackBaseNat lower hk
  have n296 : (fr.rsp - 296).toNat = fr.rsp.toNat - 296 := sub 296 (by decide)
  have n240 : (fr.rsp - 240).toNat = fr.rsp.toNat - 240 := sub 240 (by decide)
  have n56 : (fr.rsp - 56).toNat = fr.rsp.toNat - 56 := sub 56 (by decide)
  have preserved (k : Nat) (hk : k ≤ 48) :
      memLoad mid.store (fr.rsp - BitVec.ofNat 64 k) 64 =
        memLoad m (fr.rsp - BitVec.ofNat 64 k) 64 := by
    have hn := sub k (by omega)
    rw [childFrame.memLoad_eq, setupFrame.memLoad_eq]
    all_goals
      refine ⟨by omega, ?_⟩
      simp only [childWrites, setupWrites, List.mem_cons, List.not_mem_nil, or_false]
      intro r hr
      rcases hr with rfl | rfl
      all_goals
        change _ ≤ _ ∨ _ ≤ _
        first
        | right; change (fr.rsp - 240).toNat + 96 ≤ _; omega
        | right; change (fr.rsp - 56).toNat + 1 ≤ _; omega
        | right; change (fr.rsp - 296).toNat + 56 ≤ _; omega
        | left; change _ ≤ fr.rdi.toNat; omega
  have retEq : memLoad mid.store fr.rsp 64 = fr.ret := by
    have same := preserved 0 (by decide)
    rw [show fr.rsp - BitVec.ofNat 64 0 = fr.rsp from BitVec.sub_zero _] at same
    exact same.trans retWord
  have resume : Atom.All Extracted.programImage mid.values mid.store (Fn10fe50.frameAt .l10ee65 fr) := by
    simp only [Fn10fe50.frameAt, Fn10fe50.frameAtG1, Atom.All, Atom.Holds]
    exact ⟨sp, (reg 22 (by decide)).trans df, (reg 3 (by decide)).trans bx,
      (reg 14 (by decide)).trans r14, (reg 39 (by decide)).trans mx,
      (reg 50 (by decide)).trans ftw, (reg 51 (by decide)).trans fcw,
      (preserved 48 (by decide)).trans save3, (preserved 40 (by decide)).trans save12,
      (preserved 32 (by decide)).trans save13, (preserved 24 (by decide)).trans save14,
      (preserved 16 (by decide)).trans save15, (preserved 8 (by decide)).trans save5,
      (retRead.of_frame setupFrame).of_frame childFrame, retEq, retLow,
      stack₁.of_frame childFrame, lower, align, trivial⟩
  have withinStack (k n : Nat) (hk : k ≤ 976) (hn : n ≤ k) :
      ∃ r ∈ writes fr, r.start ≤ (fr.rsp - BitVec.ofNat 64 k).toNat ∧
        (fr.rsp - BitVec.ofNat 64 k).toNat + n ≤ r.start + r.size := by
    have off := sub k hk
    refine ⟨fr.region, List.mem_cons_self, ?_, ?_⟩ <;> dsimp only [Activation.region] <;> omega
  obtain ⟨out, epilogue, returned, outMem, done_⟩ := returnPoint resume
  refine ⟨out, ?_, returned, outMem.symm ▸ done_, ?_, ?_⟩
  · apply ParseSignature.exec_call call run _ epilogue
    rw [tag]
    rfl
  · rw [outMem]
    apply (s.frame.trans setupFrame ?_).trans childFrame
    · intro r hr
      simp only [childWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact withinStack 296 56 (by decide) (by decide)
      · refine ⟨⟨fr.rdi.toNat, 88⟩, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_, ?_⟩
        · exact Nat.le_refl _
        · change fr.rdi.toNat + 81 ≤ fr.rdi.toNat + 88
          exact Nat.add_le_add_left (by decide) _
    · intro r hr
      simp only [setupWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact withinStack 240 96 (by decide) (by decide)
      · exact withinStack 56 1 (by decide) (by decide)
  · rw [outMem]
    have srcNat : (fr.rsp - 144).toNat = fr.rsp.toNat - 144 := sub 144 (by decide)
    have sources (i w : Nat) (fit : i + w / 8 ≤ 81) :
        memLoad m₁ (fr.rsp - 144 + BitVec.ofNat 64 i) w =
          memLoad m (fr.rsp - 144 + BitVec.ofNat 64 i) w := by
      have hn : (fr.rsp - 144 + BitVec.ofNat 64 i).toNat = fr.rsp.toNat - 144 + i := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, srcNat,
          Nat.mod_eq_of_lt (by omega : i < 2^64), Nat.mod_eq_of_lt (by omega)]
      apply setupFrame.memLoad_eq
      refine ⟨by omega, ?_⟩
      simp only [setupWrites, List.mem_cons, List.not_mem_nil, or_false]
      intro r hr
      rcases hr with rfl | rfl
      · right
        change (fr.rsp - 240).toNat + 96 ≤ _
        omega
      · left
        change _ ≤ (fr.rsp - 56).toNat
        omega
    obtain ⟨x, y, hp, xl, yl, wx, wy, flag, rx, ry⟩ := h.pointAt
    refine ⟨x, y, hp, xl, yl, ?_, ?_, ?_, rx, ry⟩
    · intro i hi
      exact (wordCopy i (by omega)).trans ((sources (8*i) 64 (by omega)).trans (wx i hi))
    · intro i hi
      have w := (wordCopy (5+i) (by omega : 5+i < 10)).trans
        (sources (8*(5+i)) 64 (by omega))
      have address (p : Word) : wordAddr (p + 40) 64 i = p + BitVec.ofNat 64 (8*(5+i)) := by
        simp only [wordAddr, Nat.mul_add, BitVec.ofNat_add, BitVec.add_assoc]
        rfl
      rw [← address fr.rdi, ← address (fr.rsp - 144)] at w
      exact w.trans (wy i hi)
    · exact flagCopy.trans ((sources 80 8 (by decide)).trans flag)

end K256.Proofs.Signing.Affine
