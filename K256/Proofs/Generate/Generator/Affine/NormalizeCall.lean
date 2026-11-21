import K256.Proofs.Generate.Serialize.Transfer.Blocks
import K256.Proofs.Sec1.Serialize.Normalize.Execution
import K256.Proofs.Sec1.Serialize.Layout

namespace K256.Proofs.Generate.Generator.Affine

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Spec.Program
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field

theorem normalizeCall {a : Vector Value Reg.count} {m : Ram} {sp src dst ret : Word}
    {v : Limbs} (rsp : a[4] = ⟨64, sp⟩) (rsi : a[6] = ⟨64, src⟩) (rdi : a[7] = ⟨64, dst⟩)
    (df : a[22] = ⟨1, 0⟩) (saved : ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15] →
      a[i] = ⟨64, a[i].get 64⟩)
    (win : Writable Extracted.programImage m (sp - 113) 121)
    (source : Readable m src 40) (dest : Writable Extracted.programImage m dst 40)
    (hsrc : sp.toNat + 8 ≤ src.toNat) (hdst : sp.toNat + 8 ≤ dst.toNat)
    (apart : dst.toNat + 40 ≤ src.toNat ∨ src.toNat + 40 ≤ dst.toNat)
    (dstAlign : dst.toNat % 8 = 0) (align : sp.toNat % 16 = 8) (room : 113 ≤ sp.toNat)
    (slot : memLoad m sp 64 = ret) (retLow : ret.toNat < 2^32) (input : WordsAt m src 64 v) :
    ∃ out, LIR.program.Exec (dialect Extracted.programImage) ⟨⟨.l114930, a, m⟩, []⟩ out ∧
      out.tag = some ⟨64, ret⟩ ∧ out.values[4] = ⟨64, sp + 8⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15,22,39,50,51] → out.values[i] = a[i]) ∧
      RamWriteFrame m out.store [⟨(sp - 113).toNat, 113⟩, ⟨dst.toNat, 40⟩] ∧
      WordsAt out.store dst 64 (Sec1.Serialize.Normalize.normalize v) := by
  let c : Sec1.Serialize.Normalize.Ctx := ⟨src, dst, a[39], a[50], a[51]⟩
  let fr : Activation := {
    original := m, rsp := sp, low := sp - 113, ret := ret, rdi := dst, rsi := src
    rbx := a[3].get 64, rbp := a[5].get 64, r12 := a[12].get 64, r13 := a[13].get 64
    r14 := a[14].get 64, r15 := a[15].get 64, rdx := 0, rcx := 0, r8 := 0, r9 := 0
    mxcsr := 0, ftw := 0, fcw := 0, fs := default }
  let old := Vector.ofFn fun i : Fin 5 => memLoad m (wordAddr dst 64 i.val) 64
  have oldAt : WordsAt m dst 64 old := by
    intro i hi
    simp only [old, Vector.getElem_ofFn]
  have hs : (sp - 113).toNat + 113 = sp.toNat := by
    rw [BitVec.toNat_sub_of_le (by exact room : (113 : Word) ≤ sp)]
    exact Nat.sub_add_cancel room
  have ht := Sec1.Serialize.writable_text_apart win (by decide)
  have hx := Sec1.Serialize.writable_text_apart dest (by decide)
  have entry : Atom.All Extracted.programImage a m
      (Sec1.Serialize.Normalize.frameAt .l114930 fr ++
       Sec1.Serialize.Normalize.core.atoms .entry c fr ⟨dst, v, old⟩) := by
    rw [Sec1.Serialize.Normalize.frameAt_114930, Atom.all_append]
    constructor
    · exact ⟨rsp, df, saved 3 (by decide), saved 5 (by decide), rsi, rdi,
        saved 12 (by decide), saved 13 (by decide), saved 14 (by decide), saved 15 (by decide),
        win.readable.sub (a := sp) (by omega) (by omega), slot, retLow,
        win.sub (a := sp - 113) (n := 113) (Nat.le_refl _) (by omega), Nat.le_of_eq hs, align, trivial⟩
    · exact ⟨rsi, rdi, rfl, rfl, rfl, rfl, input, source, oldAt, dest, dstAlign, apart,
        Or.inr hsrc, Or.inr hdst, hx, (by dsimp only [Atom.Holds, fr]; omega), trivial⟩
  obtain ⟨out, run, tag, atoms, frame⟩ := Sec1.Serialize.Normalize.normalizeExecution c fr v old
    a m entry (RamWriteFrame.refl _ _)
  rw [Sec1.Serialize.Normalize.doneAt_eq] at atoms
  obtain ⟨r4, r22, r3, r5, r12, r13, r14, r15, r39, r50, r51, _, _, result, _⟩ := atoms
  refine ⟨out, Serialize.Relabel.exec Serialize.matches_blocks run rfl, tag, r4, ?_, ?_, result⟩
  · intro i hi
    rcases i with ⟨i, hi'⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact Eq.trans r3 (saved 3 (by decide)).symm
    · exact Eq.trans r5 (saved 5 (by decide)).symm
    · exact Eq.trans r12 (saved 12 (by decide)).symm
    · exact Eq.trans r13 (saved 13 (by decide)).symm
    · exact Eq.trans r14 (saved 14 (by decide)).symm
    · exact Eq.trans r15 (saved 15 (by decide)).symm
    · exact Eq.trans r22 df.symm
    · exact r39
    · exact r50
    · exact r51
  · change RamWriteFrame m out.store [⟨(sp - 113).toNat, sp.toNat - (sp - 113).toNat⟩, _] at frame
    rwa [show sp.toNat - (sp - 113).toNat = 113 by omega] at frame

end K256.Proofs.Generate.Generator.Affine
