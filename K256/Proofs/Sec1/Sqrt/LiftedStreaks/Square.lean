import K256.Proofs.Sec1.Sqrt.Rounds

set_option autoImplicit false

namespace K256.Proofs.Sec1.Sqrt.LiftedSquare

open X86 X86.Machine X86.UserProcess X86Proofs Prelude
open CFG Lift Refine Common.Field

def preserved : List Nat := [3, 5, 12, 13, 14, 15, 22, 39, 50, 51]

def volatile : List Nat := [1, 2, 8, 9]

structure Entry (code : CodeMap) (child : LIR.lifted.Location)
    (base ret : BitVec 64) (words : Limbs) : Prop where
  label : child.label = .l1145f0
  rsp : child.arguments[4]'(by change 4 < Reg.count; decide) = ⟨64, base - 8⟩
  rsi : child.arguments[6]'(by change 6 < Reg.count; decide) = ⟨64, base⟩
  rdi : child.arguments[7]'(by change 7 < Reg.count; decide) = ⟨64, base + 40⟩
  df : child.arguments[22]'(by change 22 < Reg.count; decide) = ⟨1, 0⟩
  widths : ∀ i : Fin Reg.count, i.val ∈ volatile ++ [3, 5, 12, 13, 14, 15, 39, 50, 51] →
    child.arguments[i.val].width = (Reg.ofIndex i.val).width
  workspace : Writable code child.store (base - 112) 192
  slot : memLoad child.store (base - 8) 64 = ret
  retLow : ret.toNat < 2^32
  room : 112 ≤ base.toNat
  align : base.toNat % 16 = 0
  apart : base.toNat + 80 ≤ 0x1145f0 ∨ 0x1148c4 ≤ base.toNat - 112
  input : WordsAt child.store base 64 words

structure Exit (child : LIR.lifted.Location) (base ret : BitVec 64) (words : Limbs)
    (out : CFG.Output Value Ram Reg.count) : Prop where
  tag : out.tag = some ⟨64, ret⟩
  rsp : out.values[4] = ⟨64, base⟩
  saved : ∀ i : Fin Reg.count, i.val ∈ preserved → out.values[i.val] = child.arguments[i.val]
  input : WordsAt out.store base 64 words
  output : WordsAt out.store (base + 40) 64 (squareWords words)
  frame : RamWriteFrame child.store out.store [roundStack base]

private theorem value_get_of_width (v : Value) {n : Nat} (h : v.width = n) :
    v = ⟨n, v.get n⟩ := by
  cases v with
  | mk width bits =>
    change width = n at h
    subst n
    simp only [Value.get, BitVec.setWidth_eq]

private def activation (l : LIR.lifted.Location) (base ret : BitVec 64) : Activation where
  original := l.store
  rsp := base - 8
  ret := ret
  low := base - 112
  rbx := l.arguments[3]'(by change 3 < Reg.count; decide) |>.get 64
  rbp := l.arguments[5]'(by change 5 < Reg.count; decide) |>.get 64
  r12 := l.arguments[12]'(by change 12 < Reg.count; decide) |>.get 64
  r13 := l.arguments[13]'(by change 13 < Reg.count; decide) |>.get 64
  r14 := l.arguments[14]'(by change 14 < Reg.count; decide) |>.get 64
  r15 := l.arguments[15]'(by change 15 < Reg.count; decide) |>.get 64
  rdi := base + 40
  rsi := base
  rdx := l.arguments[2]'(by change 2 < Reg.count; decide) |>.get 64
  rcx := l.arguments[1]'(by change 1 < Reg.count; decide) |>.get 64
  r8 := l.arguments[8]'(by change 8 < Reg.count; decide) |>.get 64
  r9 := l.arguments[9]'(by change 9 < Reg.count; decide) |>.get 64
  mxcsr := l.arguments[39]'(by change 39 < Reg.count; decide) |>.get 32
  ftw := l.arguments[50]'(by change 50 < Reg.count; decide) |>.get 16
  fcw := l.arguments[51]'(by change 51 < Reg.count; decide) |>.get 16
  fs := (default : RamState).FS

theorem execute (code : CodeMap) {child : LIR.lifted.Location}
    {base ret : BitVec 64} {words : Limbs} (h : Entry code child base ret words) :
    ∃ out, LIR.lifted.program.Exec (Lift.dialect code) ⟨child, []⟩ out ∧
      Exit child base ret words out := by
  let fr := activation child base ret
  have h112 : (base - 112).toNat = base.toNat - 112 :=
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact h.room)
  have h8 : (base - 8).toNat = base.toNat - 8 :=
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; change 8 ≤ _; have := h.room; omega)
  have hbound : base.toNat + 80 ≤ 2^32 := by
    have hm := h.workspace.readable.low
    have := h.room
    rw [h112] at hm
    omega
  have h40 : (base + 40).toNat = base.toNat + 40 := by
    rw [BitVec.toNat_add]
    change (base.toNat + 40) % 2^64 = _
    exact Nat.mod_eq_of_lt (by omega)
  have hin : Readable child.store base 40 :=
    h.workspace.readable.sub (by rw [h112]; omega) (by rw [h112]; have := h.room; omega)
  have hout : Writable code child.store (base + 40) 40 :=
    h.workspace.sub (by rw [h40, h112]; omega) (by rw [h40, h112]; have := h.room; omega)
  have hslot : Readable child.store (base - 8) 8 :=
    h.workspace.readable.sub (by rw [h8, h112]; omega) (by rw [h8, h112]; have := h.room; omega)
  have hfloor : fr.rsp - 104 = base - 112 := by
    change base - 8#64 - 104#64 = base - 112#64
    rw [BitVec.sub_sub]
    rfl
  have hwin : Writable code child.store (fr.rsp - 104) 104 := by
    rw [hfloor]
    exact h.workspace.sub (Nat.le_refl _) (by omega)
  let old : Limbs := Vector.ofFn fun i => memLoad child.store (wordAddr (base + 40) 64 i.val) 64
  have hold : WordsAt child.store (base + 40) 64 old := by
    intro i hi
    simp only [old, Vector.getElem_ofFn]
  have hregs (i : Fin Reg.count)
      (hi : i.val ∈ volatile ++ [3, 5, 12, 13, 14, 15, 39, 50, 51]) :
      child.arguments[i.val] = ⟨(Reg.ofIndex i.val).width,
        child.arguments[i.val].get (Reg.ofIndex i.val).width⟩ :=
    value_get_of_width _ (h.widths i hi)
  have hframe : Atom.All code child.arguments child.store (LIR.Fn1145f0.frameAt .l1145f0 fr) := by
    change Atom.All code child.arguments child.store (LIR.Fn1145f0.frameAtG0 .l1145f0 fr)
    simp only [LIR.Fn1145f0.frameAtG0, Atom.All, Atom.Holds, Atom.gpr, Fin.getElem_fin]
    refine ⟨h.rsp, h.df, hregs 1 (by decide), hregs 2 (by decide), hregs 3 (by decide),
      hregs 5 (by decide), h.rsi, h.rdi, hregs 8 (by decide), hregs 9 (by decide),
      hregs 12 (by decide), hregs 13 (by decide), hregs 14 (by decide), hregs 15 (by decide),
      hregs 39 (by decide), hregs 50 (by decide), hregs 51 (by decide),
      hslot, h.slot, h.retLow, hwin, ?_, ?_, trivial⟩
    · change (base - 112).toNat + 104 ≤ (base - 8).toNat
      rw [h112, h8]
      have := h.room
      omega
    · change (base - 8).toNat % 16 = 8
      rw [h8]
      have := h.align
      have := h.room
      omega
  have hwords : Atom.All code child.arguments child.store (Square.core.atoms .entry () fr (words, old)) := by
    have hroom := h.room
    have hap := h.apart
    have halign := h.align
    refine ⟨h.input, hin, hold, hout, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
    · change (base + 40).toNat % 8 = 0
      rw [h40]
      omega
    · change (base + 40).toNat + 40 ≤ base.toNat ∨ base.toNat + 40 ≤ (base + 40).toNat
      rw [h40]
      omega
    · change base.toNat + 40 ≤ (base - 112).toNat ∨ (base - 8).toNat + 8 ≤ base.toNat
      rw [h112, h8]
      omega
    · change (base + 40).toNat + 40 ≤ 0x1145f0 ∨ 0x1148c4 ≤ (base + 40).toNat
      rw [h40]
      omega
    · change (base - 8).toNat + 8 ≤ 0x1145f0 ∨ 0x1148c4 ≤ (base - 112).toNat
      rw [h8, h112]
      omega
    · change (base + 40).toNat + 40 ≤ (base - 112).toNat ∨
        (base - 8).toNat + 8 ≤ (base + 40).toNat
      rw [h40, h112, h8]
      omega
  have hrel : Square.layout.Rel code (fr, ()) ⟨.entry, #v[], (words, old)⟩ child :=
    ⟨h.label, ⟨_, rfl, rfl, (Atom.all_append _ _).2 ⟨hframe, hwords⟩⟩, RamWriteFrame.refl _ _⟩
  obtain ⟨out, he, hpost, hdone⟩ := Square.call code fr (words, old) child hrel
  obtain ⟨htag, ⟨result, heq, hatoms⟩, hwrite⟩ := hpost
  have hs := congrArg CFG.Output.store heq
  change (words, squareWords words) = result at hs
  subst result
  change Atom.All code out.values out.store
    (LIR.Fn1145f0.doneAt fr ++ Square.core.done () fr (words, squareWords words)) at hatoms
  obtain ⟨_, _, hIn, hOut, _⟩ := (Atom.all_append _ _).1 hatoms
  change Atom.All code out.values out.store (LIR.Fn1145f0.doneAt fr) at hdone
  simp only [LIR.Fn1145f0.doneAt, Atom.All, Atom.Holds, Atom.gpr, Fin.getElem_fin] at hdone
  obtain ⟨hsp, hdf, h3, h5, h12, h13, h14, h15, h39, h50, h51, _⟩ := hdone
  have hSaved (i : Fin Reg.count) (hi : i.val ∈ preserved) :
      out.values[i.val] = child.arguments[i.val] := by
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hi
    obtain ⟨i, hlt⟩ := i
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h3.trans (hregs 3 (by decide)).symm
    · exact h5.trans (hregs 5 (by decide)).symm
    · exact h12.trans (hregs 12 (by decide)).symm
    · exact h13.trans (hregs 13 (by decide)).symm
    · exact h14.trans (hregs 14 (by decide)).symm
    · exact h15.trans (hregs 15 (by decide)).symm
    · exact hdf.trans h.df.symm
    · exact h39.trans (hregs 39 (by decide)).symm
    · exact h50.trans (hregs 50 (by decide)).symm
    · exact h51.trans (hregs 51 (by decide)).symm
  have hregion : RegionsWithin (fr.region :: Square.core.footprint () fr) [roundStack base] := by
    intro r hr
    simp only [Square.core, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> refine ⟨roundStack base, List.mem_cons_self, ?_, ?_⟩
    · exact Nat.le_refl _
    · change (base - 112).toNat + ((base - 8).toNat - (base - 112).toNat) ≤ (base - 112).toNat + 192
      rw [h112, h8]
      omega
    · change (base - 112).toNat ≤ (base + 40).toNat
      rw [h112, h40]
      omega
    · change (base + 40).toNat + 40 ≤ (base - 112).toNat + 192
      rw [h112, h40]
      have := h.room
      omega
  have hsp' : out.values[4] = ⟨64, base⟩ := by
    change out.values[4] = ⟨64, (base - 8#64) + 8#64⟩ at hsp
    rwa [BitVec.sub_add_cancel] at hsp
  exact ⟨out, he, htag, hsp', hSaved, hIn, hOut, (RamWriteFrame.refl _ _).trans hwrite hregion⟩

end K256.Proofs.Sec1.Sqrt.LiftedSquare
