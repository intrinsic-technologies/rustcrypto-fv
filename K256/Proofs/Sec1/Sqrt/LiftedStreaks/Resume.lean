import K256.Proofs.Sec1.Sqrt.LiftedStreaks.CopyCall
import K256.Proofs.Sec1.Sqrt.LiftedStreaks.Widths
import K256.Proofs.ParseSignature.Call

set_option autoImplicit false

namespace K256.Proofs.Sec1.Sqrt.LiftedCopy

open X86 X86.Machine X86.UserProcess X86Proofs Prelude
open CFG Lift Refine Common.Field LIR

def dstReg (useRbp : Bool) : Fin Reg.count := if useRbp then 5 else 3

structure Ready (code : CodeMap) (useRbp : Bool) (base : Word) (words : Limbs)
    (l : LIR.lifted.Location) : Prop where
  rsp : l.arguments[4]'(by change 4 < Reg.count; decide) = ⟨64, base⟩
  src : (l.arguments[14]'(by change 14 < Reg.count; decide)).get 64 = base
  dst : (l.arguments[(dstReg useRbp).val]).get 64 = base + 40
  df : l.arguments[22]'(by change 22 < Reg.count; decide) = ⟨1, 0⟩
  widths : ∀ i : Fin Reg.count, i.val ∈ LiftedSquare.volatile ++ [3, 5, 12, 13, 14, 15, 39, 50, 51] →
    l.arguments[i.val].width = (Reg.ofIndex i.val).width
  workspace : Writable code l.store (base - 112) 192
  output : WordsAt l.store (base + 40) 64 words

private theorem argsAfterCopy_saved (a : Values Value Reg.count) (base : Word) (w : Limbs)
    (i : Fin Reg.count) (hi : i.val ∈ LiftedSquare.preserved) :
    (argsAfterCopy a base w)[i.val] = a[i.val] := by
  simp only [LiftedSquare.preserved, List.mem_cons, List.not_mem_nil, or_false] at hi
  obtain ⟨i, il⟩ := i
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [argsAfterCopy]

private theorem argsAfterCopy_widths (a : Values Value Reg.count) (base : Word) (w : Limbs)
    (h : ∀ i : Fin Reg.count, i.val ∈ LiftedSquare.volatile ++ [3, 5, 12, 13, 14, 15, 39, 50, 51] →
      a[i.val].width = (Reg.ofIndex i.val).width)
    (i : Fin Reg.count) (hi : i.val ∈ LiftedSquare.volatile ++ [3, 5, 12, 13, 14, 15, 39, 50, 51]) :
    (argsAfterCopy a base w)[i.val].width = (Reg.ofIndex i.val).width := by
  have hw := h i hi
  simp only [LiftedSquare.volatile, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hi
  obtain ⟨i, il⟩ := i
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [argsAfterCopy, Vector.getElem_set, Nat.reduceEqDiff] <;>
    first | exact hw | rfl

private theorem widths_after_square {code : CodeMap} {child : LIR.lifted.Location}
    {base ret : Word} {w : Limbs} {output : CFG.Output Value Ram Reg.count}
    (hin : LiftedSquare.Entry code child base ret w)
    (hExec : LIR.lifted.program.Exec (Lift.dialect code) ⟨child, []⟩ output)
    (hex : LiftedSquare.Exit child base ret w output) :
    ∀ i : Fin Reg.count, i.val ∈ LiftedSquare.volatile ++ [3, 5, 12, 13, 14, 15, 39, 50, 51] →
      output.values[i.val].width = (Reg.ofIndex i.val).width := by
  intro i hi
  rcases List.mem_append.1 hi with hv | hp
  · have he := LiftedSquare.volatileWidths code child hin.label output hExec i hv
    simp only [LiftedSquare.volatile, List.mem_cons, List.not_mem_nil, or_false] at hv
    obtain ⟨i, il⟩ := i
    rcases hv with rfl | rfl | rfl | rfl <;> exact he
  · have hs : i.val ∈ LiftedSquare.preserved := by
      simp only [LiftedSquare.preserved, List.mem_cons, List.not_mem_nil, or_false] at hp ⊢
      omega
    rw [hex.saved i hs]
    exact hin.widths i hi

theorem resume {code : CodeMap} {l : LIR.lifted.Location} {target : Label}
    {useRbp : Bool} {base : Word} {words : Limbs}
    (stack : List LIR.lifted.StackFrame)
    (hBlock : program.blocks l.label =
      block (address l.label) target (dstReg useRbp))
    (hroom : 112 ≤ base.toNat) (halign : base.toNat % 16 = 0)
    (hp : (address l.label).toNat + 60 ≤ 2^32)
    (hret : ((address l.label) + 60).toNat < 2^32)
    (hap : base.toNat + 80 ≤ (address l.label).toNat ∨
      (address l.label).toNat + 60 ≤ base.toNat - 112)
    (hapSquare : base.toNat + 80 ≤ 0x1145f0 ∨ 0x1148c4 ≤ base.toNat - 112)
    (h : Ready code useRbp base words l) :
    ∃ t, (program.sem (Lift.dialect code)).Reaches ⟨l, stack⟩ ⟨t, stack⟩ ∧
      t.label = target ∧ Ready code useRbp base (squareWords words) t ∧
      RamWriteFrame l.store t.store [roundStack base] ∧
      (∀ i : Fin Reg.count, i.val ∈ LiftedSquare.preserved →
        t.arguments[i.val] = l.arguments[i.val]) := by
  let ret := address l.label + 60#64
  let frame := copyFrame target ret
  let child : LIR.lifted.Location := ⟨.l1145f0, argsAfterCopy l.arguments base words,
    memStore (copyWordsMemory l.store base words) (base - 8) ret⟩
  have hrsp64 : (l.arguments[4]'(by change 4 < Reg.count; decide)).get 64 = base := by
    rw [h.rsp]
    simp only [Value.get, BitVec.setWidth_eq]
  have hcall : program.runBlock (Lift.dialect code) l = .call child frame :=
    runFromLabel (useRbp := useRbp) hBlock hrsp64 h.src (by cases useRbp <;> exact h.dst) h.workspace hroom hp hap h.output
  obtain ⟨hw, hwords, hslot, hframe⟩ := preparedMemory (w := words) ret hroom h.workspace
  have hchild : LiftedSquare.Entry code child base ret words := by
    refine ⟨rfl, ?_, ?_, ?_, ?_, argsAfterCopy_widths _ _ _ h.widths,
      hw, hslot, hret, hroom, halign, hapSquare, hwords⟩
    · change (argsAfterCopy l.arguments base words)[4] = _
      simp [argsAfterCopy]
    · change (argsAfterCopy l.arguments base words)[6] = _
      simp [argsAfterCopy]
    · change (argsAfterCopy l.arguments base words)[7] = _
      simp [argsAfterCopy]
    · exact (argsAfterCopy_saved _ _ _ 22 (by decide)).trans h.df
  obtain ⟨out, hExec, hx⟩ := LiftedSquare.execute code hchild
  have accept : frame.Accepts (Lift.dialect code) out.tag = true := by
    rw [hx.tag]
    simp [frame, copyFrame, StackFrame.Accepts, Lift.dialect]
  let t := frame.resume out
  have reached : (program.sem (Lift.dialect code)).Reaches ⟨l, stack⟩ ⟨t, stack⟩ := by
    have entered : (program.sem (Lift.dialect code)).Reaches ⟨l, stack⟩
        ⟨child, frame :: stack⟩ := by
      refine .single ?_
      change program.step (Lift.dialect code) ⟨l, stack⟩ = _
      rw [Program.step, hcall]
      rfl
    exact entered.trans (ParseSignature.exec_reaches_resume hExec frame stack accept)
  have ha : t.arguments = out.values := ParseSignature.resume_arguments frame out
  have hSaved (i : Fin Reg.count) (hi : i.val ∈ LiftedSquare.preserved) :
      t.arguments[i.val] = l.arguments[i.val] := by
    exact (congrArg (fun a : Values Value Reg.count => a[i.val]) ha).trans
      ((hx.saved i hi).trans (argsAfterCopy_saved _ _ _ i hi))
  have hf := hframe.trans hx.frame (fun r hr => ⟨r, hr, Nat.le_refl _, Nat.le_refl _⟩)
  refine ⟨t, reached, rfl, ⟨?_, ?_, ?_, ?_, ?_, h.workspace.of_frame hf, hx.output⟩, hf, hSaved⟩
  · exact (congrArg (fun a : Values Value Reg.count => a[4]) ha).trans hx.rsp
  · rw [show t.arguments[14]'(by change 14 < Reg.count; decide) = l.arguments[14]'(by
      change 14 < Reg.count; decide) from hSaved 14 (by decide)]
    exact h.src
  · rw [hSaved (dstReg useRbp) (by cases useRbp <;> decide)]
    exact h.dst
  · exact (hSaved 22 (by decide)).trans h.df
  · intro i hi
    rw [show t.arguments[i.val] = out.values[i.val] from
      congrArg (fun a : Values Value Reg.count => a[i.val]) ha]
    exact widths_after_square hchild hExec hx i hi

end K256.Proofs.Sec1.Sqrt.LiftedCopy
