import K256.Proofs.Generate.Generator.Multiply.AddExecution.Frame.Return

namespace K256.Proofs.Generate.Generator.Multiply.AddFrame

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
  K256.Proofs.Refine K256.Proofs.Generate.LIR K256.Proofs.Sec1.Affine.Uncompressed

private def finishRegions (sp dst : BitVec 64) : List MemoryRegion :=
  [⟨sp.toNat, 384⟩, ⟨dst.toNat, 120⟩]

private abbrev FinishCut (n : Nat) := BitVec 64 → BitVec 64 → Values Value n → Prop

private def FinishSegment {n k} (block : Block Op Label signature Reg.count n)
    (tail : Block Op Label signature Reg.count k) (before : FinishCut n) (after : FinishCut k) : Prop :=
  ∀ {code : CodeMap} (included : ∀ x ∈ fnCode, x ∈ code)
    {a : Values Value n} {m : Ram} {sp dst : BitVec 64} (hn : 65 < n),
    a[65].get 64 = sp → Writable code m sp 536 → Writable code m dst 120 →
    sp.toNat + 544 ≤ dst.toNat → memLoad m (sp + 384) 64 = dst → before sp dst a →
    ∃ b m', block.eval (dialect code) a m = tail.eval (dialect code) b m' ∧
      a.Prefix b ∧ RamWriteFrame m m' (finishRegions sp dst) ∧ after sp dst b

private theorem destAfterSpill (m : Ram) (sp v : BitVec 64) :
    memLoad (memStore m (sp + 184) v) (sp + 384) 64 = memLoad m (sp + 384) 64 :=
  memLoad_memStore_of_rangeApart _ _ _ _ _ (RangeApart.of_offsets rfl rfl (by decide))

private def finish168 : FinishCut 7144 := fun _ dst a => a[7120].get 64 = dst

private def finish169 : FinishCut 7186 := fun _ dst a =>
  a[7120].get 64 = dst ∧ a[7149].get 64 = dst ∧ a[7151].width = 64 ∧ a[7159].width = 64

private def finish170 : FinishCut 7225 := fun _ dst a =>
  a[7149].get 64 = dst ∧ a[7151].width = 64 ∧ a[7159].width = 64

private def finish171 : FinishCut 7260 := fun sp _ a =>
  a[7258].get 64 = sp + 488 ∧ a[7247].width = 64 ∧ a[7249].width = 64 ∧
  a[7251].width = 64 ∧ a[7243].width = 64 ∧ a[7151].width = 64 ∧ a[7159].width = 64

private theorem keepStackWord {sp dst addr : BitVec 64} {m m' : Ram}
    (f : RamWriteFrame m m' (finishRegions sp dst))
    (h : sp.toNat + 384 ≤ addr.toNat) (h' : addr.toNat + 8 ≤ dst.toNat) :
    memLoad m' addr 64 = memLoad m addr 64 := by
  apply f.memLoad_eq
  refine ⟨by have := dst.isLt; change addr.toNat + 8 ≤ _; omega, ?_⟩
  intro r hr
  simp only [finishRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Or.inr h
  · exact Or.inl h'

private theorem FinishSegment.trans {n k j} {b : Block Op Label signature Reg.count n}
    {c : Block Op Label signature Reg.count k} {d : Block Op Label signature Reg.count j}
    {P : FinishCut n} {Q : FinishCut k} {R : FinishCut j}
    (f : FinishSegment b c P Q) (g : FinishSegment c d Q R) : FinishSegment b d P R := by
  intro code inc a m sp dst hn reg stack output gap spill pre
  obtain ⟨b', m', e, p, h, q⟩ := f inc hn reg stack output gap spill pre
  have hsp : (sp + 384).toNat = sp.toNat + 384 := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by have := dst.isLt; change sp.toNat + 384 < _; omega)]
    rfl
  have hk := Nat.lt_of_lt_of_le hn p.1
  obtain ⟨b'', m'', e', p', h', r⟩ := g inc hk ((congrArg (Value.get 64) (p.2 65 hn hk)).trans reg)
    (stack.of_frame h) (output.of_frame h)
    gap ((keepStackWord h (by omega) (by omega)).trans spill) q
  exact ⟨_, _, e.trans e', ⟨Nat.le_trans p.1 p'.1, fun i hi hi' =>
    (p'.2 i (Nat.lt_of_lt_of_le hi p.1) hi').trans (p.2 i hi _)⟩,
    h.trans h' fun r hr => ⟨r, hr, Nat.le_refl _, Nat.le_refl _⟩, r⟩

private theorem savedAfterFinish {fr : Activation} {m m' : Ram} {a : Values Value n}
    {b : Values Value k} (s : AtBody fr a m) (p : a.Prefix b)
    (f : RamWriteFrame m m' (finishRegions (fr.rsp - 536) fr.rdi))
    (depth : 536 ≤ fr.rsp.toNat) (gap : fr.rsp.toNat + 8 ≤ fr.rdi.toNat) :
    AtBody fr b m' := by
  have base : (fr.rsp - 536).toNat = fr.rsp.toNat - 536 :=
    BitVec.toNat_sub_of_le (by exact depth)
  have saved (i : Nat) (hi : i ≤ 48) :
      memLoad m' (fr.rsp - BitVec.ofNat 64 i) 64 = memLoad m (fr.rsp - BitVec.ofNat 64 i) 64 := by
    have hx : (BitVec.ofNat 64 i).toNat = i := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have ha := BitVec.toNat_sub_of_le (x := fr.rsp) (y := BitVec.ofNat 64 i) (by change (BitVec.ofNat 64 i).toNat ≤ fr.rsp.toNat; omega)
    apply keepStackWord f <;> omega
  have spill : ((fr.rsp - 536) + 384).toNat = (fr.rsp - 536).toNat + 384 := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by have := fr.rdi.isLt; change _ + 384 < _; omega)]
    rfl
  have hk := Nat.lt_of_lt_of_le s.size p.1
  refine ⟨hk, (congrArg (Value.get 64) (p.2 65 s.size hk)).trans s.sp,
    p.read (by have := s.size; omega) (by omega) s.df,
    p.read (by have := s.size; omega) (by omega) s.mx,
    p.read (by have := s.size; omega) (by omega) s.ftw,
    p.read (by have := s.size; omega) (by omega) s.fcw,
    (keepStackWord f (by omega) (by omega)).trans s.dest,
    (saved 48 (by decide)).trans s.bx, (saved 40 (by decide)).trans s.r12,
    (saved 32 (by decide)).trans s.r13, (saved 24 (by decide)).trans s.r14,
    (saved 16 (by decide)).trans s.r15, (saved 8 (by decide)).trans s.bp,
    (keepStackWord f (by omega) gap).trans s.ret⟩

open Lean Elab Tactic in
elab "add_finish_step " blockCode:ident " [" fields:ident,* "]" : tactic => do
  let pre := mkIdent `pre
  let reg := mkIdent `reg
  let spill := mkIdent `spill
  let inc := mkIdent `inc
  let hs := fields.getElems
  evalTactic (← `(tactic| (
    intro code included a m sp dst hn $reg stack output gap $spill $pre
    have $inc := fun x hx => included x ($blockCode x hx)
    have slow := stack.readable.low
    have dlow := output.readable.low)))
  if hs.size == 1 then
    let h := hs[0]!
    evalTactic (← `(tactic| unfold finish168 at $pre:ident; have $h := $pre))
  else if hs.size > 1 then
    evalTactic (← `(tactic| obtain ⟨$hs,*⟩ := $pre))
  let facts ← hs.mapM fun h => `(Lean.Parser.Tactic.simpLemma| $h:ident)
  evalTactic (← `(tactic| (
    refine ⟨?_, ?_, ?ev, ?pref, ?frame, ?post⟩
    case ev =>
      arithmetic_prefix [$reg:ident, BitVec.add_zero, destAfterSpill, $spill:ident, $facts,*]
      repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using $inc)
      rfl
    case pref =>
      repeat' apply Values.Prefix.push
      exact Values.Prefix.refl _
    case frame =>
      unfold finishRegions
      slot_state region
    case post =>
      first | exact True.intro | (
        first | unfold finish168 | unfold finish169 | unfold finish170 | unfold finish171
        repeat' apply And.intro
        all_goals simp only [↓arithmeticRead, cfg_eval, BitVec.reduceSignExtend, BitVec.reduceSetWidth, $reg:ident, $spill:ident, $facts,*] <;> rfl))))

private theorem finishStep160 : FinishSegment b_l10a410_160 b_l10a410_161
    (fun _ _ _ => True) (fun _ _ _ => True) := by
  add_finish_step code_l10a410_160 []

private theorem finishStep161 : FinishSegment b_l10a410_161 b_l10a410_162
    (fun _ _ _ => True) (fun _ _ _ => True) := by
  add_finish_step code_l10a410_161 []

private theorem finishStep162 : FinishSegment b_l10a410_162 b_l10a410_163
    (fun _ _ _ => True) (fun _ _ _ => True) := by
  add_finish_step code_l10a410_162 []

private theorem finishStep163 : FinishSegment b_l10a410_163 b_l10a410_164
    (fun _ _ _ => True) (fun _ _ _ => True) := by
  add_finish_step code_l10a410_163 []

private theorem finishStep164 : FinishSegment b_l10a410_164 b_l10a410_165
    (fun _ _ _ => True) (fun _ _ _ => True) := by
  add_finish_step code_l10a410_164 []

private theorem finishStep165 : FinishSegment b_l10a410_165 b_l10a410_166
    (fun _ _ _ => True) (fun _ _ _ => True) := by
  add_finish_step code_l10a410_165 []

private theorem finishStep166 : FinishSegment b_l10a410_166 b_l10a410_167
    (fun _ _ _ => True) (fun _ _ _ => True) := by
  add_finish_step code_l10a410_166 []

private theorem finishStep167 : FinishSegment b_l10a410_167 b_l10a410_168
    (fun _ _ _ => True) finish168 := by
  add_finish_step code_l10a410_167 []

private theorem finishStep168 : FinishSegment b_l10a410_168 b_l10a410_169
    finish168 finish169 := by
  add_finish_step code_l10a410_168 [d7]

private theorem finishStep169 : FinishSegment b_l10a410_169 b_l10a410_170
    finish169 finish170 := by
  add_finish_step code_l10a410_169 [d7, d11, w8, w9]

private theorem finishStep170 : FinishSegment b_l10a410_170 b_l10a410_171
    finish170 finish171 := by
  add_finish_step code_l10a410_170 [d11, w8, w9]

private theorem finishSteps : FinishSegment b_l10a410_160 b_l10a410_171 (fun _ _ _ => True) finish171 :=
  finishStep160.trans <| finishStep161.trans <| finishStep162.trans <|
  finishStep163.trans <| finishStep164.trans <| finishStep165.trans <|
  finishStep166.trans <| finishStep167.trans <| finishStep168.trans <|
  finishStep169.trans <| finishStep170

set_option linter.unusedVariables false in
theorem finishBody {code : CodeMap} (included : ∀ a ∈ fnCode, a ∈ code)
    {fr : Activation} {args : Values Value Reg.count} {mem : Ram}
    (atoms : Atom.All code args mem (Fn10a410.frameAt .l10a410 fr))
    (src : Readable mem fr.rsi 120) (dst : Writable code mem fr.rdi 120)
    (srcAbove : fr.rsp.toNat + 8 ≤ fr.rsi.toNat) (dstAbove : fr.rsp.toNat + 8 ≤ fr.rdi.toNat)
    (apart : fr.rdi.toNat + 120 ≤ fr.rsi.toNat ∨ fr.rsi.toNat + 120 ≤ fr.rdi.toNat)
    {b : Values Value 6804} {m : Ram} (frame : RamWriteFrame mem m (regions fr))
    (state : AtBody fr b m) :
    ∃ out, b_l10a410_160.eval (dialect code) b m = .returned out ∧
      out.tag = some ⟨64, fr.ret⟩ ∧ Atom.All code out.values out.store (Fn10a410.doneAt fr) ∧
      ParseSignature.ArgumentWidths out.values ∧ RamWriteFrame mem out.store (regions fr) := by
  simp only [Fn10a410.frameAt, Fn10a410.frameAtG0, Atom.All, Atom.Holds] at atoms
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rd, _, retLow, stack, low, _⟩ := atoms
  have depth : 536 ≤ fr.rsp.toNat := by omega
  have base : (fr.rsp - 536).toNat = fr.rsp.toNat - 536 :=
    BitVec.toNat_sub_of_le (by exact depth)
  obtain ⟨c, m', ev, p, f, sp, w1, w2, w6, w7, w8, w9⟩ := finishSteps included
    (by decide) state.sp (stack.of_frame frame) (dst.of_frame frame) (by omega) state.dest trivial
  have full := savedAfterFinish state p f depth dstAbove
  have outputFrame := frame.trans f (by
    intro r hr
    simp only [finishRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, Nat.le_refl _, by dsimp; omega⟩
    · exact ⟨_, List.mem_cons.mpr (Or.inr List.mem_cons_self), Nat.le_refl _, Nat.le_refl _⟩)
  obtain ⟨out, run, tag, post, widths, store⟩ := popReturn
    (stack.of_frame outputFrame) (rd.of_frame outputFrame) retLow full
    (sp.trans (by bv_omega)) w1 w2 w6 w7 w8 w9
  exact ⟨out, ev.trans run, tag, post, widths, store ▸ outputFrame⟩

end K256.Proofs.Generate.Generator.Multiply.AddFrame
