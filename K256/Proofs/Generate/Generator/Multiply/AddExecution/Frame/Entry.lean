import K256.Proofs.Generate.Generator.Multiply.AddExecution.Frame.Preservation

namespace K256.Proofs.Generate.Generator.Multiply.AddFrame

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
  K256.Proofs.Refine K256.Proofs.Generate.LIR K256.Proofs.Sec1.Affine.Uncompressed

private structure EntryState {n : Nat} (fr : Activation) (a : Values Value n) (m : Ram)
    extends AtBody fr a m where
  si : (a[6]'(by have := size; omega)).get 64 = fr.rsi
  di : (a[7]'(by have := size; omega)).get 64 = fr.rdi
  sourceSlot : 123 ≤ n → n ≤ 1110 → memLoad m ((fr.rsp - 0x218) + 0x60) 64 = fr.rsi
  destY : ∀ h : 570 < n, n ≤ 637 → (a[570]'h).get 64 = fr.rdi
  sourceY : ∀ h : 574 < n, n ≤ 637 → (a[574]'h).get 64 = fr.rsi
  destZ : ∀ h : 1108 < n, (a[1108]'h).get 64 = fr.rdi

private def EntrySegment {n k : Nat} (b : Block Op Label signature Reg.count n)
    (t : Block Op Label signature Reg.count k) : Prop :=
  ∀ {fr : Activation} {code : CodeMap} (_included : ∀ a ∈ fnCode, a ∈ code)
    {a : Values Value n} {m : Ram}, EntryState fr a m →
    Writable code m (fr.rsp - 0x218) 0x218 → Readable m fr.rsi 120 → Writable code m fr.rdi 120 →
    0x218 ≤ fr.rsp.toNat → fr.rsp.toNat + 8 ≤ 2^32 →
    ∃ c p, b.eval (dialect code) a m = t.eval (dialect code) c p ∧
      RamWriteFrame m p (regions fr) ∧ EntryState fr c p

private theorem EntrySegment.trans {n k j} {b : Block Op Label signature Reg.count n}
    {c : Block Op Label signature Reg.count k} {d : Block Op Label signature Reg.count j}
    (f : EntrySegment b c) (g : EntrySegment c d) : EntrySegment b d := by
  intro fr code inc a m s win src dst dep low
  obtain ⟨v, o, h, w, st⟩ := f inc s win src dst dep low
  obtain ⟨v', o', h', w', st'⟩ := g inc st (win.of_frame w) (src.of_frame w) (dst.of_frame w) dep low
  exact ⟨v', o', h.trans h', w.trans w' (fun r hr => ⟨r, hr, Nat.le_refl _, Nat.le_refl _⟩), st'⟩

set_option maxHeartbeats 1500000 in
private theorem prologue {code : CodeMap} (included : ∀ a ∈ fnCode, a ∈ code)
    {fr : Activation} {args : Values Value Reg.count} {mem : Ram}
    (atoms : Atom.All code args mem (Fn10a410.frameAt .l10a410 fr))
    (src : Readable mem fr.rsi 120) (dst : Writable code mem fr.rdi 120) :
    ∃ b m, b_l10a410.eval (dialect code) args mem = b_l10a410_1.eval (dialect code) b m ∧
      RamWriteFrame mem m (regions fr) ∧ EntryState fr b m := by
  simp only [Fn10a410.frameAt, Fn10a410.frameAtG0, Atom.All, Atom.Holds] at atoms
  obtain ⟨sp, df, _, _, bx, bp, si, di, _, _, r12, r13, r14, r15, mx, ft, fc,
    rr, ret, _, win, room, _, _⟩ := atoms
  have inc := fun x hx => included x (code_l10a410 x hx)
  change args[22] = ⟨1, 0⟩ at df
  change args[39] = ⟨32, fr.mxcsr⟩ at mx
  change args[50] = ⟨16, fr.ftw⟩ at ft
  change args[51] = ⟨16, fr.fcw⟩ at fc
  have spWord : args[4].get 64 = fr.rsp := congrArg (Value.get 64) sp
  have bpWord : args[5].get 64 = fr.rbp := congrArg (Value.get 64) bp
  have bxWord : args[3].get 64 = fr.rbx := congrArg (Value.get 64) bx
  have siWord : args[6].get 64 = fr.rsi := congrArg (Value.get 64) si
  have diWord : args[7].get 64 = fr.rdi := congrArg (Value.get 64) di
  have r12Word : args[12].get 64 = fr.r12 := congrArg (Value.get 64) r12
  have r13Word : args[13].get 64 = fr.r13 := congrArg (Value.get 64) r13
  have r14Word : args[14].get 64 = fr.r14 := congrArg (Value.get 64) r14
  have r15Word : args[15].get 64 = fr.r15 := congrArg (Value.get 64) r15
  have low := rr.low
  have dep : 0x218 ≤ fr.rsp.toNat := by omega
  refine ⟨?_, ?_, ?ev, ?frame, ?st⟩
  case ev =>
    arithmetic_prefix [spWord, bpWord, bxWord, siWord, diWord, r12Word, r13Word, r14Word, r15Word,
      BitVec.sub_sub, BitVec.reduceAdd, Lift.reduceAddOffset, Lift.reduceSubOffset,
      Lift.reduceSubNeg, Lift.reduceAddNeg, BitVec.add_zero]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using inc)
    rfl
  case frame => unfold regions; slot_state region
  case st =>
    refine { toAtBody := ?body, si := ?si, di := ?di, sourceSlot := ?_,
             destY := ?_, sourceY := ?_, destZ := ?_ }
    case body =>
      refine ⟨by decide, ?sp, ?df, ?mx, ?ft, ?fc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      case sp => simp only [↓arithmeticRead, Value.get_mk_setWidth, BitVec.setWidth_eq]
      case df => simpa only [↓arithmeticRead] using df
      case mx => simpa only [↓arithmeticRead] using mx
      case ft => simpa only [↓arithmeticRead] using ft
      case fc => simpa only [↓arithmeticRead] using fc
      all_goals segment_words [ret]
    case si => simpa only [↓arithmeticRead] using siWord
    case di => simpa only [↓arithmeticRead] using diWord
    all_goals intro h; exact absurd h (by decide)

private theorem EntryState.advance {n k : Nat} {fr : Activation}
    {a : Values Value n} {b : Values Value k} {m p : Ram} {base : BitVec 64}
    (s : EntryState fr a m) (hb : fr.rsp - 0x218 = base)
    (dep : 0x218 ≤ fr.rsp.toNat) (low : fr.rsp.toNat + 8 ≤ 2^32)
    (hf : RamWriteFrame m p (spills base)) (hp : a.Prefix b)
    (slot : 123 ≤ k → k ≤ 1110 → memLoad p (base + 0x60) 64 = fr.rsi)
    (dy : ∀ h : 570 < k, k ≤ 637 → (b[570]'h).get 64 = fr.rdi)
    (sy : ∀ h : 574 < k, k ≤ 637 → (b[574]'h).get 64 = fr.rsi)
    (dz : ∀ h : 1108 < k, (b[1108]'h).get 64 = fr.rdi) :
    RamWriteFrame m p (regions fr) ∧ EntryState fr b p := by
  subst base
  have kept := s.toAtBody.preserve hp hf dep low
  have hn := s.size
  have hk := kept.size
  refine ⟨(RamWriteFrame.refl _ _).trans hf (spillsWithin fr dep), ?_⟩
  exact { toAtBody := kept
          si := (congrArg (Value.get 64) (hp.2 6 (by omega) (by omega))).trans s.si
          di := (congrArg (Value.get 64) (hp.2 7 (by omega) (by omega))).trans s.di
          sourceSlot := slot, destY := dy, sourceY := sy, destZ := dz }


macro "add_entry_segment" : tactic => `(tactic| (
  intro fr code included a m s win src dst dep low
  have inc := fun x hx => included x (code_l10a410 x hx)
  generalize hb : fr.rsp - 0x218 = base at win
  have sp := s.sp.trans hb
  have si := s.si
  have di := s.di
  have dest := s.dest
  rw [hb] at dest
  first | (have source := s.sourceSlot (by decide) (by decide); rw [hb] at source) | have source := si
  first | (have dy := s.destY (by decide) (by decide)) | have dy := si
  first | (have sy := s.sourceY (by decide) (by decide)) | have sy := si
  first | (have dz := s.destZ (by decide)) | have dz := si
  have hi := win.readable.low
  have upper : Writable code m (base + 0x188) 0x60 := by slot_state region
  refine ⟨?b, ?o, ?ev, ?rest⟩
  case ev =>
    arithmetic_prefix [sp, si, di, dest, source, dy, sy, dz, BitVec.add_zero]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using inc)
    rfl
  case rest =>
    apply EntryState.advance s hb dep low
    · unfold spills
      slot_state region
    · repeat' apply Values.Prefix.push
      exact Values.Prefix.refl _
    all_goals
      intros
      first | (exfalso; first | contradiction | omega) |
        (segment_words [↓arithmeticRead, si, di, sp, dest, source, dy, sy, dz] <;> rfl)))

open Lean Elab Tactic in
elab "add_entry_range " lo:num " through " hi:num : tactic => do
  for i in [lo.getNat + 1 : hi.getNat] do
    let block := mkIdent (`K256.Proofs.Generate.LIR ++ Name.mkSimple s!"b_l10a410_{i}")
    evalTactic (← `(tactic| refine EntrySegment.trans (c := $block) (by add_entry_segment) ?_))
  evalTactic (← `(tactic| add_entry_segment))

set_option maxHeartbeats 1600000 in
private theorem entry1 : EntrySegment b_l10a410_1 b_l10a410_5 := by
  add_entry_range 1 through 5

set_option maxHeartbeats 1600000 in
private theorem entry5 : EntrySegment b_l10a410_5 b_l10a410_9 := by
  add_entry_range 5 through 9

set_option maxHeartbeats 1600000 in
private theorem entry9 : EntrySegment b_l10a410_9 b_l10a410_13 := by
  add_entry_range 9 through 13

set_option maxHeartbeats 1600000 in
private theorem entry13 : EntrySegment b_l10a410_13 b_l10a410_17 := by
  add_entry_range 13 through 17

set_option maxHeartbeats 1600000 in
private theorem entry17 : EntrySegment b_l10a410_17 b_l10a410_21 := by
  add_entry_range 17 through 21

set_option maxHeartbeats 1600000 in
private theorem entry21 : EntrySegment b_l10a410_21 b_l10a410_25 := by
  add_entry_range 21 through 25

set_option maxHeartbeats 1600000 in
private theorem entry25 : EntrySegment b_l10a410_25 b_l10a410_27 := by
  add_entry_range 25 through 27

set_option linter.unusedVariables false in
theorem enterBody {code : CodeMap} (included : ∀ a ∈ fnCode, a ∈ code)
    {fr : Activation} {args : Values Value Reg.count} {mem : Ram}
    (atoms : Atom.All code args mem (Fn10a410.frameAt .l10a410 fr))
    (src : Readable mem fr.rsi 120) (dst : Writable code mem fr.rdi 120)
    (srcAbove : fr.rsp.toNat + 8 ≤ fr.rsi.toNat) (dstAbove : fr.rsp.toNat + 8 ≤ fr.rdi.toNat)
    (apart : fr.rdi.toNat + 120 ≤ fr.rsi.toNat ∨ fr.rsi.toNat + 120 ≤ fr.rdi.toNat) :
    ∃ b m, b_l10a410.eval (dialect code) args mem = b_l10a410_27.eval (dialect code) b m ∧
      RamWriteFrame mem m (regions fr) ∧ AtBody fr b m := by
  obtain ⟨b, m, ev, hf, st⟩ := prologue included atoms src dst
  simp only [Fn10a410.frameAt, Fn10a410.frameAtG0, Atom.All, Atom.Holds] at atoms
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rr, _, _, win, room, _⟩ := atoms
  have run : EntrySegment b_l10a410_1 b_l10a410_27 :=
    entry1.trans (entry5.trans (entry9.trans (entry13.trans (entry17.trans (entry21.trans entry25)))))
  obtain ⟨c, p, ev', hf', st'⟩ := run included st (win.of_frame hf) (src.of_frame hf)
    (dst.of_frame hf) (by omega) rr.low
  exact ⟨c, p, ev.trans ev', hf.trans hf' (fun r hr => ⟨r, hr, Nat.le_refl _, Nat.le_refl _⟩),
    st'.toAtBody⟩

end K256.Proofs.Generate.Generator.Multiply.AddFrame
