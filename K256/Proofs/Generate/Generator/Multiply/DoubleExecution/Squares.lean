import K256.Proofs.Generate.Generator.Multiply.DoubleExecution.SquareInterface
import K256.Proofs.ParseSignature.Call
import K256.Proofs.Generate.Generator.Entry
import K256.Proofs.Generate.Serialize.Transfer.Relabel
import K256.Proofs.Sec1.Square.Contract
import K256.Proofs.Sec1.Serialize.Layout

namespace K256.Proofs.Generate.Generator.Multiply

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR Common.Field

private def squareLabel : Sec1.LIR.Label → Option Label
  | .l1145f0 => some .l1145f0
  | _ => none

set_option maxRecDepth 4096 in
private theorem squareBlocks (a : Sec1.LIR.Label) (b : Label) (h : squareLabel a = some b) :
    Serialize.Relabel.block squareLabel (Sec1.LIR.program.blocks a) =
      Serialize.Relabel.block some (program.blocks b) := by
  cases a <;> rename_i l <;> cases l <;> cases h <;> rfl

private def squareScratch (i : Nat) : Bool := i == 1 || i == 2 || i == 8 || i == 9

private def squareArgs (a : Registers) : Registers :=
  Vector.ofFn fun i => if squareScratch i.val then ⟨64, 0⟩ else a[i]

private def operandsAvoid {n k : Nat} (xs : Vector (Fin n) k) : Bool :=
  xs.toList.all fun i => !squareScratch i.val

private def blockAvoid {n : Nat} : Block Op Label signature Reg.count n → Bool
  | .letOp _ xs rest => operandsAvoid xs && blockAvoid rest
  | .terminate (.ret xs tag) => operandsAvoid xs && (tag.map fun i => !squareScratch i.val).getD true
  | .terminate _ => false

private def Agree {n : Nat} (a b : Values Value n) : Prop :=
  ∀ i : Fin n, squareScratch i.val = false → a[i] = b[i]

private theorem select_agree {n k : Nat} {xs : Vector (Fin n) k} {a b : Values Value n}
    (hxs : operandsAvoid xs = true) (h : Agree a b) : a.select xs = b.select xs := by
  apply Vector.ext
  intro i hi
  simp only [Values.getElem_select]
  apply h
  have := (List.all_eq_true.mp hxs) xs[i] (by
    rw [← Vector.getElem_toList (h := by simpa only [Vector.length_toList] using hi)]
    exact List.getElem_mem _)
  cases he : squareScratch xs[i].val <;> simp_all

private theorem agree_push {n : Nat} {a b : Values Value n} (h : Agree a b)
    (x : Value) : Agree (a.push x) (b.push x) := by
  intro i hi
  simp only [Fin.getElem_fin, Vector.getElem_push]
  split
  · exact h ⟨i.val, ‹i.val < n›⟩ hi
  · rfl

private theorem eval_agree {n : Nat} (block : Block Op Label signature Reg.count n)
    (avoid : blockAvoid block = true) {a b : Values Value n} (agree : Agree a b) (m : Ram) :
    block.eval (dialect Extracted.programImage) a m =
      block.eval (dialect Extracted.programImage) b m := by
  induction block generalizing m with
  | letOp op xs rest ih =>
    have ⟨hx, hr⟩ := Bool.and_eq_true_iff.mp avoid
    simp only [Block.eval, select_agree hx agree]
    split
    · exact ih hr (agree_push agree _) _
    · rfl
  | terminate t =>
    cases t <;> try simp [blockAvoid] at avoid
    case ret xs tag =>
      have ⟨hx, ht⟩ := avoid
      simp only [Block.eval, Terminator.eval, select_agree hx agree]
      cases tag with
      | none => rfl
      | some i =>
        have hi : squareScratch i.val = false := by cases he : squareScratch i.val <;> simp_all
        simp only [Option.map_some, agree i hi]

set_option maxRecDepth 4096 in
private theorem squareStep (a : Registers) (m : Ram) :
    program.step (dialect Extracted.programImage) ⟨⟨.l1145f0, a, m⟩, []⟩ =
      program.step (dialect Extracted.programImage) ⟨⟨.l1145f0, squareArgs a, m⟩, []⟩ := by
  have agree : Agree a (squareArgs a) := by
    intro i hi
    simp only [squareArgs, Fin.getElem_fin, Vector.getElem_ofFn, hi, Bool.false_eq_true, ite_false]
  exact congrArg (fun t => t.next (dialect Extracted.programImage) []) <|
    eval_agree b_l1145f0 (by decide +kernel) agree m

private theorem value_of_width (v : Value) {n : Nat} (h : v.width = n) :
    v = ⟨n, v.get n⟩ := by
  cases v with
  | mk width bits =>
    change width = n at h
    subst n
    simp only [Value.get, BitVec.setWidth_eq]

private def savedRegs : List Nat := [3, 5, 12, 13, 14, 15, 22, 39, 50, 51]

set_option maxHeartbeats 700000 in
private theorem squareCall {a : Registers} {m : Ram} {sp src dst ret : BitVec 64} {words : Limbs}
    (rsp : a[4] = ⟨64, sp⟩) (rsi : a[6] = ⟨64, src⟩) (rdi : a[7] = ⟨64, dst⟩)
    (df : a[22] = ⟨1, 0⟩) (saved : SavedWidths a)
    (mx : a[39].width = 32) (ft : a[50].width = 16) (fc : a[51].width = 16)
    (win : Writable Extracted.programImage m (sp - 104) 112)
    (source : Readable m src 40) (dest : Writable Extracted.programImage m dst 40)
    (srcAbove : sp.toNat + 8 ≤ src.toNat) (dstAbove : sp.toNat + 8 ≤ dst.toNat)
    (apart : dst.toNat + 40 ≤ src.toNat ∨ src.toNat + 40 ≤ dst.toNat)
    (dstAlign : dst.toNat % 8 = 0) (align : sp.toNat % 16 = 8) (room : 104 ≤ sp.toNat)
    (slot : memLoad m sp 64 = ret) (retLow : ret.toNat < 2^32) (input : WordsAt m src 64 words) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l1145f0, a, m⟩, []⟩ out ∧
      out.tag = some ⟨64, ret⟩ ∧ out.values[4] = ⟨64, sp + 8⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ savedRegs → out.values[i] = a[i]) ∧
      RamWriteFrame m out.store [⟨(sp - 104).toNat, 104⟩, ⟨dst.toNat, 40⟩] ∧
      WordsAt out.store dst 64 (squareWords words) := by
  let fr : Activation := {
    original := m, rsp := sp, low := sp - 104, ret := ret, rdi := dst, rsi := src
    rbx := a[3].get 64, rbp := a[5].get 64, r12 := a[12].get 64, r13 := a[13].get 64
    r14 := a[14].get 64, r15 := a[15].get 64, rdx := 0, rcx := 0, r8 := 0, r9 := 0
    mxcsr := a[39].get 32, ftw := a[50].get 16, fcw := a[51].get 16, fs := default }
  let old := Vector.ofFn fun i : Fin 5 => memLoad m (wordAddr dst 64 i.val) 64
  have oldAt : WordsAt m dst 64 old := by
    intro i hi
    simp only [old, Vector.getElem_ofFn]
  have hs : (sp - 104).toNat + 104 = sp.toNat := by
    rw [BitVec.toNat_sub_of_le (by exact room : (104 : Word) ≤ sp)]
    exact Nat.sub_add_cancel room
  have ht := Sec1.Serialize.writable_text_apart win (by decide)
  have hx := Sec1.Serialize.writable_text_apart dest (by decide)
  have hregs (i : Fin Reg.count) (hi : i.val ∈ Activation.calleeSavedNumbers) :
      a[i] = ⟨64, a[i].get 64⟩ := value_of_width _ (saved i hi)
  have entry : Atom.All Extracted.programImage (squareArgs a) m
      (Sec1.LIR.Fn1145f0.frameAt .l1145f0 fr) := by
    change Atom.All _ _ _ (Sec1.LIR.Fn1145f0.frameAtG0 .l1145f0 fr)
    simp only [Sec1.LIR.Fn1145f0.frameAtG0, Atom.All, Atom.Holds, Atom.gpr, Fin.getElem_fin]
    have same (i : Fin Reg.count) (hi : squareScratch i.val = false) :
        (squareArgs a)[i] = a[i] := by
      simp only [squareArgs, Fin.getElem_fin, Vector.getElem_ofFn, hi, Bool.false_eq_true, ite_false]
    refine ⟨(same 4 (by decide)).trans rsp, (same 22 (by decide)).trans df, ?_, ?_,
      (same 3 (by decide)).trans (hregs 3 (by decide)),
      (same 5 (by decide)).trans (hregs 5 (by decide)),
      (same 6 (by decide)).trans rsi, (same 7 (by decide)).trans rdi, ?_, ?_,
      (same 12 (by decide)).trans (hregs 12 (by decide)),
      (same 13 (by decide)).trans (hregs 13 (by decide)),
      (same 14 (by decide)).trans (hregs 14 (by decide)),
      (same 15 (by decide)).trans (hregs 15 (by decide)),
      (same 39 (by decide)).trans (value_of_width _ mx),
      (same 50 (by decide)).trans (value_of_width _ ft),
      (same 51 (by decide)).trans (value_of_width _ fc),
      win.readable.sub (a := sp) (by omega) (by omega), slot, retLow,
      win.sub (a := sp - 104) (n := 104) (Nat.le_refl _) (by omega), Nat.le_of_eq hs, align, trivial⟩
    all_goals
      simp only [squareArgs, Vector.getElem_ofFn, fr]
      rfl
  have core : Atom.All Extracted.programImage (squareArgs a) m
      (Sec1.Square.core.atoms .entry () fr (words, old)) := by
    exact ⟨input, source, oldAt, dest, dstAlign, apart, Or.inr srcAbove,
      (by dsimp only [Atom.Holds, fr]; omega), (by dsimp only [Atom.Holds, fr]; omega),
      Or.inr dstAbove, trivial⟩
  have rel : Sec1.Square.layout.Rel Extracted.programImage (fr, ()) ⟨.entry, #v[], (words, old)⟩
      ⟨.l1145f0, squareArgs a, m⟩ :=
    ⟨rfl, ⟨_, rfl, rfl, (Atom.all_append _ _).2 ⟨entry, core⟩⟩, RamWriteFrame.refl _ _⟩
  obtain ⟨out, run, post, done_⟩ := Sec1.Square.call Extracted.programImage fr (words, old) _ rel
  obtain ⟨tag, ⟨result, heq, atoms⟩, frame⟩ := post
  have hr := congrArg CFG.Output.store heq
  change (words, squareWords words) = result at hr
  subst result
  change Atom.All _ _ _ (Sec1.LIR.Fn1145f0.doneAt fr ++ Sec1.Square.core.done () fr (words, squareWords words)) at atoms
  obtain ⟨_, _, _, output, _⟩ := (Atom.all_append _ _).1 atoms
  change Atom.All _ _ _ (Sec1.LIR.Fn1145f0.doneAt fr) at done_
  simp only [Sec1.LIR.Fn1145f0.doneAt, Atom.All, Atom.Holds, Atom.gpr, Fin.getElem_fin] at done_
  obtain ⟨hsp, hdf, h3, h5, h12, h13, h14, h15, h39, h50, h51, _⟩ := done_
  have gen : program.Exec (dialect Extracted.programImage) ⟨⟨.l1145f0, squareArgs a, m⟩, []⟩ out :=
    Serialize.Relabel.exec squareBlocks run rfl
  refine ⟨out, ?_, tag, hsp, ?_, ?_, output⟩
  · cases gen with
    | done h => exact .done ((squareStep a m).trans h)
    | next h rest => exact .next ((squareStep a m).trans h) rest
  · rintro ⟨i, hi⟩ h
    simp only [savedRegs, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact h3.trans (hregs 3 (by decide)).symm
      | exact h5.trans (hregs 5 (by decide)).symm
      | exact h12.trans (hregs 12 (by decide)).symm
      | exact h13.trans (hregs 13 (by decide)).symm
      | exact h14.trans (hregs 14 (by decide)).symm
      | exact h15.trans (hregs 15 (by decide)).symm
      | exact hdf.trans df.symm
      | exact h39.trans (value_of_width _ mx).symm
      | exact h50.trans (value_of_width _ ft).symm
      | exact h51.trans (value_of_width _ fc).symm
  · change RamWriteFrame m out.store [⟨(sp - 104).toNat, sp.toNat - (sp - 104).toNat⟩, ⟨dst.toNat, 40⟩] at frame
    rwa [show sp.toNat - (sp - 104).toNat = 104 by omega] at frame

private def countWrites (sp : BitVec 64) : List MemoryRegion :=
  [⟨(sp - 8).toNat, 8⟩, ⟨(sp + 0x1bc).toNat, 4⟩]

private def copyWrites (sp : BitVec 64) : List MemoryRegion :=
  [⟨(sp - 8).toNat, 8⟩, ⟨(sp + 0x30).toNat, 40⟩, ⟨(sp + 0x88).toNat, 8⟩]

private theorem copies_at {m : Ram} {sp : BitVec 64} {words : Limbs}
    (h0 : memLoad m (sp + 0x88) 64 = words[0])
    (h1 : memLoad m (sp + 0x48) 64 = words[1])
    (h2 : memLoad m (sp + 0x50) 64 = words[2])
    (h3 : memLoad m (sp + 0x30) 64 = words[3])
    (h4 : memLoad m (sp + 0x40) 64 = words[4]) (i : Fin 5) :
    memLoad m (sp + squareCopies[i]) 64 = words[i] := by
  rcases i with ⟨i, hi⟩
  have cases_i : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases cases_i with rfl | rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

set_option maxRecDepth 2048 in
private theorem firstSquareSetup {a : Registers} {m : Ram} {sp : BitVec 64} {count : BitVec 32}
    (rsp : a[4].get 64 = sp) (ecx : a[1].get 32 = count)
    (window : Writable Extracted.programImage m (sp - 8) 0x1c8) :
    ∃ b n, program.runBlock (dialect Extracted.programImage) ⟨.l11d810, a, m⟩ =
      .call ⟨.l1145f0, b, n⟩ (callFrame .l11d82c 0x11d82c) ∧
      b[4] = ⟨64, sp - 8⟩ ∧ b[6] = ⟨64, sp + 0x150⟩ ∧ b[7] = ⟨64, sp + 0x850⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ savedRegs → b[i] = a[i]) ∧
      memLoad n (sp - 8) 64 = 0x11d82c ∧ memLoad n (sp + 0x1bc) 32 = count ∧
      RamWriteFrame m n (countWrites sp) := by
  have ecx' : (a[1].get 64).setWidth 32 = count :=
    (BitVec.setWidth_setWidth_of_le _ (by decide)).trans ecx
  refine ⟨?_, ?_, ?run, ?post⟩
  case run =>
    arithmetic_segment using code_l11d810 [rsp, ecx', callFrame]
  case post =>
    refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · rintro ⟨i, hi⟩ h
      simp only [savedRegs, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · segment_words []
    · segment_words [ecx']
    · have base := window.readable.low
      have q : (sp + 0x1bc).toNat = (sp - 8).toNat + 0x1c4 :=
        toNat_of_offsets (n := 4) rfl (addr_sub sp 8) base (by decide)
      refine ((RamWriteFrame.refl m _).memStore _ ?_).memStore _ ?_
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Nat.le_refl _, Nat.le_refl _, by omega⟩
      · exact ⟨_, List.mem_cons_self, Nat.le_refl _, Nat.le_refl _, by omega⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 500000 in
private theorem secondSquareSetup {a : Registers} {m : Ram} {sp : BitVec 64} {words : Limbs}
    (rsp : a[4].get 64 = sp) (r12 : a[12].get 64 = sp + 0x490)
    (localWrite : Writable Extracted.programImage m (sp - 8) 0x98)
    (sourceRead : Readable m (sp + 0x850) 40)
    (wordsAt : WordsAt m (sp + 0x850) 64 words) :
    ∃ b n, program.runBlock (dialect Extracted.programImage) ⟨.l11d82c, a, m⟩ =
      .call ⟨.l1145f0, b, n⟩ (callFrame .l11d880 0x11d880) ∧
      b[4] = ⟨64, sp - 8⟩ ∧ b[6] = ⟨64, sp + 0x178⟩ ∧ b[7] = ⟨64, sp + 0x490⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ savedRegs → b[i] = a[i]) ∧
      memLoad n (sp - 8) 64 = 0x11d880 ∧
      (∀ i : Fin 5, memLoad n (sp + squareCopies[i]) 64 = words[i]) ∧
      RamWriteFrame m n (copyWrites sp) := by
  have word (i : Nat) (hi : i < 5) :
      memLoad m (sp + (0x850 + BitVec.ofNat 64 (8*i))) 64 = words[i] := by
    rw [← BitVec.add_assoc]
    exact wordsAt i hi
  have w0 : memLoad m (sp + 0x850) 64 = words[0] := word 0 (by decide)
  have w1 : memLoad m (sp + 0x858) 64 = words[1] := word 1 (by decide)
  have w2 : memLoad m (sp + 0x860) 64 = words[2] := word 2 (by decide)
  have w3 : memLoad m (sp + 0x868) 64 = words[3] := word 3 (by decide)
  have w4 : memLoad m (sp + 0x870) 64 = words[4] := word 4 (by decide)
  refine ⟨?_, ?_, ?run, ?post⟩
  case run =>
    arithmetic_segment using code_l11d82c [rsp, r12, callFrame, w0, w1, w2, w3, w4]
  case post =>
    refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · rintro ⟨i, hi⟩ h
      simp only [savedRegs, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · segment_words []
    · apply copies_at
      all_goals lifted_word_reads [w0, w1, w2, w3, w4] <;> lifted_word_eq []
    · have base := localWrite.readable.low
      have start : (sp + 0x30).toNat = (sp - 8).toNat + 0x38 :=
        toNat_of_offsets (n := 8) rfl (addr_sub sp 8) base (by decide)
      have copySlot (off : BitVec 64) (hmin : 0x30 ≤ off.toNat) (hmax : off.toNat ≤ 0x50)
          (fit : (off - (0 - 8)).toNat + 8 ≤ 0x98) :
          InRegions (copyWrites sp) (sp + off) 8 := by
        have addr := toNat_of_offsets rfl (addr_sub sp 8) base fit
        have offset : (off - (0 - 8)).toNat = off.toNat + 8 := by
          rw [show off - (0 - 8) = off + 8 by bv_omega, BitVec.toNat_add]
          exact Nat.mod_eq_of_lt (by change off.toNat + 8 < 2^64; omega)
        rw [offset] at addr
        refine ⟨⟨(sp + 0x30).toNat, 40⟩, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
        change (sp + 0x30).toNat ≤ (sp + off).toNat ∧
          (sp + off).toNat + 8 ≤ (sp + 0x30).toNat + 40 ∧ (sp + off).toNat + 8 ≤ 2^64
        omega
      have far : (sp + 0x88).toNat = (sp - 8).toNat + 0x90 :=
        toNat_of_offsets (n := 8) rfl (addr_sub sp 8) base (by decide)
      have g88 : InRegions (copyWrites sp) (sp + 0x88) 8 :=
        ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
          Nat.le_refl _, Nat.le_refl _, by omega⟩
      have gret : InRegions (copyWrites sp) (sp - 8) 8 :=
        ⟨_, List.mem_cons_self, Nat.le_refl _, Nat.le_refl _, by omega⟩
      have f := (RamWriteFrame.refl m _).memStore words[0] g88
      have f := f.memStore words[1] (copySlot 0x48 (by decide) (by decide) (by decide))
      have f := f.memStore words[2] (copySlot 0x50 (by decide) (by decide) (by decide))
      have f := f.memStore words[3] (copySlot 0x30 (by decide) (by decide) (by decide))
      have f := f.memStore words[4] (copySlot 0x40 (by decide) (by decide) (by decide))
      exact f.memStore (0x11d880 : BitVec 64) gret

private theorem squareResumes {caller callee : lifted.Location} {resume : Label} {ret : BitVec 64}
    {out : Output Value Ram Reg.count}
    (step : program.runBlock (dialect Extracted.programImage) caller = .call callee (callFrame resume ret))
    (exec : program.Exec (dialect Extracted.programImage) ⟨callee, []⟩ out)
    (tag : out.tag = some ⟨64, ret⟩) :
    (program.sem (dialect Extracted.programImage)).Reaches
      ⟨caller, []⟩ ⟨⟨resume, out.values, out.store⟩, []⟩ := by
  apply Star.step (b := ⟨callee, [callFrame resume ret]⟩)
  · change program.step _ _ = _
    simp only [Program.step, step, Transfer.next]
  · exact ParseSignature.exec_reaches_resume exec (callFrame resume ret) [] (by
      rw [tag]
      change decide ((⟨64, ret⟩ : Value) = ⟨64, ret⟩) = true
      simp)

private theorem savedSub (i : Fin Reg.count) (hi : i.val ∈ Activation.calleeSavedNumbers) :
    i.val ∈ savedRegs := by
  simp only [Activation.calleeSavedNumbers, savedRegs, List.mem_cons, List.not_mem_nil, or_false] at *
  rcases hi with h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))

private theorem copyOffsetBound : ∀ i : Fin 5, (squareCopies[i]).toNat ≤ 0x88 := by
  decide +kernel

private theorem parentDepth {sp : BitVec 64} (h : (sp - 0xed8).toNat + 0xed8 ≤ 2^32) :
    0xed8 ≤ sp.toNat := by
  by_cases hr : 0xed8 ≤ sp.toNat
  · exact hr
  · have hr' : sp < (0xed8 : BitVec 64) := Nat.lt_of_not_ge hr
    have eq := BitVec.toNat_sub_of_lt hr'
    change (sp - 0xed8).toNat = 2^64 - (0xed8 - sp.toNat) at eq
    omega

private theorem atPlus {sp k : BitVec 64} (hs : sp.toNat + 0xcb8 ≤ 2^32)
    (hk : k.toNat ≤ 0xcb8) : (sp + k).toNat = sp.toNat + k.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]

private theorem atMinus {sp k : BitVec 64} (hs : 0x220 ≤ sp.toNat)
    (hk : k.toNat ≤ 0x220) : (sp - k).toNat = sp.toNat - k.toNat :=
  BitVec.toNat_sub_of_le (by exact Nat.le_trans hk hs)

private theorem writesWiden (sp : BitVec 64) (hs : 0x220 ≤ sp.toNat) :
    RegionsWithin (countWrites sp) (squareWrites sp) ∧
    RegionsWithin (copyWrites sp) (squareWrites sp) := by
  constructor
  · intro r hr
    simp only [countWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · refine ⟨_, List.mem_cons_self, ?_, ?_⟩
      all_goals
        simp (disch := decide) only [atMinus hs, BitVec.reduceToNat]
        omega
    · exact ⟨_, by simp [squareWrites], Nat.le_refl _, Nat.le_refl _⟩
  · intro r hr
    simp only [copyWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · refine ⟨_, List.mem_cons_self, ?_, ?_⟩
      all_goals
        simp (disch := decide) only [atMinus hs, BitVec.reduceToNat]
        omega
    · exact ⟨_, by simp [squareWrites], Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨_, by simp [squareWrites], Nat.le_refl _, Nat.le_refl _⟩

private theorem childWiden {sp : BitVec 64}
    (k : BitVec 64) (hk : k = 0x850 ∨ k = 0x490) :
    RegionsWithin [⟨(sp - 8 - 104).toNat, 104⟩, ⟨(sp + k).toNat, 40⟩] (squareWrites sp) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · refine ⟨_, List.mem_cons_self, ?_, ?_⟩
    · rw [show sp - 8 - 104 = sp - 112 by bv_omega]
      exact Nat.le_refl _
    · rw [show sp - 8 - 104 = sp - 112 by bv_omega]
      change (sp - 112).toNat + 104 ≤ (sp - 112).toNat + 112
      omega
  · rcases hk with rfl | rfl <;> exact ⟨_, by simp [squareWrites], Nat.le_refl _, Nat.le_refl _⟩

private theorem inputSquareWords {m n : Ram} {sp : BitVec 64} {w : Limbs}
    (hs : 0x220 ≤ sp.toNat) (hl : sp.toNat + 0xcb8 ≤ 2^32)
    (frame : RamWriteFrame m n (squareWrites sp))
    (k : BitVec 64) (hk : k = 0x150 ∨ k = 0x178) (input : WordsAt m (sp + k) 64 w) :
    WordsAt n (sp + k) 64 w := by
  intro i hi
  refine (frame.memLoad_eq ?_).trans (input i hi)
  have addr : wordAddr (sp + k) 64 i = sp + (k + BitVec.ofNat 64 (8*i)) := by
    simp only [wordAddr, BitVec.add_assoc]
  have hk' : k.toNat = 0x150 ∨ k.toNat = 0x178 := by
    rcases hk with rfl | rfl <;> decide
  have off : (k + BitVec.ofNat 64 (8*i)).toNat = k.toNat + 8*i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 8*i) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  rw [addr, Outside, atPlus hl (by rw [off]; omega), off]
  refine ⟨by omega, ?_⟩
  intro r hr
  simp only [squareWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp (disch := decide) only [atMinus hs, atPlus hl, BitVec.reduceToNat]
    omega

set_option maxHeartbeats 700000 in
set_option maxRecDepth 2048 in
theorem prepareSquares : SquarePreparation := by
  intro fr a m y z count sp atoms widths ecx mask temp yin zin
  change Atom.All _ _ _ (Fn11c880.frameAtG2 .l11d810 fr) at atoms
  simp only [Fn11c880.frameAtG2, Atom.All, Atom.Holds, Atom.gpr, Fin.getElem_fin] at atoms
  obtain ⟨rsp, df, mx, ft, fc, bx, s12, s13, s14, s15, bp, retRead, retVal,
    retLow, stack, floor, align, gotRead, got, gotRead', got', gotGap, _⟩ := atoms
  have hlow := stack.readable.low
  have room := parentDepth hlow
  have lowNat : (fr.rsp - 0xed8).toNat = fr.rsp.toNat - 0xed8 :=
    BitVec.toNat_sub_of_le (by exact room)
  have spNat : sp.toNat = fr.rsp.toNat - 0xcb8 :=
    BitVec.toNat_sub_of_le (by exact show 0xcb8 ≤ fr.rsp.toNat by omega)
  have hroom : 0x220 ≤ sp.toNat := by rw [spNat]; omega
  have hhigh : sp.toNat + 0xcb8 ≤ 2^32 := by rw [spNat]; omega
  have align16 : sp.toNat % 16 = 0 := by rw [spNat]; omega
  have childAlign : (sp - 8).toNat % 16 = 8 := by
    rw [atMinus (k := 8) hroom (by decide)]
    change (sp.toNat - 8) % 16 = 8
    omega
  have childRoom : 104 ≤ (sp - 8).toNat := by
    rw [atMinus (k := 8) hroom (by decide)]
    change 104 ≤ sp.toNat - 8
    omega
  have childLow : sp - 8 - 104 = sp - 112 := by bv_omega
  have lowEq : fr.rsp - 0xed8 = sp - 0x220 := by dsimp [sp]; bv_omega
  have area := lowEq ▸ stack
  have win {n : Ram} {rs : List MemoryRegion} (write : RamWriteFrame m n rs)
      {a0 c : BitVec 64} {len : Nat} (eq : a0 = sp + c)
      (fit : (c - (0 - 0x220)).toNat + len ≤ 0xed8) :
      Writable Extracted.programImage n a0 len :=
    (area.of_frame write).of_offsets eq (addr_sub _ _) fit
  have r5 : a[5] = ⟨64, 0x1000003d10⟩ := by
    rw [← mask]
    exact value_of_width a[5] (widths 5 (by decide))
  have r0 : a[4].get 64 = sp := congrArg (Value.get 64) rsp
  let writes := squareWrites sp
  have widen := writesWiden sp hroom
  have origin : RamWriteFrame m m writes := RamWriteFrame.refl _ _
  obtain ⟨c, m₁, run₁, c4, c6, c7, keep₁, ret₁, count₁, f₁⟩ :=
    firstSquareSetup r0 ecx (win origin (addr_sub _ _) (by decide))
  have f₁' := origin.trans f₁ widen.1
  have saved {x x' : Registers} (h : ∀ i : Fin Reg.count, i.val ∈ savedRegs → x'[i] = x[i])
      (w : SavedWidths x) : SavedWidths x' := fun i hi => congrArg Value.width (h i (savedSub i hi)) |>.trans (w i hi)
  have win₁ : Writable Extracted.programImage m₁ (sp - 8 - 104) 112 := by
    rw [childLow]
    exact win f₁' (addr_sub _ _) (by decide)
  have ay : WordsAt m₁ (sp + 0x150) 64 y := inputSquareWords hroom hhigh f₁' _ (Or.inl rfl) yin
  obtain ⟨o₁, e₁, t₁, sp₁, s₁, g₁, y₁⟩ :=
    squareCall c4 c6 c7 ((keep₁ 22 (by decide)).trans df) (saved keep₁ widths)
      (congrArg Value.width ((keep₁ 39 (by decide)).trans mx))
      (congrArg Value.width ((keep₁ 50 (by decide)).trans ft))
      (congrArg Value.width ((keep₁ 51 (by decide)).trans fc))
      win₁ (win f₁' rfl (by decide) |>.readable) (win f₁' rfl (by decide))
      (by simp (disch := decide) only [atMinus hroom, atPlus hhigh, BitVec.reduceToNat]; omega)
      (by simp (disch := decide) only [atMinus hroom, atPlus hhigh, BitVec.reduceToNat]; omega)
      (Or.inr (by simp (disch := decide) only [atPlus hhigh, BitVec.reduceToNat]; omega))
      (by simp (disch := decide) only [atPlus hhigh, BitVec.reduceToNat]; omega)
      childAlign childRoom ret₁ (by decide) ay
  have g₁' := f₁'.trans g₁ (childWiden 0x850 (Or.inl rfl))
  have first := squareResumes run₁ e₁ t₁
  have sp₁' : o₁.values[4].get 64 = sp := by
    rw [sp₁]
    exact BitVec.sub_add_cancel _ _
  have r12₁ : o₁.values[12].get 64 = sp + 0x490 :=
    (congrArg (Value.get 64) ((s₁ 12 (by decide)).trans (keep₁ 12 (by decide)))).trans temp
  obtain ⟨d, m₂, run₂, d4, d6, d7, keep₂, ret₂, copies, f₂⟩ :=
    secondSquareSetup sp₁' r12₁ (win g₁' (addr_sub _ _) (by decide))
      (win g₁' rfl (by decide) |>.readable) y₁
  have f₂' := g₁'.trans f₂ widen.2
  have win₂ : Writable Extracted.programImage m₂ (sp - 8 - 104) 112 := by
    rw [childLow]
    exact win f₂' (addr_sub _ _) (by decide)
  have az : WordsAt m₂ (sp + 0x178) 64 z := inputSquareWords hroom hhigh f₂' _ (Or.inr rfl) zin
  have kept (i : Fin Reg.count) (hi : i.val ∈ savedRegs) : d[i] = a[i] :=
    (keep₂ i hi).trans ((s₁ i hi).trans (keep₁ i hi))
  obtain ⟨o₂, e₂, t₂, sp₂, s₂, g₂, z₂⟩ :=
    squareCall d4 d6 d7 ((kept 22 (by decide)).trans df) (saved kept widths)
      (congrArg Value.width ((kept 39 (by decide)).trans mx))
      (congrArg Value.width ((kept 50 (by decide)).trans ft))
      (congrArg Value.width ((kept 51 (by decide)).trans fc))
      win₂ (win f₂' rfl (by decide) |>.readable) (win f₂' rfl (by decide))
      (by simp (disch := decide) only [atMinus hroom, atPlus hhigh, BitVec.reduceToNat]; omega)
      (by simp (disch := decide) only [atMinus hroom, atPlus hhigh, BitVec.reduceToNat]; omega)
      (Or.inr (by simp (disch := decide) only [atPlus hhigh, BitVec.reduceToNat]; omega))
      (by simp (disch := decide) only [atPlus hhigh, BitVec.reduceToNat]; omega)
      childAlign childRoom ret₂ (by decide) az
  have result := f₂'.trans g₂ (childWiden 0x490 (Or.inr rfl))
  have second := squareResumes run₂ e₂ t₂
  have finalReg (i : Fin Reg.count) (hi : i.val ∈ savedRegs) : o₂.values[i] = a[i] :=
    (s₂ i hi).trans (kept i hi)
  have count₁' : memLoad o₁.store (sp + 0x1bc) 32 = count := by
    rw [g₁.memLoad_eq]
    · exact count₁
    · rw [childLow]
      simp (disch := decide) only [Outside, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Nat.reduceDiv, atMinus hroom, atPlus hhigh, BitVec.reduceToNat]
      omega
  have count₂ : memLoad m₂ (sp + 0x1bc) 32 = count := by
    rw [f₂.memLoad_eq]
    · exact count₁'
    · simp (disch := decide) only [copyWrites, Outside, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Nat.reduceDiv, atMinus hroom, atPlus hhigh, BitVec.reduceToNat]
      omega
  refine ⟨o₂.values, o₂.store, first.trans second, ?_, (finalReg 5 (by decide)).trans r5,
    ?_, ?_, z₂, result⟩
  · have saveSlot (off : BitVec 64) (h : off.toNat ≤ 48) :
        memLoad o₂.store (fr.rsp - off) 64 = memLoad m (fr.rsp - off) 64 := by
      apply result.memLoad_eq
      have natOff : (fr.rsp - off).toNat = fr.rsp.toNat - off.toNat :=
        BitVec.toNat_sub_of_le (by exact show off.toNat ≤ fr.rsp.toNat by omega)
      simp (disch := decide) only [writes, squareWrites, Outside, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Nat.reduceDiv, atMinus hroom, atPlus hhigh, BitVec.reduceToNat, natOff]
      omega
    have protectGot {p : BitVec 64} (lo : 0x203de0 ≤ p.toNat) (hi : p.toNat + 8 ≤ 0x203e28) :
        memLoad o₂.store p 64 = memLoad m p 64 := by
      apply result.memLoad_eq
      simp (disch := decide) only [writes, squareWrites, Outside, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Nat.reduceDiv, atMinus hroom, atPlus hhigh, BitVec.reduceToNat]
      omega
    change Atom.All _ _ _ (Fn11c880.frameAtG2 .l11d880 fr)
    simp only [Fn11c880.frameAtG2, Atom.All, Atom.Holds, Atom.gpr, Fin.getElem_fin]
    refine ⟨?_, (finalReg 22 (by decide)).trans df, (finalReg 39 (by decide)).trans mx,
      (finalReg 50 (by decide)).trans ft, (finalReg 51 (by decide)).trans fc,
      (saveSlot 48 (by decide)).trans bx, (saveSlot 40 (by decide)).trans s12,
      (saveSlot 32 (by decide)).trans s13, (saveSlot 24 (by decide)).trans s14,
      (saveSlot 16 (by decide)).trans s15, (saveSlot 8 (by decide)).trans bp, retRead.of_frame result,
      ?_, retLow, stack.of_frame result, floor, align, gotRead.of_frame result,
      (protectGot (by decide) (by decide)).trans got, gotRead'.of_frame result,
      (protectGot (by decide) (by decide)).trans got', gotGap, trivial⟩
    · rwa [BitVec.sub_add_cancel] at sp₂
    · have sameRet : memLoad o₂.store fr.rsp 64 = memLoad m fr.rsp 64 := by
        have zero : fr.rsp - (0 : BitVec 64) = fr.rsp := BitVec.sub_zero _
        simpa only [zero] using saveSlot 0 (by decide)
      exact sameRet.trans retVal
  · rw [g₂.memLoad_eq]
    · exact count₂
    · rw [childLow]
      simp (disch := decide) only [Outside, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Nat.reduceDiv, atMinus hroom, atPlus hhigh, BitVec.reduceToNat]
      omega
  · intro i
    rw [g₂.memLoad_eq]
    · exact copies i
    · rw [childLow]
      have off := copyOffsetBound i
      simp (disch := first | decide | omega) only [Outside, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Nat.reduceDiv, atMinus hroom, atPlus hhigh, BitVec.reduceToNat]
      omega

end K256.Proofs.Generate.Generator.Multiply
