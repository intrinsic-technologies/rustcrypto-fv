import K256.Proofs.Verify.Core.Affine.Serialize
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Signing.Composition.Attempt.Serializer

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  Ecdh.LIR Common.Field Standards.SECG.ECC

def Kept (a b : Values Value Reg.count) : Prop :=
  ∀ i : Fin Reg.count, i.val ∈ [5, 12, 13, 15, 39, 50, 51] → b[i] = a[i]

private theorem guardedCall {p : Prop} [Decidable p] {t : CFG.Transfer Value Ram Label signature Reg.count}
    {loc frame} (eq : (if p then t else .stuck) = .call loc frame) : t = .call loc frame := by
  split at eq <;> simp_all

private theorem setupKept {a b : Values Value Reg.count} {m n : Ram}
    (run : program.runBlock (dialect Extracted.programImage) ⟨.l120350, a, m⟩ =
      .call ⟨.l114930, b, n⟩ (Ecdh.Output.fieldReturn .l120398 0x120398)) :
    Kept a b := by
  cfg_eval at run
  repeat' replace run := guardedCall run
  cases run
  intro ⟨i, hi⟩ hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

set_option maxHeartbeats 800000 in
private theorem normalize {a : Values Value Reg.count} {m : Ram} {base dst : Word} {w : Limbs}
    (rsp : a[4] = ⟨64, base - 8⟩) (rsi : a[6] = ⟨64, base + 8⟩) (rdi : a[7] = ⟨64, base + 48⟩)
    (rbx : a[3] = ⟨64, dst⟩) (r14 : a[14] = ⟨64, base + 48⟩) (df : a[22] = ⟨1, 0⟩)
    (bp : a[5].width = 64) (r12 : a[12].width = 64) (r13 : a[13].width = 64) (r15 : a[15].width = 64)
    (win : Writable Extracted.programImage m (base - 121) 433) (align : base.toNat % 16 = 0)
    (slot : memLoad m (base - 8) 64 = 0x120398) (input : WordsAt m (base + 8) 64 w) :
    ∃ o, program.Exec (dialect Extracted.programImage) ⟨⟨.l114930, a, m⟩, []⟩ o ∧
      o.tag = some ⟨64, 0x120398⟩ ∧ o.values[4] = ⟨64, base⟩ ∧
      o.values[3] = ⟨64, dst⟩ ∧ o.values[14] = ⟨64, base + 48⟩ ∧ o.values[22] = ⟨1, 0⟩ ∧
      Kept a o.values ∧ o.values[12].width = 64 ∧ o.values[13].width = 64 ∧
      RamWriteFrame m o.store [⟨(base - 121).toNat, 113⟩, ⟨(base + 48).toNat, 40⟩] ∧
      WordsAt o.store (base + 48) 64 (Sec1.Serialize.Normalize.normalize w) := by
  have eqWord (v : Value) (width : v.width = 64) : v = ⟨64, v.get 64⟩ := by
    obtain ⟨w, x⟩ := v
    cases width
    rfl
  have saved (i : Fin Reg.count) (h : i.val ∈ [3, 5, 12, 13, 14, 15]) :
      a[i] = ⟨64, a[i].get 64⟩ := by
    rcases i with ⟨i, hi⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl
    · exact eqWord _ (congrArg Value.width rbx)
    · exact eqWord _ bp
    · exact eqWord _ r12
    · exact eqWord _ r13
    · exact eqWord _ (congrArg Value.width r14)
    · exact eqWord _ r15
  obtain ⟨hbase, hsp, off⟩ := Sec1.Serialize.Coordinates.stackOffsets win.readable.low
  have srcOff := off 8 (by decide)
  have dstOff := off 48 (by decide)
  change (base + 8).toNat = base.toNat + 8 at srcOff
  change (base + 48).toNat = base.toNat + 48 at dstOff
  have low : base - 8 - 113 = base - 121 := by bv_omega
  have stack : Writable Extracted.programImage m (base - 8 - 113) 121 := by
    rw [low]
    exact win.sub (Nat.le_refl _) (by omega)
  obtain ⟨o, run, tag, pop, keep, frame, words⟩ :=
    Generate.Generator.Affine.normalizeCall rsp rsi rdi df saved stack
      (win.readable.of_offsets rfl (addr_sub _ _) (by decide))
      (win.of_offsets rfl (addr_sub _ _) (by decide))
      (by omega) (by omega) (Or.inr (by omega)) (by omega) (by omega) (by omega)
      slot (by decide) input
  have child := Ecdh.Transfer.generateExec (dst := .l114930) (by decide) rfl run
  refine ⟨o, child, tag, by simpa only [BitVec.sub_add_cancel] using pop,
    (keep 3 (by decide)).trans rbx, (keep 14 (by decide)).trans r14, (keep 22 (by decide)).trans df,
    fun i hi => keep i (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
      omega),
    (congrArg Value.width (keep 12 (by decide))).trans r12,
    (congrArg Value.width (keep 13 (by decide))).trans r13,
    (by simpa only [low] using frame), words⟩

set_option maxRecDepth 4096 in
private theorem packingWidths {code : CodeMap} {a : Values Value Reg.count} {m : Ram}
    {out : Output Value Ram Reg.count}
    (dst : a[7].width = 64)
    (run : Sec1.LIR.program.Exec (dialect code) ⟨⟨.l1148d0,a,m⟩, []⟩ out) :
    ParseSignature.ArgumentWidths out.values := by
  let widthOk : CFG.Transfer Value Ram Sec1.LIR.Label signature Reg.count → Prop
    | .returned o => ParseSignature.ArgumentWidths o.values
    | .stuck => True
    | _ => False
  have guard (p : Prop) [Decidable p] (t : CFG.Transfer Value Ram Sec1.LIR.Label signature Reg.count)
      (h : widthOk t) : widthOk (if p then t else .stuck) := by
    split <;> first | exact h | trivial
  have checked : widthOk (Sec1.LIR.program.runBlock (dialect code) ⟨.l1148d0,a,m⟩) := by
    cfg_eval [Sec1.LIR.b_l1148d0_1]
    repeat' apply guard
    intro ⟨i, hi⟩ hm
    simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact dst | rfl
  cases run with
  | done h =>
    change (Sec1.LIR.program.runBlock _ _).next _ [] = _ at h
    generalize ht : Sec1.LIR.program.runBlock (dialect code) ⟨.l1148d0,a,m⟩ = t at checked h
    cases t <;> cases h
    exact checked
  | next h _ =>
    change (Sec1.LIR.program.runBlock _ _).next _ [] = _ at h
    generalize ht : Sec1.LIR.program.runBlock (dialect code) ⟨.l1148d0,a,m⟩ = t at checked h
    cases t <;> first | exact (show False from checked).elim | cases h

set_option maxHeartbeats 1000000 in
private theorem packReturn {a : Values Value Reg.count} {m : Ram} {base dst bx saved14 returnTag : Word} {w : Limbs}
    (rsp : a[4] = ⟨64, base⟩) (rbx : a[3] = ⟨64, dst⟩) (r14 : a[14] = ⟨64, base + 48⟩)
    (df : a[22] = ⟨1, 0⟩)
    (win : Writable Extracted.programImage m (base - 121) 433)
    (dest : Writable Extracted.programImage m dst 32) (sep : base.toNat + 112 ≤ dst.toNat)
    (saved : memLoad m (base + 88) 64 = bx)
    (r14Saved : memLoad m (base + 96) 64 = saved14)
    (tagLow : returnTag.toNat < 2^32)
    (ret : memLoad m (base + 104) 64 = returnTag)
    (words : WordsAt m (base + 48) 64 w) :
    ∃ o, program.Exec (dialect Extracted.programImage) ⟨⟨.l120398, a, m⟩, []⟩ o ∧
      o.tag = some ⟨64, returnTag⟩ ∧ o.values[4] = ⟨64, base + 112⟩ ∧
      o.values[3] = ⟨64, bx⟩ ∧ o.values[22] = ⟨1, 0⟩ ∧
      Kept a o.values ∧ ParseSignature.ArgumentWidths o.values ∧ o.values[14] = ⟨64,saved14⟩ ∧
      RamWriteFrame m o.store [⟨(base - 8).toNat, 8⟩, ⟨dst.toNat, 32⟩] ∧
      WordsAt o.store dst 64 (Sec1.Serialize.packWords w) := by
  have slot : Writable Extracted.programImage m (base - 8) 8 :=
    win.of_offsets (addr_sub base 8) (addr_sub base 121) (by decide)
  have ok : StoreOk Extracted.programImage m (base - 8) 8 0x12039e 5 :=
    ParseSignature.storeOk_of_codeRange (off := 6) slot
      (fun x hx => Common.fnCode_subset_programImage x (code_l120398 x hx)) (by decide)
  let pushed := memStore m (base - 8) (0x1203a3 : Word)
  have h4 : a[4].get 64 = base := by rw [rsp]; rfl
  have h3 : a[3].get 64 = dst := by rw [rbx]; rfl
  have h14 : a[14].get 64 = base + 48 := by rw [r14]; rfl
  have call : ∃ b, program.runBlock (dialect Extracted.programImage) ⟨.l120398, a, m⟩ =
      .call ⟨.l1148d0, b, pushed⟩ (Ecdh.Output.fieldReturn .l1203a3 0x1203a3) ∧
      b[4] = ⟨64, base - 8⟩ ∧ b[6] = ⟨64, base + 48⟩ ∧ b[7] = ⟨64, dst⟩ ∧ b[22] = ⟨1, 0⟩ ∧
      b[12] = a[12] ∧ b[13] = a[13] ∧ Kept a b := by
    refine ⟨?_, ?run, ?_⟩
    case run =>
      cfg_eval [h4, h3, h14, ok]
      rfl
    refine ⟨rfl, rfl, rfl, df, rfl, rfl, ?_⟩
    rintro ⟨i, hi⟩ hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  obtain ⟨b, call, b4, b6, b7, b22, b12, b13, bk⟩ := call
  have rsrc : Readable m (base + 48) 40 := win.readable.of_offsets rfl (addr_sub base 121) (by decide)
  have input : WordsAt pushed (base + 48) 64 w :=
    words.write_apart _ _ (RangeApart.of_offsets (addr_sub base 8) rfl (by decide))
  obtain ⟨lower, off, offset⟩ := Sec1.Serialize.Coordinates.stackOffsets win.readable.low
  obtain ⟨o, ex, tag, pop, _, keep, frame, result⟩ := Sec1.Serialize.packExecution
    (fun x hx => Common.fnCode_subset_programImage x (Sec1.LIR.code_l1148d0 x hx))
    b4 b6 b7 (rsrc.memStore _ _) (dest.memStore _ _) input (slot.readable.memStore _ _)
    (show memLoad pushed (base - 8) 64 = 0x1203a3 from memLoad_memStore_same _ _ _ (by decide) (by decide))
    (by decide) (Or.inl (by omega))
  have run := Ecdh.Transfer.sec1Exec (dst := .l1148d0) (by decide) rfl ex
  have sp' : o.values[4] = ⟨64, base⟩ := by simpa only [BitVec.sub_add_cancel] using pop
  have hsp : o.values[4].get 64 = base := by rw [sp']; rfl
  have df' : o.values[22] = ⟨1, 0⟩ := (keep 22 (by decide)).trans b22
  have pushedFrame : RamWriteFrame m pushed [⟨(base - 8).toNat, 8⟩, ⟨dst.toNat, 32⟩] := by
    apply (RamWriteFrame.refl _ _).memStore
    refine ⟨_, List.mem_cons_self .., Nat.le_refl _, Nat.le_refl _, ?_⟩
    have h := slot.readable.low
    change (base - 8).toNat + 8 ≤ 2^64
    omega
  have frame' := pushedFrame.trans frame (by
    intro r hr; obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Nat.le_refl _, Nat.le_refl _⟩)
  have low := win.readable.low
  have outside (i : Nat) (h : i ≤ 104) :
      Outside [⟨(base - 8).toNat, 8⟩, ⟨dst.toNat, 32⟩] (base + BitVec.ofNat 64 i) 8 := by
    have addr := offset i (by omega)
    have := dest.readable.low
    refine ⟨by omega, ?_⟩
    intro r hr; rcases List.mem_cons.mp hr with rfl | ht
    · right; change (base - 8).toNat + 8 ≤ _; omega
    · obtain rfl := List.mem_singleton.mp ht
      left; change _ + 8 ≤ dst.toNat; omega
  have saved' : memLoad o.store (base + 88) 64 = bx :=
    (frame'.memLoad_eq (outside 88 (by decide))).trans saved
  have ret' : memLoad o.store (base + 104) 64 = returnTag :=
    (frame'.memLoad_eq (outside 104 (by decide))).trans ret
  have load (i : Nat) (hi : i ≤ 104) : LoadOk o.store (base + BitVec.ofNat 64 i) 8 := by
    apply LoadOk.of_region (win.readable.of_frame frame')
    all_goals have := offset i (by omega); omega
  have l88 : LoadOk o.store (base + 88) 8 := load 88 (by decide)
  have l96 : LoadOk o.store (base + 96) 8 := load 96 (by decide)
  have l104 : LoadOk o.store (base + 104) 8 := load 104 (by decide)
  have add88 : (addSpec base (88 : Word)).1 = base + 88 := rfl
  have widths := packingWidths (a := b) (m := pushed) (by rw [b7]) ex
  have saved14' := (frame'.memLoad_eq (outside 96 (by decide))).trans r14Saved
  have tail : ∃ u, program.runBlock (dialect Extracted.programImage) ⟨.l1203a3, o.values, o.store⟩ =
      .returned u ∧ u.tag = some ⟨64, returnTag⟩ ∧ u.values[4] = ⟨64, base + 112⟩ ∧
      u.values[3] = ⟨64, bx⟩ ∧ u.values[22] = ⟨1, 0⟩ ∧ Kept a u.values ∧
      ParseSignature.ArgumentWidths u.values ∧ u.values[14] = ⟨64,saved14⟩ ∧ u.store = o.store := by
    refine ⟨?_, ?run, ?_⟩
    case run =>
      cfg_eval [hsp, add88, BitVec.add_assoc, l88, l96, l104, ret', saved', saved14', tagLow]
      rfl
    refine ⟨rfl, rfl, rfl, df', ?keepTail, ?widthTail, rfl, rfl⟩
    case widthTail =>
      intro ⟨i, hi⟩ hm
      simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
      · exact widths 7 (by decide)
      · exact widths 6 (by decide)
      · exact widths 2 (by decide)
      · exact widths 1 (by decide)
      · exact widths 8 (by decide)
      · exact widths 9 (by decide)
    rintro ⟨i, hi⟩ hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (keep 5 (by decide)).trans (bk 5 (by decide))
    · exact (keep 12 (by decide)).trans (bk 12 (by decide))
    · exact (keep 13 (by decide)).trans (bk 13 (by decide))
    · exact (keep 15 (by decide)).trans (bk 15 (by decide))
    · exact (keep 39 (by decide)).trans (bk 39 (by decide))
    · exact (keep 50 (by decide)).trans (bk 50 (by decide))
    · exact (keep 51 (by decide)).trans (bk 51 (by decide))
  obtain ⟨u, tail, ut, us, ub, ud, uk, widths, u14, um⟩ := tail
  refine ⟨u, ParseSignature.exec_call call run (by rw [tag]; rfl) (.done ?_), ut, us, ub, ud, uk, widths, u14, um ▸ frame', um ▸ result⟩
  change program.step _ ⟨⟨.l1203a3, o.values, o.store⟩, []⟩ = .done u
  simp only [Program.step, tail, CFG.Transfer.next]

theorem serializeWords {a : Values Value Reg.count} {m : Ram} {base dst src saved14 returnTag : Word} {w : Limbs}
    (rsp : a[4].get 64 = base + 104) (rsi : a[6].get 64 = src) (rdi : a[7].get 64 = dst)
    (bp : a[5].width = 64) (r12 : a[12].width = 64) (r13 : a[13].width = 64)
    (r15 : a[15].width = 64) (df : a[22] = ⟨1, 0⟩) (r14 : a[14].get 64 = saved14)
    (win : Writable Extracted.programImage m (base - 121) 433) (source : Readable m src 40)
    (dest : Writable Extracted.programImage m dst 32) (sep : base.toNat + 112 ≤ src.toNat)
    (apart : base.toNat + 112 ≤ dst.toNat) (align : base.toNat % 16 = 0)
    (tagLow : returnTag.toNat < 2^32)
    (ret : memLoad m (base + 104) 64 = returnTag) (words : WordsAt m src 64 w) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l120350, a, m⟩, []⟩ out ∧
      out.tag = some ⟨64, returnTag⟩ ∧ out.values[4] = ⟨64, base + 112⟩ ∧
      out.values[3] = ⟨64, a[3].get 64⟩ ∧ out.values[22] = ⟨1, 0⟩ ∧ Kept a out.values ∧
      ParseSignature.ArgumentWidths out.values ∧ out.values[14] = ⟨64,saved14⟩ ∧
      RamWriteFrame m out.store [⟨(base - 121).toNat, 233⟩, ⟨dst.toNat, 32⟩] ∧
      WordsAt out.store dst 64 (Sec1.Serialize.packWords (Sec1.Serialize.Normalize.normalize w)) := by
  obtain ⟨b, n, setup, b4, b6, b7, b3, b14, b22, f1, bx, slot, input⟩ :=
    Ecdh.Output.normalizeSetup rsp rsi rdi win source sep words
  have keep1 := setupKept setup
  have saved14Setup : memLoad n (base + 96) 64 = saved14 := by
    cfg_eval at setup
    repeat' replace setup := guardedCall setup
    cases setup
    have addr : base + 104 - 8 = base + 96 := by bv_omega
    rw [← r14]
    simp (disch := store_disch) only [memLoad_memStore_same, memLoad_memStore_of_rangeApart,
      rsp, addr]
  obtain ⟨c, cr, ct, c4, c3, c14, c22, keep2, _, _, f2, normalized⟩ :=
    normalize b4 b6 b7 b3 b14 (b22.trans df) ((congrArg Value.width (keep1 5 (by decide))).trans bp)
      ((congrArg Value.width (keep1 12 (by decide))).trans r12)
      ((congrArg Value.width (keep1 13 (by decide))).trans r13)
      ((congrArg Value.width (keep1 15 (by decide))).trans r15) (win.of_frame f1) align slot input
  obtain ⟨lo, sp, off⟩ := Sec1.Serialize.Coordinates.stackOffsets win.readable.low
  have at88 : (base + 88).toNat = base.toNat + 88 := off 88 (by decide)
  have at104 : (base + 104).toNat = base.toNat + 104 := off 104 (by decide)
  have at48 : (base + 48).toNat = base.toNat + 48 := off 48 (by decide)
  have rd := win.readable.low
  have ret1 : memLoad n (base + 104) 64 = returnTag := by
    rw [f1.memLoad_eq, ret]
    refine ⟨by change _ + 8 ≤ 2^64; omega, fun reg hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    right; change (base - 8).toNat + 112 ≤ _; omega
  have restore (i : Nat) (hi : 88 ≤ i) (hj : i ≤ 104) :
      memLoad c.store (base + BitVec.ofNat 64 i) 64 = memLoad n (base + BitVec.ofNat 64 i) 64 := by
    have offi := off i (by omega)
    apply f2.memLoad_eq
    refine ⟨by change _ + 8 ≤ 2^64; omega, ?_⟩
    intro reg hr
    rcases List.mem_cons.mp hr with rfl | ht
    · right; change (base - 121).toNat + 113 ≤ _; omega
    · obtain rfl := List.mem_singleton.mp ht
      right; change (base + 48).toNat + 40 ≤ _; omega
  obtain ⟨o, pr, tag, o4, o3, o22, k3, widths, o14, f3, packed⟩ := packReturn c4 c3 c14 c22
    ((win.of_frame f1).of_frame f2) ((dest.of_frame f1).of_frame f2) apart
    ((restore 88 (by decide) (by decide)).trans bx)
    ((restore 96 (by decide) (by decide)).trans saved14Setup) tagLow
    ((restore 104 (by decide) (by decide)).trans ret1) normalized
  let ws : List MemoryRegion := [⟨(base - 121).toNat, 233⟩, ⟨dst.toNat, 32⟩]
  have within {x : Word} {len : Nat} (l : (base - 121).toNat ≤ x.toNat)
      (u : x.toNat + len ≤ (base - 121).toNat + 233) :
      ∃ g ∈ ws, g.start ≤ x.toNat ∧ x.toNat + len ≤ g.start + g.size :=
    ⟨_, .head _, l, u⟩
  have wf := (RamWriteFrame.refl m ws).trans f1 (by
    intro reg hr
    obtain rfl := List.mem_singleton.mp hr
    exact within (x := base - 8) (len := 112) (by omega) (by omega))
  have wf := wf.trans f2 (by
    intro reg hr
    rcases List.mem_cons.mp hr with rfl | ht
    · exact within (x := base - 121) (len := 113) (by omega) (by omega)
    · obtain rfl := List.mem_singleton.mp ht
      exact within (x := base + 48) (len := 40) (by omega) (by omega))
  have wf := wf.trans f3 (by
    intro reg hr
    rcases List.mem_cons.mp hr with rfl | ht
    · exact within (x := base - 8) (len := 8) (by omega) (by omega)
    · obtain rfl := List.mem_singleton.mp ht
      exact ⟨_, .tail _ (.head _), Nat.le_refl _, Nat.le_refl _⟩)
  exact ⟨o, ParseSignature.exec_call setup cr (by rw [ct]; rfl) pr, tag, o4, o3, o22,
    fun i hi => (k3 i hi).trans ((keep2 i hi).trans (keep1 i hi)), widths, o14, wf, packed⟩

theorem serializeX {a : Values Value Reg.count} {m : Ram} {base dst src saved14 returnTag : Word} {point : Curve.Point}
    (rsp : a[4].get 64 = base + 104) (rsi : a[6].get 64 = src) (rdi : a[7].get 64 = dst)
    (bp : a[5].width = 64) (r12 : a[12].width = 64) (r13 : a[13].width = 64)
    (r15 : a[15].width = 64) (df : a[22] = ⟨1, 0⟩) (r14 : a[14].get 64 = saved14)
    (win : Writable Extracted.programImage m (base - 121) 433) (source : Readable m src 40)
    (dest : Writable Extracted.programImage m dst 32) (sep : base.toNat + 112 ≤ src.toNat)
    (apart : base.toNat + 112 ≤ dst.toNat) (align : base.toNat % 16 = 0)
    (tagLow : returnTag.toNat < 2^32)
    (ret : memLoad m (base + 104) 64 = returnTag) (x : Ecdh.Affine.XAt m src point) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l120350, a, m⟩, []⟩ out ∧
      out.tag = some ⟨64, returnTag⟩ ∧ out.values[4] = ⟨64, base + 112⟩ ∧
      out.values[3] = ⟨64, a[3].get 64⟩ ∧ out.values[22] = ⟨1, 0⟩ ∧ Kept a out.values ∧
      ParseSignature.ArgumentWidths out.values ∧ out.values[14] = ⟨64,saved14⟩ ∧
      RamWriteFrame m out.store [⟨(base - 121).toNat, 233⟩, ⟨dst.toNat, 32⟩] ∧
      (⟨dst.toNat, 32⟩ : MemoryRegion).HasBytes out.store (Ecdh.Output.xBytes point) := by
  obtain ⟨v,w,words,repr,val⟩ := x
  obtain ⟨o,run,tag,o4,o3,o22,keep,widths,o14,writes,packed⟩ :=
    serializeWords rsp rsi rdi bp r12 r13 r15 df r14 win source dest sep apart align tagLow ret words
  obtain ⟨width,value⟩ := Sec1.Serialize.Normalize.normalize_correct w v 8 repr (by decide)
  have bytes := Sec1.Serialize.packWords_hasBytes width packed (dest.of_frame writes).readable
  rw [value,val] at bytes
  exact ⟨o,run,tag,o4,o3,o22,keep,widths,o14,writes,bytes⟩

private def target : Ecdh.LIR.Label → Option Verify.LIR.Label
  | .l120350 => some .l120350
  | .l120398 => some .l120398
  | .l1203a3 => some .l1203a3
  | .l114930 => some .l114930
  | .l114a10 => some .l114a10
  | .l1148d0 => some .l1148d0
  | .l127d50 => some .l127d50
  | _ => none

private theorem blocks (a : Ecdh.LIR.Label) (b : Verify.LIR.Label) (h : target a = some b) :
    Generate.Serialize.Relabel.block target (Ecdh.LIR.program.blocks a) =
      Generate.Serialize.Relabel.block some (Verify.LIR.program.blocks b) := by
  unfold target at h
  split at h <;> cases h <;> rfl

theorem transfer {a : Values Value Reg.count} {m : Ram} {out : Output Value Ram Reg.count}
    (run : Ecdh.LIR.program.Exec (dialect Extracted.programImage) ⟨⟨.l120350,a,m⟩,[]⟩ out) :
    Verify.LIR.program.Exec (dialect Extracted.programImage) ⟨⟨.l120350,a,m⟩,[]⟩ out :=
  Generate.Serialize.Relabel.exec blocks run rfl

end K256.Proofs.Signing.Composition.Attempt.Serializer
