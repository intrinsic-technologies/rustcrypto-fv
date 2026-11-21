import K256.Proofs.Verify.Core.Memory
import K256.Proofs.Verify.LIR.Generated.Values
import K256.Proofs.Ecdh.Output.Serialize

namespace K256.Proofs.Verify.Core.Serializer

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  Ecdh.LIR Common.Field Standards.SECG.ECC

private def Kept (a b : Values Value Reg.count) : Prop :=
  ∀ i : Fin Reg.count, i.val ∈ [5, 15, 39, 50, 51] → b[i] = a[i]

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
  rcases hm with rfl | rfl | rfl | rfl | rfl <;> rfl

private def canonicalArgs (a : Values Value Reg.count) : Values Value Reg.count :=
  Vector.ofFn fun i =>
    if i.val ∈ [12, 13] then ⟨64, a[i].get 64⟩ else a[i]

private theorem canonicalNat (a : Values Value Reg.count) (i : Nat) (hi : i < Reg.count) :
    (canonicalArgs a)[i] = if i ∈ [12, 13] then ⟨64, a[i].get 64⟩ else a[i] :=
  Vector.getElem_ofFn ..

private theorem normalizeBlock (a : Values Value Reg.count) (m : Ram) :
    program.runBlock (dialect Extracted.programImage) ⟨.l114930, a, m⟩ =
    program.runBlock (dialect Extracted.programImage) ⟨.l114930, canonicalArgs a, m⟩ := by
  cfg_eval
  simp (config := { decide := true }) only [canonicalNat, ↓reduceIte, Value.get_mk]

set_option maxHeartbeats 800000 in
private theorem normalize {a : Values Value Reg.count} {m : Ram} {base dst : Word} {w : Limbs}
    (rsp : a[4] = ⟨64, base - 8⟩) (rsi : a[6] = ⟨64, base + 8⟩) (rdi : a[7] = ⟨64, base + 48⟩)
    (rbx : a[3] = ⟨64, dst⟩) (r14 : a[14] = ⟨64, base + 48⟩) (df : a[22] = ⟨1, 0⟩)
    (bp : a[5].width = 64) (r15 : a[15].width = 64)
    (win : Writable Extracted.programImage m (base - 121) 433) (align : base.toNat % 16 = 0)
    (slot : memLoad m (base - 8) 64 = 0x120398) (input : WordsAt m (base + 8) 64 w) :
    ∃ o, program.Exec (dialect Extracted.programImage) ⟨⟨.l114930, a, m⟩, []⟩ o ∧
      o.tag = some ⟨64, 0x120398⟩ ∧ o.values[4] = ⟨64, base⟩ ∧
      o.values[3] = ⟨64, dst⟩ ∧ o.values[14] = ⟨64, base + 48⟩ ∧ o.values[22] = ⟨1, 0⟩ ∧
      Kept a o.values ∧ o.values[12].width = 64 ∧ o.values[13].width = 64 ∧
      RamWriteFrame m o.store [⟨(base - 121).toNat, 113⟩, ⟨(base + 48).toNat, 40⟩] ∧
      WordsAt o.store (base + 48) 64 (Sec1.Serialize.Normalize.normalize w) := by
  have same (i : Nat) (h : i ∉ [12, 13]) (hi : i < Reg.count := by decide) :
      (canonicalArgs a)[i] = a[i] := by rw [canonicalNat, ite_eq_right h]
  have eqWord (v : Value) (width : v.width = 64) : v = ⟨64, v.get 64⟩ := by
    obtain ⟨w, x⟩ := v
    cases width
    rfl
  have saved (i : Fin Reg.count) (h : i.val ∈ [3, 5, 12, 13, 14, 15]) :
      (canonicalArgs a)[i] = ⟨64, (canonicalArgs a)[i].get 64⟩ := by
    change (canonicalArgs a)[i.val] = ⟨64, (canonicalArgs a)[i.val].get 64⟩
    rw [canonicalNat]
    split
    · rw [Value.get_mk]
    · rename_i outside
      have cases : i.val = 3 ∨ i.val = 5 ∨ i.val = 14 ∨ i.val = 15 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h outside
        omega
      rcases cases with e | e | e | e
      · simp only [e, rbx, Value.get_mk]
      · simp only [e]
        exact eqWord _ bp
      · simp only [e, r14, Value.get_mk]
      · simp only [e]
        exact eqWord _ r15
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
    Generate.Generator.Affine.normalizeCall ((same 4 (by decide)).trans rsp)
      ((same 6 (by decide)).trans rsi) ((same 7 (by decide)).trans rdi)
      ((same 22 (by decide)).trans df) saved stack
      (win.readable.of_offsets rfl (addr_sub _ _) (by decide))
      (win.of_offsets rfl (addr_sub _ _) (by decide))
      (by omega) (by omega) (Or.inr (by omega)) (by omega) (by omega) (by omega)
      slot (by decide) input
  have child := Ecdh.Transfer.generateExec (dst := .l114930) (by decide) rfl run
  refine ⟨o, ?_, tag, ?_, (keep 3 (by decide)).trans ((same 3 (by decide)).trans rbx),
    (keep 14 (by decide)).trans ((same 14 (by decide)).trans r14),
    (keep 22 (by decide)).trans ((same 22 (by decide)).trans df), ?pres, ?width12, ?width13, (by simpa only [low] using frame), words⟩
  · have stepEq : program.step (dialect Extracted.programImage) ⟨⟨.l114930, a, m⟩, []⟩ =
        program.step (dialect Extracted.programImage) ⟨⟨.l114930, canonicalArgs a, m⟩, []⟩ :=
      congrArg (fun block => block.next (dialect Extracted.programImage) []) (normalizeBlock a m)
    cases child with
    | done h => exact .done (stepEq.trans h)
    | next h tail => exact .next (stepEq.trans h) tail
  · simpa only [BitVec.sub_add_cancel] using pop
  case pres =>
    rintro ⟨i, hi⟩ hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl
    · exact (keep 5 (by decide)).trans (same 5 (by decide))
    · exact (keep 15 (by decide)).trans (same 15 (by decide))
    · exact (keep 39 (by decide)).trans (same 39 (by decide))
    · exact (keep 50 (by decide)).trans (same 50 (by decide))
    · exact (keep 51 (by decide)).trans (same 51 (by decide))
  case width12 =>
    have width : (canonicalArgs a)[12].width = 64 := by rw [canonicalNat]; rfl
    exact (congrArg Value.width (keep 12 (by decide))).trans width
  case width13 =>
    have width : (canonicalArgs a)[13].width = 64 := by rw [canonicalNat]; rfl
    exact (congrArg Value.width (keep 13 (by decide))).trans width

set_option maxRecDepth 4096 in
private theorem packingR9 {code : CodeMap} {a : Values Value Reg.count} {m : Ram}
    {out : Output Value Ram Reg.count}
    (run : Sec1.LIR.program.Exec (dialect code) ⟨⟨.l1148d0,a,m⟩, []⟩ out) :
    out.values[9].width = 64 := by
  let widthOk : CFG.Transfer Value Ram Sec1.LIR.Label signature Reg.count → Prop
    | .returned o => o.values[9].width = 64
    | .stuck => True
    | _ => False
  have guard (p : Prop) [Decidable p] (t : CFG.Transfer Value Ram Sec1.LIR.Label signature Reg.count)
      (h : widthOk t) : widthOk (if p then t else .stuck) := by
    split <;> first | exact h | trivial
  have checked : widthOk (Sec1.LIR.program.runBlock (dialect code) ⟨.l1148d0,a,m⟩) := by
    cfg_eval [Sec1.LIR.b_l1148d0_1]
    repeat' apply guard
    rfl
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
private theorem packReturn {a : Values Value Reg.count} {m : Ram} {base dst bx : Word} {w : Limbs}
    (rsp : a[4] = ⟨64, base⟩) (rbx : a[3] = ⟨64, dst⟩) (r14 : a[14] = ⟨64, base + 48⟩)
    (df : a[22] = ⟨1, 0⟩) (width12 : a[12].width = 64) (width13 : a[13].width = 64)
    (win : Writable Extracted.programImage m (base - 121) 433)
    (dest : Writable Extracted.programImage m dst 32) (sep : base.toNat + 112 ≤ dst.toNat)
    (saved : memLoad m (base + 88) 64 = bx) (ret : memLoad m (base + 104) 64 = 0x105292)
    (words : WordsAt m (base + 48) 64 w) :
    ∃ o, program.Exec (dialect Extracted.programImage) ⟨⟨.l120398, a, m⟩, []⟩ o ∧
      o.tag = some ⟨64, 0x105292⟩ ∧ o.values[4] = ⟨64, base + 112⟩ ∧
      o.values[3] = ⟨64, bx⟩ ∧ o.values[22] = ⟨1, 0⟩ ∧
      Kept a o.values ∧ o.values[9].width = 64 ∧ o.values[12].width = 64 ∧ o.values[13].width = 64 ∧ o.values[14].width = 64 ∧
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
    rcases hm with rfl | rfl | rfl | rfl | rfl <;> rfl
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
  have ret' : memLoad o.store (base + 104) 64 = 0x105292 :=
    (frame'.memLoad_eq (outside 104 (by decide))).trans ret
  have load (i : Nat) (hi : i ≤ 104) : LoadOk o.store (base + BitVec.ofNat 64 i) 8 := by
    apply LoadOk.of_region (win.readable.of_frame frame')
    all_goals have := offset i (by omega); omega
  have l88 : LoadOk o.store (base + 88) 8 := load 88 (by decide)
  have l96 : LoadOk o.store (base + 96) 8 := load 96 (by decide)
  have l104 : LoadOk o.store (base + 104) 8 := load 104 (by decide)
  have add88 : (addSpec base (88 : Word)).1 = base + 88 := rfl
  have w9 := packingR9 (code := Extracted.programImage) (a := b) (m := pushed) ex
  have w12 := (congrArg Value.width ((keep 12 (by decide)).trans b12)).trans width12
  have w13 := (congrArg Value.width ((keep 13 (by decide)).trans b13)).trans width13
  have tail : ∃ u, program.runBlock (dialect Extracted.programImage) ⟨.l1203a3, o.values, o.store⟩ =
      .returned u ∧ u.tag = some ⟨64, 0x105292⟩ ∧ u.values[4] = ⟨64, base + 112⟩ ∧
      u.values[3] = ⟨64, bx⟩ ∧ u.values[22] = ⟨1, 0⟩ ∧ Kept a u.values ∧
      u.values[9].width = 64 ∧ u.values[12].width = 64 ∧ u.values[13].width = 64 ∧ u.values[14].width = 64 ∧ u.store = o.store := by
    refine ⟨?_, ?run, ?_⟩
    case run =>
      cfg_eval [hsp, add88, BitVec.add_assoc, l88, l96, l104, ret', saved']
      rfl
    refine ⟨rfl, rfl, rfl, df', ?_, w9, w12, w13, rfl, rfl⟩
    rintro ⟨i, hi⟩ hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl
    · exact (keep 5 (by decide)).trans (bk 5 (by decide))
    · exact (keep 15 (by decide)).trans (bk 15 (by decide))
    · exact (keep 39 (by decide)).trans (bk 39 (by decide))
    · exact (keep 50 (by decide)).trans (bk 50 (by decide))
    · exact (keep 51 (by decide)).trans (bk 51 (by decide))
  obtain ⟨u, tail, ut, us, ub, ud, uk, u9, u12, u13, u14, um⟩ := tail
  refine ⟨u, ParseSignature.exec_call call run (by rw [tag]; rfl) (.done ?_), ut, us, ub, ud, uk, u9, u12, u13, u14, um ▸ frame', um ▸ result⟩
  change program.step _ ⟨⟨.l1203a3, o.values, o.store⟩, []⟩ = .done u
  simp only [Program.step, tail, CFG.Transfer.next]

private theorem run {a : Values Value Reg.count} {m : Ram} {base dst src : Word} {point : Curve.Point}
    (rsp : a[4].get 64 = base + 104) (rsi : a[6].get 64 = src) (rdi : a[7].get 64 = dst)
    (bp : a[5].width = 64) (r15 : a[15].width = 64) (df : a[22] = ⟨1, 0⟩)
    (win : Writable Extracted.programImage m (base - 121) 433) (source : Readable m src 40)
    (dest : Writable Extracted.programImage m dst 32) (sep : base.toNat + 112 ≤ src.toNat)
    (apart : base.toNat + 112 ≤ dst.toNat) (align : base.toNat % 16 = 0)
    (ret : memLoad m (base + 104) 64 = 0x105292) (x : Ecdh.Affine.XAt m src point) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l120350, a, m⟩, []⟩ out ∧
      out.tag = some ⟨64, 0x105292⟩ ∧ out.values[4] = ⟨64, base + 112⟩ ∧
      out.values[3] = ⟨64, a[3].get 64⟩ ∧ out.values[22] = ⟨1, 0⟩ ∧ Kept a out.values ∧
      out.values[9].width = 64 ∧ out.values[12].width = 64 ∧ out.values[13].width = 64 ∧ out.values[14].width = 64 ∧
      RamWriteFrame m out.store [⟨(base - 121).toNat, 233⟩, ⟨dst.toNat, 32⟩] ∧
      (⟨dst.toNat, 32⟩ : MemoryRegion).HasBytes out.store (Ecdh.Output.xBytes point) := by
  obtain ⟨v, w, words, repr, val⟩ := x
  obtain ⟨b, n, setup, b4, b6, b7, b3, b14, b22, f1, bx, slot, input⟩ :=
    Ecdh.Output.normalizeSetup rsp rsi rdi win source sep words
  have keep1 := setupKept setup
  obtain ⟨c, cr, ct, c4, c3, c14, c22, keep2, c12, c13, f2, normalized⟩ :=
    normalize b4 b6 b7 b3 b14 (b22.trans df) ((congrArg Value.width (keep1 5 (by decide))).trans bp)
      ((congrArg Value.width (keep1 15 (by decide))).trans r15) (win.of_frame f1) align slot input
  obtain ⟨lo, sp, off⟩ := Sec1.Serialize.Coordinates.stackOffsets win.readable.low
  have at88 : (base + 88).toNat = base.toNat + 88 := off 88 (by decide)
  have at104 : (base + 104).toNat = base.toNat + 104 := off 104 (by decide)
  have at48 : (base + 48).toNat = base.toNat + 48 := off 48 (by decide)
  have rd := win.readable.low
  have ret1 : memLoad n (base + 104) 64 = 0x105292 := by
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
  obtain ⟨o, pr, tag, o4, o3, o22, k3, o9, o12, o13, o14, f3, packed⟩ := packReturn c4 c3 c14 c22 c12 c13
    ((win.of_frame f1).of_frame f2) ((dest.of_frame f1).of_frame f2) apart
    ((restore 88 (by decide) (by decide)).trans bx)
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
  obtain ⟨width, value⟩ := Sec1.Serialize.Normalize.normalize_correct w v 8 repr (by decide)
  have bytes := Sec1.Serialize.packWords_hasBytes width packed (dest.of_frame wf).readable
  rw [value, val] at bytes
  exact ⟨o, ParseSignature.exec_call setup cr (by rw [ct]; rfl) pr, tag, o4, o3, o22,
    fun i hi => (k3 i hi).trans ((keep2 i hi).trans (keep1 i hi)), o9, o12, o13, o14, wf, bytes⟩

private def target : Ecdh.LIR.Label → Option LIR.Label
  | .l120350 => some .l120350
  | .l120398 => some .l120398
  | .l1203a3 => some .l1203a3
  | .l114930 => some .l114930
  | .l114a10 => some .l114a10
  | .l1148d0 => some .l1148d0
  | .l127d50 => some .l127d50
  | _ => none

private theorem blocks (a : Ecdh.LIR.Label) (b : LIR.Label) (h : target a = some b) :
    Generate.Serialize.Relabel.block target (Ecdh.LIR.program.blocks a) =
      Generate.Serialize.Relabel.block some (LIR.program.blocks b) := by
  unfold target at h
  split at h <;> cases h <;> rfl

end K256.Proofs.Verify.Core.Serializer

namespace K256.Proofs.Verify.Core

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Verify.LIR
  Standards.SECG.ECC
open Generate.Generator.Multiply (scalarWords)
open Common.Field (Word)

theorem serializeX {fr : Activation} {a b : Registers} {p point : Curve.Point}
    {digest : ByteArray} {r s : Nat} {m : Ram}
    (e : Entry fr a p digest r s) (h : Phase fr b m)
    (ptr : b[14] = ⟨64, localSp fr + 136⟩)
    (x : Ecdh.Affine.XAt m (localSp fr + 136) point)
    (hr : WordsAt m (localSp fr + 256) 64 (scalarWords r)) :
    ∃ c n, Reaches .l10527f b m .l105292 c n ∧ Phase fr c n ∧
      c[15] = ⟨64, localSp fr + 320⟩ ∧
      c[9].width = 64 ∧ c[12].width = 64 ∧ c[13].width = 64 ∧ c[14].width = 64 ∧
      (⟨(localSp fr + 320).toNat, 32⟩ : MemoryRegion).HasBytes n (Ecdh.Output.xBytes point) ∧
      WordsAt n (localSp fr + 256) 64 (scalarWords r) := by
  let sp := localSp fr
  let base := sp - 112
  let src := sp + 136
  let dst := sp + 320
  let ret : Word := 0x105292
  let pushed := memStore m (sp - 8) ret
  let resume : StackFrame Value Label signature Reg.count := ⟨.l105292, #v[], rfl, some ⟨64, ret⟩⟩
  have room := e.stackRoom
  have limit := e.low
  have bot := e.low_toNat
  have subN (k : Nat) (hk : k ≤ 12456) :
      (fr.rsp - BitVec.ofNat 64 k).toNat = fr.rsp.toNat - k := by
    have k' : (BitVec.ofNat 64 k).toNat = k := Nat.mod_eq_of_lt (by omega)
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, k']; omega), k']
  have spN : sp.toNat = fr.rsp.toNat - 488 := subN 488 (by decide)
  have baseN : base.toNat = fr.rsp.toNat - 600 := by
    rw [show base = fr.rsp - 600 by dsimp only [base, sp, localSp]; bv_omega]
    exact subN 600 (by decide)
  have firstN : (base - 121).toNat = fr.rsp.toNat - 721 := by
    rw [show base - 121 = fr.rsp - 721 by dsimp only [base, sp, localSp]; bv_omega]
    exact subN 721 (by decide)
  have slotN : (sp - 8).toNat = fr.rsp.toNat - 496 := by
    rw [show sp - 8 = fr.rsp - 496 by dsimp only [sp, localSp]; bv_omega]
    exact subN 496 (by decide)
  have addN (k : Nat) (hk : k ≤ 488) : (sp + BitVec.ofNat 64 k).toNat = sp.toNat + k := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt (by omega)]
  have dstN : dst.toNat = sp.toNat + 320 := addN 320 (by decide)
  have srcN : src.toNat = sp.toNat + 136 := addN 136 (by decide)
  have rN : (localSp fr + 256).toNat = sp.toNat + 256 := addN 256 (by decide)
  have stack := e.stack.of_frame h.frame
  have window : Writable Extracted.programImage m (base - 121) 433 := stack.sub (by omega) (by omega)
  have output : Writable Extracted.programImage m dst 32 := stack.sub (by omega) (by omega)
  have read : Readable m src 40 := stack.readable.sub (by omega) (by omega)
  have slot : Writable Extracted.programImage m (sp - 8) 8 := stack.sub (by omega) (by omega)
  have push : StoreOk Extracted.programImage m (sp - 8) 8 0x10528d 5 :=
    ParseSignature.storeOk_of_codeRange (off := 14) slot
      (fun x hx => Common.fnCode_subset_programImage x (code_l10527f x hx)) (by decide)
  have spReg : b[4].get 64 = sp := congrArg (Value.get 64) h.sp
  have srcReg : b[14].get 64 = src := congrArg (Value.get 64) ptr
  have called : ∃ d, program.runBlock (dialect Extracted.programImage) ⟨.l10527f, b, m⟩ =
      .call ⟨.l120350, d, pushed⟩ resume ∧ d[4] = ⟨64, sp - 8⟩ ∧ d[6] = ⟨64, src⟩ ∧ d[7] = ⟨64, dst⟩ ∧
      d[3] = ⟨64, fr.rdi⟩ ∧ d[5] = ⟨64, fr.rbp⟩ ∧ d[15] = ⟨64, dst⟩ ∧
      d[22] = ⟨1, 0⟩ ∧ d[39] = ⟨32, fr.mxcsr⟩ ∧ d[50] = ⟨16, fr.ftw⟩ ∧ d[51] = ⟨16, fr.fcw⟩ := by
    refine ⟨?_, ?run, ?_⟩
    case run =>
      cfg_eval [spReg, srcReg, push]
      rfl
    exact ⟨rfl, rfl, rfl, h.dst, h.rbp, rfl, h.df, h.mxcsr, h.ftw, h.fcw⟩
  obtain ⟨d, call, d4, d6, d7, d3, d5, d15, d22, d39, d50, d51⟩ := called
  have x' : Ecdh.Affine.XAt pushed src point := by
    obtain ⟨v, w, words, repr, val⟩ := x
    refine ⟨v, w, words.write_apart _ _ ?_, repr, val⟩
    exact RangeApart.of_offsets (addr_sub sp 8) (show src = sp + 136 from rfl) (by decide)
  have retAt : memLoad pushed (base + 104) 64 = ret := by
    rw [show base + 104 = sp - 8 by dsimp only [base]; bv_omega]
    exact memLoad_memStore_same _ _ _ (by decide) (by decide)
  have aligned : fr.rsp.toNat % 16 = 8 := by
    have ent := e.atoms
    simp only [Fn104f20.frameAt, Fn104f20.frameAtG6, Atom.All, Atom.Holds] at ent
    exact ent.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨out, run, tag, o4, o3, o22, keep, o9, o12, o13, o14, wf, bytes⟩ := Serializer.run (m := pushed) (base := base)
    (by rw [d4]; change sp - 8 = base + 104; dsimp only [base]; bv_omega)
    (by rw [d6]; rfl) (by rw [d7]; rfl) (congrArg Value.width d5) (congrArg Value.width d15)
    d22 (window.memStore _ _) (read.memStore _ _) (output.memStore _ _) (by omega) (by omega)
    (by omega) retAt x'
  have exec : program.Exec (dialect Extracted.programImage) ⟨⟨.l120350, d, pushed⟩, []⟩ out :=
    Generate.Serialize.Relabel.exec Serializer.blocks run rfl
  have pop : base + 112 = sp := BitVec.sub_add_cancel _ _
  let ws : List MemoryRegion := [⟨(base - 121).toNat, 233⟩, ⟨dst.toNat, 32⟩]
  have f0 : RamWriteFrame m pushed ws := (RamWriteFrame.refl m ws).memStore _
    ⟨_, .head _, by change (base - 121).toNat ≤ (sp - 8).toNat; omega,
      by change (sp - 8).toNat + 8 ≤ (base - 121).toNat + 233; omega,
      by change (sp - 8).toNat + 8 ≤ 2^64; omega⟩
  have result := f0.trans wf (fun g hg => ⟨g, hg, Nat.le_refl _, Nat.le_refl _⟩)
  have total := h.frame.trans result (by
    intro g hg
    refine ⟨_, .head _, ?_⟩
    rcases List.mem_cons.mp hg with rfl | hn
    · change fr.low.toNat ≤ (base - 121).toNat ∧ (base - 121).toNat + 233 ≤
        fr.low.toNat + (fr.rsp.toNat - fr.low.toNat)
      omega
    · obtain rfl := List.mem_singleton.mp hn
      change fr.low.toNat ≤ dst.toNat ∧ dst.toNat + 32 ≤ fr.low.toNat+(fr.rsp.toNat - fr.low.toNat)
      omega)
  have outside {addr : Word} {len : Nat} (hi : addr.toNat+len ≤ 2^64)
      (above : sp.toNat ≤ addr.toNat) (away : addr.toNat+len ≤ dst.toNat ∨ dst.toNat + 32 ≤ addr.toNat) :
      Outside ws addr len := by
    refine ⟨hi, fun g hg => ?_⟩
    rcases List.mem_cons.mp hg with rfl | hn
    · right; change (base - 121).toNat + 233 ≤ _; omega
    · obtain rfl := List.mem_singleton.mp hn
      exact away
  have word (k : Nat) (bound : k ≤ 40) :
      memLoad out.store (fr.rsp-BitVec.ofNat 64 k) 64 = memLoad m (fr.rsp-BitVec.ofNat 64 k) 64 := by
    have := subN k (by omega)
    apply result.memLoad_eq
    exact outside (by change _ + 8 ≤ 2^64; omega) (by omega) (Or.inr (by omega))
  have back := ParseSignature.exec_reaches_resume exec resume [] (by rw [tag]; rfl)
  refine ⟨out.values, out.store, .step (congrArg (CFG.Transfer.next _ []) call) back,
    ⟨⟨by simpa only [pop] using o4, by simpa only [d3, Value.get_mk] using o3,
      (keep 5 (by decide)).trans d5, o22, (keep 39 (by decide)).trans d39,
      (keep 50 (by decide)).trans d50, (keep 51 (by decide)).trans d51,
      (word 40 (by decide)).trans h.rbx, (word 32 (by decide)).trans h.r12,
      (word 24 (by decide)).trans h.r13, (word 16 (by decide)).trans h.r14,
      (word 8 (by decide)).trans h.r15⟩, total⟩, (keep 15 (by decide)).trans d15, o9, o12, o13, o14, bytes,
    hr.of_frame result (by decide) ?_⟩
  exact outside (by change _ + 32 ≤ 2^64; omega) (by omega)
    (Or.inl (by change _ + 32 ≤ dst.toNat; omega))

end K256.Proofs.Verify.Core
