import K256.Proofs.Sec1.Sqrt.CopySites
import K256.Proofs.Sec1.Sqrt.SquareSegment
import K256.Proofs.Sec1.Sqrt.Loop
import K256.Proofs.Common.Refine.Lemma.Store

set_option autoImplicit false

namespace K256.Proofs.Sec1.Sqrt

open X86 X86.Machine X86.UserProcess X86Proofs Prelude K256.Spec.Program
open CFG Lift Refine Common.Field

abbrev roundCode : CodeMap := Extracted.programSections.toCodeMap

def roundStack (base : BitVec 64) : MemoryRegion :=
  ⟨(base - 112).toNat, 192⟩

structure RoundState [Bindings] (c : SquareCallSite) (base : BitVec 64)
    (words : Limbs) (s : RamState) : Prop where
  entry : EntryReady roundCode s
  rsp : stackPtr s = base
  workspace : Writable roundCode s.external (base - 112) 192
  inputReg : (Operand.reg c.regs.inReg : Operand 64).read s = base
  outputReg : (Operand.reg c.regs.outReg : Operand 64).read s = base + 40
  df : RFLAGS.DirectionFlagClear s.RFLAGS
  input : WordsAt s.external base 64 words

private theorem squareCode_subset : ∀ x ∈ LIR.fnCode, x ∈ roundCode := by
  intro x hx
  apply List.mem_flatMap.mpr
  refine ⟨LIR.textSection, by simp [Extracted.programSections, LIR.textSection], ?_⟩
  simpa only [LIR.fnCode, LIR.sections, ImageSections.toCodeMap, List.flatMap_cons,
    List.flatMap_nil, List.append_nil] using hx

private theorem squareSite_bounds {c : SquareCallSite} (hc : c ∈ squareCallSites) :
    0x100000 ≤ c.pc.toNat ∧ c.pc.toNat + 60 ≤ 0x12aa00 := by
  have h : squareCallSites.all (fun c => decide (0x100000 ≤ c.pc.toNat ∧
      c.pc.toNat + 60 ≤ 0x12aa00)) = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h c hc)

private theorem squareSite_returnCode {c : SquareCallSite} (hc : c ∈ squareCallSites) :
    CodeAt roundCode (c.pc + 11) := by
  have h : squareCallSites.all (fun c => decide (c.offset + 11 < Extracted.textBytes.size)) =
      true := by decide +kernel
  have hi : c.offset + 11 < Extracted.textBytes.toList.length := by
    rw [chunked_toList_length]
    exact of_decide_eq_true (List.all_eq_true.mp h c hc)
  have hp : Extracted.textAddress + BitVec.ofNat 64 (c.offset + 11) = c.pc + 11 := by
    rw [BitVec.ofNat_add, ← BitVec.add_assoc]
    rfl
  refine ⟨Extracted.textBytes.toList[c.offset + 11], List.mem_flatMap.mpr
      ⟨LIR.textSection, by simp [Extracted.programSections, LIR.textSection], ?_⟩⟩
  change _ ∈ codeRange Extracted.textAddress Extracted.textBytes.toList
  rw [← hp]
  exact mem_codeRange _ _ _ hi

private theorem roundAdd_toNat {base : BitVec 64} {n : Nat}
    (h : base.toNat + n < 2^64) :
    (base + BitVec.ofNat 64 n).toNat = base.toNat + n := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := n) (by omega),
    Nat.mod_eq_of_lt h]

private theorem preservedReg {s t : RamState} {cs : List Component}
    (h : AgreesExcept cs s t) {r : Nat} (hr : Component.reg (BitVec.ofNat 5 r) ∉ cs) :
    (Operand.reg (BitVec.ofNat 5 r) : Operand 64).read t =
    (Operand.reg (BitVec.ofNat 5 r) : Operand 64).read s := h.read hr

private theorem saved_square {u v : RamState} {slot : BitVec 64}
    (hp : LIR.Fn1145f0.Post (Activation.ofEntry u 104 slot)
      (Square.core.footprint () (Activation.ofEntry u 104 slot)) v)
    (r : Nat) (hr : r ∈ Activation.calleeSavedNumbers) :
    (Operand.reg (BitVec.ofNat 5 r) : Operand 64).read v =
    (Operand.reg (BitVec.ofNat 5 r) : Operand 64).read u := by
  have hsmall : r < Reg.count := by
    simp only [Activation.calleeSavedNumbers, List.mem_cons, List.not_mem_nil, or_false] at hr
    have hcount : 15 < Reg.count := by decide
    omega
  have hmem : (⟨r, hsmall⟩ : Fin Reg.count) ∈ LIR.Fn1145f0.frameInfo.preserved := by
    simp only [LIR.Fn1145f0.frameInfo, Activation.calleeSavedNumbers,
      List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +revert
  have hv := hp.preserved ⟨r, hsmall⟩ hmem
  have hu := Activation.ofEntry_regs (s := u) (stackBytes := 104) (ret := slot) r
    (Activation.calleeSavedNumbers_sub r hr)
  have he := congrArg (fun w : Value => w.get 64) (hv.trans hu.symm)
  simp only [Activation.calleeSavedNumbers, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact he

private theorem roundFrame_store {s t : RamState} {cs : List Component} {addr : BitVec 64}
    {region : MemoryRegion} {len : Nat} (hf : AgreesExcept cs s t)
    (hstart : region.start ≤ addr.toNat)
    (hend : addr.toNat + len ≤ region.start + region.size)
    (hlow : addr.toNat + len ≤ 2^64)
    (hc : ∀ x c, c ∈ cs → c.Covers x → Component.Covers (.mem addr len) x) :
    RamWriteFrame s.external t.external [region] := by
  refine ⟨?_, hf.grow⟩
  intro x hx
  apply hf.byte
  intro c hmem hcov
  obtain ⟨i, hi, he⟩ := hc x c hmem hcov
  have hxn : x.toNat = addr.toNat + i := by
    rw [he, roundAdd_toNat (by omega)]
  have hap := hx.2 region List.mem_cons_self
  omega

private theorem roundSquareWithin {base : BitVec 64} {u : RamState} {slot : BitVec 64}
    (hu : stackPtr u = base - 8) (hroom : 112 ≤ base.toNat)
    (hbound : base.toNat + 80 ≤ 2^32)
    (hdi : u.regValue .rdi = base + 40) :
    RegionsWithin ((Activation.ofEntry u 104 slot).region ::
      Square.core.footprint () (Activation.ofEntry u 104 slot)) [roundStack base] := by
  have hb112 : (base - 112).toNat = base.toNat - 112 :=
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact hroom)
  have hb8 : (base - 8).toNat = base.toNat - 8 :=
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; change 8 ≤ _; omega)
  have hlow := Activation.ofEntry_low_toNat (s := u) (stackBytes := 104) (ret := slot)
  change (Activation.ofEntry u 104 slot).low.toNat = (stackPtr u).toNat - 104 at hlow
  rw [hu, hb8] at hlow
  have hdst : (Activation.ofEntry u 104 slot).rdi.toNat = base.toNat + 40 := by
    change (u.regValue .rdi).toNat = _
    rw [hdi]
    exact roundAdd_toNat (n := 40) (by omega)
  intro r hr
  simp only [Square.core, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> refine ⟨roundStack base, List.mem_cons_self, ?_, ?_⟩
  · change (base - 112).toNat ≤ (Activation.ofEntry u 104 slot).low.toNat
    omega
  · change (Activation.ofEntry u 104 slot).low.toNat +
      ((stackPtr u).toNat - (Activation.ofEntry u 104 slot).low.toNat) ≤ (base - 112).toNat + 192
    rw [hu, hb8]
    omega
  · change (base - 112).toNat ≤ (Activation.ofEntry u 104 slot).rdi.toNat
    omega
  · change (Activation.ofEntry u 104 slot).rdi.toNat + 40 ≤ (base - 112).toNat + 192
    omega

theorem SquareCallSite.squareRound [inst : Bindings] {c : SquareCallSite}
    {boundary : ReturnBoundary} {base : BitVec 64} {s : RamState} {words : Limbs}
    (hc : c ∈ squareCallSites) (stride : UnitStringStride inst) (hout : ReturnOutside boundary roundCode)
    (hroom : 112 ≤ base.toNat) (halign : base.toNat % 16 = 0)
    (hap : base.toNat + 80 ≤ 0x100000 ∨ 0x12aa00 ≤ base.toNat - 112)
    (hRsp : base ≠ boundary.rsp) (hPush : base - 8 ≠ boundary.rsp)
    (hrip : s.RIP = c.pc) (hs : RoundState c base words s) :
    ∃ n t, Advances boundary n s t ∧ t.RIP = c.pc + 11#64 ∧
      RoundState c base words t ∧
      WordsAt t.external (base + 40) 64 (squareWords words) ∧
      RamWriteFrame s.external t.external [roundStack base] ∧
      (∀ r ∈ Activation.calleeSavedNumbers,
        (Operand.reg (BitVec.ofNat 5 r) : Operand 64).read t =
        (Operand.reg (BitVec.ofNat 5 r) : Operand 64).read s) := by
  have hb112 : (base - 112).toNat = base.toNat - 112 :=
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact hroom)
  have hb8 : (base - 8).toNat = base.toNat - 8 :=
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; change 8 ≤ _; omega)
  have hbound : base.toNat + 80 ≤ 2^32 := by
    have hh := hs.workspace.readable.low
    rw [hb112] at hh
    omega
  have hb40 : (base + 40).toNat = base.toNat + 40 :=
    roundAdd_toNat (n := 40) (by omega)
  have hpush : pushAddr s = base - 8 := congrArg (· - 8) hs.rsp
  have hpushW : Writable roundCode s.external (pushAddr s) 8 := by
    apply hs.workspace.sub <;> rw [hpush, hb8, hb112] <;> omega
  have hbSite := squareSite_bounds hc
  have hpc6 : (c.pc + 6).toNat = c.pc.toNat + 6 :=
    roundAdd_toNat (n := 6) (by omega)
  have hslotlow : (c.pc + 11).toNat < 2^32 := by
    change (c.pc + BitVec.ofNat 64 11).toNat < _
    rw [roundAdd_toNat (by omega)]
    omega
  have hcallApart : RangeApart (pushAddr s) 8 (c.pc + 6) 5 := by
    apply RangeApart.of_toNat <;> simp only [hpush, hb8, hpc6] <;> omega
  obtain ⟨u, hsu, hru, hipu, hspu, htop, huOut, huIn, hfu⟩ :=
    c.enter hc hs.entry.ready hrip (hs.rsp ▸ hRsp) (hpush ▸ hPush)
      ⟨hpushW.readable.low, hpushW.readable.present, hpushW.tables⟩ hcallApart hs.entry.code
  have hspu' : stackPtr u = base - 8 := hspu.trans hpush
  have hpRegion : RamWriteFrame s.external u.external [⟨(pushAddr s).toNat, 8⟩] := by
    apply roundFrame_store hfu (addr := pushAddr s) (len := 8) (Nat.le_refl _) (Nat.le_refl _)
      (by rw [hpush, hb8]; omega)
    intro x d hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl <;> first | exact fun h => False.elim h | exact fun h => h
  have hCallFrame : RamWriteFrame s.external u.external [roundStack base] :=
    (RamWriteFrame.refl _ _).trans hpRegion (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r
      refine ⟨roundStack base, List.mem_cons_self, ?_, ?_⟩
      · change (base - 112).toNat ≤ (pushAddr s).toNat
        rw [hpush, hb8, hb112]
        omega
      · change (pushAddr s).toNat + 8 ≤ (base - 112).toNat + 192
        rw [hpush, hb8, hb112]
        omega)
  have hCodeU : CodeIn roundCode u := by
    apply hs.entry.code.of_agreesExcept hfu
    intro x hx d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl
    all_goals try (exact fun h => False.elim h)
    rintro ⟨i, hi, he⟩
    exact hpushW.notCode x hx i hi he
  have hdfU := hfu.directionFlagClear (by simp) hs.df
  have hds : u.regValue .rdi = base + 40 := huOut.trans hs.outputReg
  have his : u.regValue .rsi = base := huIn.trans hs.inputReg
  have hsi : u.regValue .rsi = stackPtr u + 8#64 := by
    rw [his, hspu']
    exact (BitVec.sub_add_cancel base 8).symm
  have hdi : u.regValue .rdi = stackPtr u + 48#64 := by
    rw [hds, hspu']
    bv_omega
  have hnSp : (stackPtr u).toNat = base.toNat - 8 := hspu' ▸ hb8
  have hnWin : (stackPtr u - 104).toNat = base.toNat - 112 := by
    rw [hspu', BitVec.sub_sub]
    exact hb112
  have hwu := hs.workspace.of_frame hCallFrame
  have hWin : Writable roundCode u.external (stackPtr u - 104) 104 := by
    apply hwu.sub <;> rw [hnWin, hb112] <;> omega
  have hRetRead : Readable u.external (stackPtr u) 8 := by
    apply hwu.readable.sub <;> rw [hnSp, hb112] <;> omega
  have hInRead : Readable u.external (u.regValue .rsi) 40 := by
    apply hwu.readable.sub <;> rw [his, hb112] <;> omega
  have hOutWrite : Writable roundCode u.external (u.regValue .rdi) 40 := by
    apply hwu.sub <;> rw [hds, hb40, hb112] <;> omega
  have hIn : WordsAt u.external (u.regValue .rsi) 64 words := by
    rw [his]
    intro i hi
    have hn : (wordAddr base 64 i).toNat = base.toNat + 8 * i := by
      change (base + BitVec.ofNat 64 (8 * i)).toNat = _
      exact roundAdd_toNat (by omega)
    rw [hpRegion.memLoad_eq (k := 64)]
    · exact hs.input i hi
    · refine ⟨by rw [hn]; omega, ?_⟩
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r
      apply Or.inr
      change (pushAddr s).toNat + 8 ≤ (wordAddr base 64 i).toNat
      rw [hpush, hb8, hn]
      omega
  let old : Limbs := Vector.ofFn fun i =>
    memLoad u.external (wordAddr (u.regValue .rdi) 64 i.val) 64
  have hOld : WordsAt u.external (u.regValue .rdi) 64 old := by
    intro i hi
    simp only [old, Vector.getElem_ofFn]
  have hEntry := squareEntry u (c.pc + 11) (words, old) hsi hdi hdfU
    hRetRead htop hslotlow hWin
    (by rw [hnSp]; omega) (by rw [hnSp]; omega) (by rw [hnSp]; omega)
    (by rw [hnSp]; omega) hIn hInRead hOld hOutWrite
  have hRet : c.pc + 11 ≠ boundary.rip :=
    ReturnOutside.ne hout (squareSite_returnCode hc)
  obtain ⟨n, v, huv, hv, hvPost, hvInput, hvWords⟩ :=
    squareSegment (words, old) stride squareCode_subset
      ⟨hru, SupportedSSE.of_agreesExcept hfu hs.entry.sse, hCodeU⟩ hipu rfl hout hRet hEntry
  have hvRip : v.RIP = c.pc + 11#64 := hvPost.rip
  have hvSp : stackPtr v = base := by
    have hh := congrArg (fun w : Value => w.get 64) hvPost.rsp
    change stackPtr v = stackPtr u + 8 at hh
    rwa [hspu', BitVec.sub_add_cancel] at hh
  have hvFrame : RamWriteFrame s.external v.external [roundStack base] :=
    hCallFrame.trans hvPost.frame (roundSquareWithin hspu' hroom hbound hds)
  have hvW := hs.workspace.of_frame hvFrame
  have hSaved r (hr : r ∈ Activation.calleeSavedNumbers) :
      (Operand.reg (BitVec.ofNat 5 r) : Operand 64).read v =
      (Operand.reg (BitVec.ofNat 5 r) : Operand 64).read s := by
    have hvs := saved_square hvPost r hr
    have huf := preservedReg hfu (r := r)
    simp only [Activation.calleeSavedNumbers, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hvs.trans (huf (by simp))
  have hInSaved : (Operand.reg c.regs.inReg : Operand 64).read v = base := by
    have h := hs.inputReg
    cases hr : c.regs <;> rw [hr] at h
    · exact (hSaved 14 (by decide)).trans h
    · exact (hSaved 14 (by decide)).trans h
    · exact (hSaved 15 (by decide)).trans h
  have hOutSaved : (Operand.reg c.regs.outReg : Operand 64).read v = base + 40 := by
    have h := hs.outputReg
    cases hr : c.regs <;> rw [hr] at h
    · exact (hSaved 3 (by decide)).trans h
    · exact (hSaved 5 (by decide)).trans h
    · exact (hSaved 14 (by decide)).trans h
  change WordsAt v.external (u.regValue .rsi) 64 words at hvInput
  change WordsAt v.external (u.regValue .rdi) 64 (squareWords words) at hvWords
  rw [his] at hvInput
  rw [hds] at hvWords
  exact ⟨3+n, v, hsu.trans huv, hvRip,
    ⟨hv, hvSp, hvW, hInSaved, hOutSaved, hvPost.df, hvInput⟩, hvWords, hvFrame, hSaved⟩

theorem SquareCallSite.squareCopyRound [inst : Bindings] {c : SquareCallSite}
    {boundary : ReturnBoundary} {base : BitVec 64} {s : RamState} {words : Limbs}
    (hc : c ∈ copySites) (stride : UnitStringStride inst) (hout : ReturnOutside boundary roundCode)
    (hroom : 112 ≤ base.toNat) (halign : base.toNat % 16 = 0)
    (hap : base.toNat + 80 ≤ 0x100000 ∨ 0x12aa00 ≤ base.toNat - 112)
    (hRsp : base ≠ boundary.rsp) (hPush : base - 8 ≠ boundary.rsp)
    (hrip : s.RIP = c.pc) (hs : RoundState c base words s) :
    ∃ n t, Advances boundary n s t ∧ t.RIP = c.pc + 60#64 ∧
      RoundState c base (squareWords words) t ∧
      WordsAt t.external (base + 40) 64 (squareWords words) ∧
      RamWriteFrame s.external t.external [roundStack base] ∧
      (∀ r ∈ Activation.calleeSavedNumbers,
        (Operand.reg (BitVec.ofNat 5 r) : Operand 64).read t =
        (Operand.reg (BitVec.ofNat 5 r) : Operand 64).read s) := by
  obtain ⟨n, v, hsv, hvRip, hv, hvWords, hvFrame, hvSaved⟩ :=
    c.squareRound (copySites_subset hc) stride hout hroom halign hap hRsp hPush hrip hs
  have hvSp := hv.rsp
  have hb112 : (base - 112).toNat = base.toNat - 112 :=
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact hroom)
  have hbound : base.toNat + 80 ≤ 2^32 := by
    have h := hv.workspace.readable.low
    rw [hb112] at h
    omega
  have hb40 : (base + 40).toNat = base.toNat + 40 :=
    roundAdd_toNat (n := 40) (by omega)
  have hvWrite : Writable roundCode v.external (stackPtr v) 40 := by
    apply hv.workspace.sub <;> rw [hvSp, hb112] <;> omega
  have hvRead : Readable v.external (stackPtr v + 40) 40 := by
    apply hv.workspace.readable.sub <;> rw [hvSp, hb40, hb112] <;> omega
  have hvOutput : WordsAt v.external (stackPtr v + 40) 64 (squareWords words) :=
    hvSp ▸ hvWords
  obtain ⟨t, hvt, hrt, hipt, htp, hct, _, _, hft, htw⟩ :=
    c.copyWords hc hv.entry.ready hvRip (hvSp ▸ hRsp) hv.entry.code hvWrite hvRead hvOutput
  have htSp := htp.trans hvSp
  have htFrame : RamWriteFrame s.external t.external [roundStack base] := by
    apply hvFrame.trans (regions' := [roundStack base]) _ (fun r hr => ⟨r, hr, Nat.le_refl _, Nat.le_refl _⟩)
    apply roundFrame_store hft (addr := stackPtr v) (len := 40)
    · change (base - 112).toNat ≤ _
      rw [hvSp, hb112]
      omega
    · change _ ≤ (base - 112).toNat + 192
      rw [hvSp, hb112]
      omega
    · rw [hvSp]
      omega
    · intro x d hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl <;> first | exact fun h => False.elim h | exact fun h => h
  have hSaved r (hr : r ∈ Activation.calleeSavedNumbers) :
      (Operand.reg (BitVec.ofNat 5 r) : Operand 64).read t =
      (Operand.reg (BitVec.ofNat 5 r) : Operand 64).read s := by
    have hvs := hvSaved r hr
    have htf := preservedReg hft (r := r)
    simp only [Activation.calleeSavedNumbers, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact (htf (by simp)).trans hvs
  have hInSaved : (Operand.reg c.regs.inReg : Operand 64).read t = base :=
    (hft.read (by cases c.regs <;> simp [PointerRegs.inReg])).trans hv.inputReg
  have hOutSaved : (Operand.reg c.regs.outReg : Operand 64).read t = base + 40 :=
    (hft.read (by cases c.regs <;> simp [PointerRegs.outReg])).trans hv.outputReg
  have hWordIn := htw
  rw [htSp] at hWordIn
  have hWordOut : WordsAt t.external (base + 40) 64 (squareWords words) := by
    rw [hvSp] at hft
    intro i hi
    have ha : (wordAddr (base + 40) 64 i).toNat = base.toNat + 40 + 8 * i := by
      change ((base + 40) + BitVec.ofNat 64 (8 * i)).toNat = _
      rw [roundAdd_toNat (by rw [hb40]; omega), hb40]
    have hf' : RamWriteFrame v.external t.external [⟨base.toNat, 40⟩] :=
      roundFrame_store hft (addr := base) (len := 40) (Nat.le_refl _) (Nat.le_refl _) (by omega)
        (by
          intro x d hmem
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
          rcases hmem with rfl | rfl | rfl | rfl <;> first | exact fun h => False.elim h | exact fun h => h)
    rw [hf'.memLoad_eq (k := 64)]
    · exact hvWords i hi
    · refine ⟨by rw [ha]; omega, ?_⟩
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r
      apply Or.inr
      change base.toNat + 40 ≤ (wordAddr (base + 40) 64 i).toNat
      rw [ha]
      omega
  exact ⟨n+10, t, hsv.trans hvt, hipt,
    ⟨⟨hrt, SupportedSSE.of_agreesExcept hft hv.entry.sse, hct⟩, htSp,
      hs.workspace.of_frame htFrame, hInSaved, hOutSaved,
      hft.directionFlagClear (by simp) hv.df, hWordIn⟩, hWordOut, htFrame, hSaved⟩

namespace SquareLoop

theorem copySite_mem (loop : SquareLoop) : loop.site ∈ copySites := by
  cases loop
  · exact first44_copySite
  · exact middle88_copySite
  · exact last44_copySite

private theorem afterDecrement [Bindings] (loop : SquareLoop) {base : BitVec 64}
    {s t : RamState} {words : Limbs} (hs : RoundState loop.site base words s)
    (hf : AgreesExcept [.reg loop.counter, .flags, .rip] s t) :
    RoundState loop.site base words t := by
  have hm := hf.external (by simp [Component.Covers])
  have hsp : stackPtr t = stackPtr s :=
    hf.read (n := 64) (r := 4) (by cases loop <;> simp [counter])
  have hi := hf.read (n := 64) (r := loop.site.regs.inReg)
    (by cases loop <;> simp [counter, site, PointerRegs.inReg])
  have ho := hf.read (n := 64) (r := loop.site.regs.outReg)
    (by cases loop <;> simp [counter, site, PointerRegs.outReg])
  exact ⟨⟨hs.entry.ready.of_agreesExcept hf (hm ▸ hs.entry.ready.memory.tables),
      SupportedSSE.of_agreesExcept hf hs.entry.sse, hs.entry.code.of_external_eq hm⟩,
    hsp.trans hs.rsp, hm ▸ hs.workspace, hi.trans hs.inputReg, ho.trans hs.outputReg,
    hf.directionFlagClear (by simp) hs.df, hm ▸ hs.input⟩

private def squareWithOutput (a : Limbs × Bool) : Limbs × Bool :=
  (squareWords a.1, true)

private theorem iter_withOutput (n : Nat) (words : Limbs) :
    SqrtChain.iter squareWithOutput (n + 1) (words, false) =
      (SqrtChain.iter squareWords (n + 1) words, true) := by
  apply Prod.ext
  · exact SqrtChain.iterate_comm Prod.fst squareWithOutput squareWords (fun _ => rfl) _ _
  · have h := SqrtChain.iterate_comm Prod.snd squareWithOutput (fun _ => true) (fun _ => rfl)
    rw [h]
    change SqrtChain.iter (fun _ => true) n true = true
    induction n with
    | zero => rfl
    | succ n ih => exact ih

theorem iterateWords [inst : Bindings] (loop : SquareLoop) {boundary : ReturnBoundary}
    {base : BitVec 64} {s : RamState} {words : Limbs}
    (stride : UnitStringStride inst) (hout : ReturnOutside boundary roundCode)
    (hroom : 112 ≤ base.toNat) (halign : base.toNat % 16 = 0)
    (hap : base.toNat + 80 ≤ 0x100000 ∨ 0x12aa00 ≤ base.toNat - 112)
    (hRsp : base ≠ boundary.rsp) (hPush : base - 8 ≠ boundary.rsp)
    (n : Nat) (hn : n < 2^64) (hrip : s.RIP = loop.site.pc)
    (hcounter : (Operand.reg loop.counter : Operand 64).read s = BitVec.ofNat 64 (n + 1))
    (hs : RoundState loop.site base words s) :
    ∃ fuel t, Advances boundary fuel s t ∧ t.RIP = loop.site.pc + 65#64 ∧
      (Operand.reg loop.counter : Operand 64).read t = 0 ∧
      RoundState loop.site base (SqrtChain.iter squareWords (n + 1) words) t ∧
      WordsAt t.external (base + 40) 64 (SqrtChain.iter squareWords (n + 1) words) ∧
      RamWriteFrame s.external t.external [roundStack base] ∧
      (∀ r ∈ Activation.calleeSavedNumbers, BitVec.ofNat 5 r ≠ loop.counter →
        (Operand.reg (BitVec.ofNat 5 r) : Operand 64).read t =
        (Operand.reg (BitVec.ofNat 5 r) : Operand 64).read s) := by
  let I (a : Limbs × Bool) (v : RamState) : Prop :=
    RoundState loop.site base a.1 v ∧
    (a.2 = true → WordsAt v.external (base + 40) 64 a.1) ∧
    RamWriteFrame s.external v.external [roundStack base] ∧
    (∀ r ∈ Activation.calleeSavedNumbers, BitVec.ofNat 5 r ≠ loop.counter →
      (Operand.reg (BitVec.ofNat 5 r) : Operand 64).read v =
      (Operand.reg (BitVec.ofNat 5 r) : Operand 64).read s)
  have preserve : ∀ a v t, I a v → AgreesExcept [.reg loop.counter, .flags, .rip] v t → I a t := by
    rintro a v t ⟨hv, hwords, hframe, hregs⟩ hf
    have he := hf.external (by simp [Component.Covers])
    refine ⟨loop.afterDecrement hv hf, fun h => he ▸ hwords h, he ▸ hframe, ?_⟩
    intro r hr hne
    exact (preservedReg hf (by simp [hne])).trans (hregs r hr hne)
  have counterSaved : ∃ r ∈ Activation.calleeSavedNumbers, BitVec.ofNat 5 r = loop.counter := by
    cases loop
    · exact ⟨3, by decide, rfl⟩
    · exact ⟨15, by decide, rfl⟩
    · exact ⟨15, by decide, rfl⟩
  have body : ∀ a k v, I a v → v.RIP = loop.site.pc →
      (Operand.reg loop.counter : Operand 64).read v = BitVec.ofNat 64 (k + 1) →
      ∃ fuel t, Advances boundary fuel v t ∧ ReadyToStep t ∧ CodeIn roundCode t ∧
        stackPtr t ≠ boundary.rsp ∧ t.RIP = loop.site.pc + 60#64 ∧
        (Operand.reg loop.counter : Operand 64).read t = BitVec.ofNat 64 (k + 1) ∧
        I (squareWithOutput a) t := by
    rintro a k v ⟨hv, _, hOldFrame, hOldRegs⟩ hip hcnt
    obtain ⟨fuel, t, ht, hpc, htReady, hw, hf, hregs⟩ :=
      loop.site.squareCopyRound loop.copySite_mem stride hout hroom halign hap hRsp hPush hip hv
    have hcnt' : (Operand.reg loop.counter : Operand 64).read t = BitVec.ofNat 64 (k + 1) := by
      obtain ⟨r, hr, he⟩ := counterSaved
      rw [← he] at hcnt ⊢
      exact (hregs r hr).trans hcnt
    exact ⟨fuel, t, ht, htReady.entry.ready, htReady.entry.code, htReady.rsp ▸ hRsp, hpc, hcnt',
      htReady, fun _ => hw,
      hOldFrame.trans hf (fun r hr => ⟨r, hr, Nat.le_refl _, Nat.le_refl _⟩),
      fun r hr hne => (hregs r hr).trans (hOldRegs r hr hne)⟩
  have hinv : I (words, false) s :=
    ⟨hs, fun h => Bool.noConfusion h, RamWriteFrame.refl _ _, fun _ _ _ => rfl⟩
  obtain ⟨fuel, t, ht, hready, hpc, hreg, hi⟩ :=
    loop.iterate squareWithOutput I preserve body n hn (words, false) s hinv hrip hcounter
  rw [iter_withOutput] at hi
  exact ⟨fuel, t, ht, hpc, hreg, hi.1, hi.2.1 rfl, hi.2.2⟩

def roundCount : SquareLoop → Nat
  | .first44 | .last44 => 44
  | .middle88 => 88

theorem executeRounds [inst : Bindings] (loop : SquareLoop) {boundary : ReturnBoundary}
    {base : BitVec 64} {s : RamState} {words : Limbs}
    (stride : UnitStringStride inst) (hout : ReturnOutside boundary roundCode)
    (hroom : 112 ≤ base.toNat) (halign : base.toNat % 16 = 0)
    (hap : base.toNat + 80 ≤ 0x100000 ∨ 0x12aa00 ≤ base.toNat - 112)
    (hRsp : base ≠ boundary.rsp) (hPush : base - 8 ≠ boundary.rsp)
    (hrip : s.RIP = loop.site.pc)
    (hcounter : (Operand.reg loop.counter : Operand 64).read s = BitVec.ofNat 64 loop.roundCount)
    (hs : RoundState loop.site base words s) :
    ∃ fuel t, Advances boundary fuel s t ∧ t.RIP = loop.site.pc + 65#64 ∧
      (Operand.reg loop.counter : Operand 64).read t = 0 ∧
      RoundState loop.site base (SqrtChain.iter squareWords loop.roundCount words) t ∧
      WordsAt t.external (base + 40) 64 (SqrtChain.iter squareWords loop.roundCount words) ∧
      RamWriteFrame s.external t.external [roundStack base] ∧
      (∀ r ∈ Activation.calleeSavedNumbers, BitVec.ofNat 5 r ≠ loop.counter →
        (Operand.reg (BitVec.ofNat 5 r) : Operand 64).read t =
        (Operand.reg (BitVec.ofNat 5 r) : Operand 64).read s) := by
  have hn : loop.roundCount - 1 < 2^64 := by cases loop <;> decide
  have hpos : loop.roundCount - 1 + 1 = loop.roundCount := by cases loop <;> decide
  have h := loop.iterateWords stride hout hroom halign hap hRsp hPush (loop.roundCount - 1) hn
    hrip (by rw [hpos]; exact hcounter) hs
  rwa [hpos] at h

end SquareLoop

end K256.Proofs.Sec1.Sqrt
