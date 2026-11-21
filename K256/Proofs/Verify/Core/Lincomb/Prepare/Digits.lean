import K256.Proofs.Verify.Core.Lincomb.Prepare.Digits.Calls

namespace K256.Proofs.Verify.Core.Lincomb.Prepare

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Curve

private theorem digitKeepAfter {a b c : Registers}
    (before : ∀ i : Fin Reg.count, i.val ∈ digitSaved → b[i] = a[i])
    (after : ∀ i : Fin Reg.count, i.val ∈ digitSaved → c[i] = b[i]) :
    ∀ i : Fin Reg.count, i.val ∈ digitSaved → c[i] = a[i] :=
  fun i h => (after i h).trans (before i h)

private theorem digitRegisterWord {a : Registers} {i : Fin Reg.count} {word : BitVec 64}
    (h : a[i] = ⟨64, word⟩) : a[i].get 64 = word := by
  rw [h, Value.get_mk]

private theorem headerOutsideStack {sp digits : BitVec 64} (room : 0x558 ≤ sp.toNat)
    (apart : Outside [scratch sp 0x558, ⟨sp.toNat, 8⟩] digits 544)
    {off len : Nat} (fit : off + len ≤ 0x2b8) :
    Outside [⟨digits.toNat, 8⟩] (frameSp sp + BitVec.ofNat 64 off) len := by
  have addr := digitFrameNat room (off := off) (by omega)
  have hi := sp.isLt
  have sep := apart.2 _ (List.mem_cons_self ..)
  refine ⟨by omega, fun r hr => ?_⟩
  obtain rfl := List.mem_singleton.mp hr
  dsimp only [scratch] at sep
  simp only [addr]
  omega

private theorem headerOutsideBuffer {digits : BitVec 64}
    (low : digits.toNat + 544 ≤ 2^64) {off len : Nat}
    (lo : 8 ≤ off) (hi : off < 544) (fit : off + len ≤ 544) :
    Outside [⟨digits.toNat, 8⟩] (digits + BitVec.ofNat 64 off) len := by
  have addr := digitOffsetNat low hi
  refine ⟨by omega, fun r hr => ?_⟩
  obtain rfl := List.mem_singleton.mp hr
  right
  exact by simp only [addr]; omega

private theorem digitHeaderFrame (n : Ram) {digits : BitVec 64}
    (low : digits.toNat + 544 ≤ 2^64) (value : BitVec 64) :
    RamWriteFrame n (memStore n digits value) [⟨digits.toNat, 8⟩] :=
  (RamWriteFrame.refl _ _).memStore value
    ⟨_, .head _, Nat.le_refl _, Nat.le_refl _, by omega⟩

theorem encodeDigits {a b : Registers} {m n : Ram} {sp src tables digits : BitVec 64}
    {k : Nat} (entry : RoutineEntry a m sp 0x558) (bound : k < domain.n)
    (digitsWrite : Writable Extracted.programImage m digits 544)
    (digitsApart : Outside [scratch sp 0x558, ⟨sp.toNat, 8⟩] digits 544)
    (zero : DigitBytes m (digits + 8) [] ∧ DigitBytes m (digits + 0x118) [])
    (split : SplitState a m sp src tables digits k b n) :
    ∃ c o, Reaches .l10f4af b n .l10f52c c o ∧ Recoded a m sp src tables digits k c o := by
  let v₁ := (first k).natAbs
  let v₂ := (second k).natAbs
  let len₁ := BitVec.ofNat 64 (Naf.digits v₁).length
  have h₁ : v₁ < 2^128 := (split_correct k bound).2.1
  have h₂ : v₂ < 2^128 := (split_correct k bound).2.2
  have room := entry.room
  have low := digitsApart.1
  have d₁ : (digits + BitVec.ofNat 64 8).toNat = digits.toNat + 8 := digitOffsetNat low (off := 8) (by decide)
  have d₂ : (digits + BitVec.ofNat 64 0x118).toNat = digits.toNat + 0x118 := digitOffsetNat low (off := 0x118) (by decide)
  have whole₀ : RamWriteFrame m n (digitWhole sp digits) :=
    (RamWriteFrame.refl m _).trans split.frame (by
      intro r h
      obtain rfl := List.mem_singleton.mp h
      exact ⟨_, .head _, Nat.le_refl _, Nat.le_refl _⟩)
  have empty {off : Nat} (lo : off < 544) (fit : off + 257 ≤ 544)
      (h : DigitBytes m (digits + BitVec.ofNat 64 off) []) :
      DigitBytes n (digits + BitVec.ofNat 64 off) [] := by
    have pos := digitOffsetNat low lo
    have sep := digitsApart.2 _ (List.mem_cons_self ..)
    apply Recode.digitBytes_of_frame split.frame _ h
    refine ⟨by rw [pos]; omega, fun r hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    rw [pos]
    dsimp only [scratch] at sep ⊢
    omega
  have empty₁ := empty (off := 8) (by decide) (by decide) zero.1
  have empty₂ := empty (off := 0x118) (by decide) (by decide) zero.2
  have push₁ : StoreOk Extracted.programImage n (digitCallSp sp) 8 0x10f4bf 5 :=
    Recode.storeGuard (off := 16) (digitPushWrite entry whole₀) code_l10f4af (by decide)
  obtain ⟨s₁, call₁, args₁⟩ := serializeFirstBlock (congrArg (Value.get 64) split.rsp) push₁
  obtain ⟨b₁, n₁, step₁, sp₁, bp₁, tmp₁, keep₁, frame₁, input₁⟩ :=
    serializeDigitCall entry whole₀ (off := 0xe0) (v := v₁) (by decide) (by decide)
      split.widths split.control split.firstWords h₁ (by decide) call₁ args₁
  have whole₁ := whole₀.trans frame₁ (serializeWithin room)
  have ctrl₁ := digitControlAfter split.control keep₁
  have widths₁ := digitWidthsAfter split.widths keep₁
    ((congrArg Value.width bp₁).trans (split.widths 5 (by decide))) (congrArg Value.width tmp₁)
  have ptr : memLoad n₁ (frameSp sp + 0xd8) 64 = digits :=
    (frame₁.memLoad_eq (stackOutsideSerialize room (off := 0xd8) (by decide) (Or.inr (by decide)))).trans split.digitPtr
  have ptrRead : LoadOk n₁ (frameSp sp + 0xd8) 8 := by
    have r := (digitScratchWindow entry whole₁ (off := 0xd8) (len := 8) (by decide)).readable
    exact LoadOk.of_region r (Nat.le_refl _) (Nat.le_refl _)
  have push₂ : StoreOk Extracted.programImage n₁ (digitCallSp sp) 8 0x10f4e9 5 :=
    Recode.storeGuard (off := 37) (digitPushWrite entry whole₁) code_l10f4c4 (by decide)
  obtain ⟨r₁, call₂, args₂⟩ := recodeFirstBlock (congrArg (Value.get 64) sp₁)
    (congrArg (Value.get 64) tmp₁) ptr ptrRead push₂
  obtain ⟨b₂, n₂, step₂, sp₂, bp₂, tmp₂, keep₂, frame₂, len₂, bytes₁⟩ :=
    recodeDigitCall entry digitsWrite digitsApart whole₁ (off := 8) (v := v₁) (by decide)
      ctrl₁ widths₁ input₁
      (Recode.digitBytes_of_frame frame₁ (bufferOutsideSerialize room digitsApart (off := 8) (by decide) (by decide)) empty₁)
      h₁ (by decide) call₂ args₂
  have whole₂ := whole₁.trans frame₂ (recodeWithin room (by rw [d₁]; omega) (by rw [d₁]; omega))
  have ctrl₂ := digitControlAfter ctrl₁ keep₂
  have widths₂ := digitWidthsAfter widths₁ keep₂ (congrArg Value.width bp₂)
    ((congrArg Value.width tmp₂).trans (widths₁ 15 (by decide)))
  let header := memStore n₂ digits len₁
  have hdr : RamWriteFrame n₂ header [⟨digits.toNat, 8⟩] := digitHeaderFrame n₂ low len₁
  have wholeHdr : RamWriteFrame m header (digitWhole sp digits) := whole₂.trans hdr (by
    intro r h
    obtain rfl := List.mem_singleton.mp h
    exact ⟨_, .tail _ (.head _), Nat.le_refl _, by change digits.toNat + 8 ≤ digits.toNat + 544; omega⟩)
  have headerWrite : StoreOk Extracted.programImage n₂ digits 8 0x10f4ee 4 := by
    have w : Writable Extracted.programImage n₂ digits 8 :=
      (digitsWrite.of_frame whole₂).sub (Nat.le_refl _) (by omega)
    exact Recode.storeGuard (off := 0) w code_l10f4ee (by decide)
  have push₃ : StoreOk Extracted.programImage header (digitCallSp sp) 8 0x10f502 5 :=
    Recode.storeGuard (off := 20) (digitPushWrite entry wholeHdr) code_l10f4ee (by decide)
  have ax := digitRegisterWord (i := 0) len₂
  obtain ⟨s₂, call₃, args₃⟩ := serializeSecondBlock (value := len₁) (congrArg (Value.get 64) sp₂)
    (congrArg (Value.get 64) bp₂) ax headerWrite push₃
  have words₂ : WordsAt header (frameSp sp + 0xb0) 64 (Generate.Generator.Multiply.scalarWords v₂) := by
    intro i hi
    have same (off : Nat) (fit : off + 8 ≤ 0x2b8) (safe : 0x58 ≤ off) :
        memLoad header (frameSp sp + BitVec.ofNat 64 off) 64 =
          memLoad n (frameSp sp + BitVec.ofNat 64 off) 64 :=
      (hdr.memLoad_eq (headerOutsideStack room digitsApart fit)).trans
        ((frame₂.memLoad_eq (stackOutsideRecode room digitsApart (by rw [d₁]; omega) (by rw [d₁]; omega) fit)).trans
          (frame₁.memLoad_eq (stackOutsideSerialize room fit (Or.inr safe))))
    change memLoad header (frameSp sp + (0xb0#64) + BitVec.ofNat 64 (8*i)) 64 = _
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, same (0xb0 + 8*i) (by omega) (by omega),
      BitVec.ofNat_add, ← BitVec.add_assoc]
    exact split.secondWords i hi
  obtain ⟨b₃, n₃, step₃, sp₃, bp₃, tmp₃, keep₃, frame₃, input₂⟩ :=
    serializeDigitCall entry wholeHdr (off := 0xb0) (v := v₂) (by decide) (by decide)
      widths₂ ctrl₂ words₂ h₂ (by decide) call₃ args₃
  have whole₃ := wholeHdr.trans frame₃ (serializeWithin room)
  have bp₃' := bp₃.trans bp₂
  have ctrl₃ := digitControlAfter ctrl₂ keep₃
  have widths₃ := digitWidthsAfter widths₂ keep₃ (congrArg Value.width bp₃') (congrArg Value.width tmp₃)
  have zero₂ : DigitBytes n₃ (digits + 0x118) [] := by
    apply Recode.digitBytes_of_frame frame₃ (bufferOutsideSerialize room digitsApart (off := 0x118) (by decide) (by decide))
    apply Recode.digitBytes_of_frame hdr (headerOutsideBuffer low (off := 0x118) (by decide) (by decide) (by decide))
    apply Recode.digitBytes_of_frame frame₂ (bufferOutsideRecode room digitsApart (off := 0x118) (by decide) (by decide) (Or.inr (by rw [d₁]; omega)))
    exact Recode.digitBytes_of_frame frame₁ (bufferOutsideSerialize room digitsApart (off := 0x118) (by decide) (by decide)) empty₂
  have push₄ : StoreOk Extracted.programImage n₃ (digitCallSp sp) 8 0x10f527 5 :=
    Recode.storeGuard (off := 32) (digitPushWrite entry whole₃) code_l10f507 (by decide)
  obtain ⟨r₂, call₄, args₄⟩ := recodeSecondBlock (congrArg (Value.get 64) sp₃)
    (congrArg (Value.get 64) tmp₃) bp₃' push₄
  obtain ⟨b₄, n₄, step₄, sp₄, bp₄, tmp₄, keep₄, frame₄, len₂', bytes₂⟩ :=
    recodeDigitCall entry digitsWrite digitsApart whole₃ (off := 0x118) (v := v₂) (by decide)
      ctrl₃ widths₃ input₂ zero₂ h₂ (by decide) call₄ args₄
  have whole₄ := whole₃.trans frame₄ (recodeWithin room (by rw [d₂]; omega) (by rw [d₂]; omega))
  have keep := digitKeepAfter (digitKeepAfter (digitKeepAfter keep₁ keep₂) keep₃) keep₄
  have stackSame (off width : Nat) (fit : off + width / 8 ≤ 0x2b8)
      (apart : off + width / 8 ≤ 0x38 ∨ 0x58 ≤ off) :
      memLoad n₄ (frameSp sp + BitVec.ofNat 64 off) width =
        memLoad n (frameSp sp + BitVec.ofNat 64 off) width :=
    (frame₄.memLoad_eq (stackOutsideRecode room digitsApart (by rw [d₂]; omega) (by rw [d₂]; omega) fit)).trans
      ((frame₃.memLoad_eq (stackOutsideSerialize room fit apart)).trans
        ((hdr.memLoad_eq (headerOutsideStack room digitsApart fit)).trans
          ((frame₂.memLoad_eq (stackOutsideRecode room digitsApart (by rw [d₁]; omega) (by rw [d₁]; omega) fit)).trans
            (frame₁.memLoad_eq (stackOutsideSerialize room fit apart)))))
  have stackSaved (off : BitVec 64) (near : off.toNat ≤ 0x2b8) (far : 8 ≤ off.toNat)
      (safe : off.toNat ≤ 0x260) :
      memLoad n₄ (sp - off) 64 = memLoad n (sp - off) 64 := by
    have eq : frameSp sp + BitVec.ofNat 64 (0x2b8 - off.toNat) = sp - off := by
      have eq' : BitVec.ofNat 64 (0x2b8 - off.toNat) = 0x2b8 - off := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr near), BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega)]
        rfl
      rw [eq']
      unfold frameSp
      bv_omega
    rw [← eq]
    exact stackSame _ 64 (by omega) (Or.inr (by omega))
  have headerLen : memLoad n₄ digits 64 = len₁ := by
    have w₃ := frame₃.memLoad_eq (k := 64) (bufferOutsideSerialize room digitsApart (off := 0) (len := 8) (by decide) (by decide))
    have w₄ := frame₄.memLoad_eq (k := 64) (bufferOutsideRecode room digitsApart (off := 0) (len := 8) (by decide) (by decide)
      (Or.inl (by rw [d₂]; omega)))
    simp only [BitVec.add_zero] at w₃ w₄
    rw [w₄, w₃]
    exact memLoad_memStore_same _ _ _ (by decide) (by decide)
  have bytes₁' : DigitBytes n₄ (digits + 8) (Naf.digits v₁) :=
    Recode.digitBytes_of_frame frame₄ (bufferOutsideRecode room digitsApart (off := 8) (by decide) (by decide)
      (Or.inl (by rw [d₂]; omega)))
      (Recode.digitBytes_of_frame frame₃ (bufferOutsideSerialize room digitsApart (off := 8) (by decide) (by decide))
        (Recode.digitBytes_of_frame hdr (headerOutsideBuffer low (off := 8) (by decide) (by decide) (by decide)) bytes₁))
  exact ⟨b₄, n₄, step₁.trans (step₂.trans (step₃.trans step₄)), {
    rsp := sp₄
    tableBase := (keep 3 (by decide)).trans split.tableBase
    widths := digitWidthsAfter widths₃ keep₄ (congrArg Value.width bp₄)
      ((congrArg Value.width tmp₄).trans (widths₃ 15 (by decide)))
    control := fun i h => (keep i (digitControlMem h)).trans (split.control i h)
    rbx := (stackSaved 48 (by decide) (by decide) (by decide)).trans split.rbx
    r12 := (stackSaved 40 (by decide) (by decide) (by decide)).trans split.r12
    r13 := (stackSaved 32 (by decide) (by decide) (by decide)).trans split.r13
    r14 := (stackSaved 24 (by decide) (by decide) (by decide)).trans split.r14
    r15 := (stackSaved 16 (by decide) (by decide) (by decide)).trans split.r15
    rbp := (stackSaved 8 (by decide) (by decide) (by decide)).trans split.rbp
    frame := whole₄
    pointPtr := (stackSame 0x28 64 (by decide) (Or.inl (by decide))).trans split.pointPtr
    digitPtr := bp₄
    signFirst := (congrArg (Value.get 8) (keep 14 (by decide))).trans split.signFirst
    signSecond := (stackSame 7 8 (by decide) (Or.inl (by decide))).trans split.signSecond
    firstLength := headerLen
    secondLength := len₂'
    firstBytes := bytes₁'
    secondBytes := bytes₂ }⟩

end K256.Proofs.Verify.Core.Lincomb.Prepare
