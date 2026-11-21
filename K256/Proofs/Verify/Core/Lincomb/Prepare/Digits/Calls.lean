import K256.Proofs.Verify.Core.Lincomb.Prepare.Digits.Geometry
import K256.Proofs.Verify.Core.Lincomb.Prepare.Digits.Serialize
import K256.Proofs.Verify.Core.Lincomb.Recode

namespace K256.Proofs.Verify.Core.Lincomb.Prepare

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
open Generate.Generator.Multiply (scalarWords)

abbrev digitCalleeSaved : List Nat := [3,5,12,13,14,15,22,39,50,51]
abbrev digitGprSaved : List Nat := [3,5,12,13,14,15]

private theorem digitFixedMem {i : Nat} (h : i ∈ digitSaved) : i ∈ digitCalleeSaved := by
  simp only [digitSaved, digitCalleeSaved, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
  omega

theorem digitControlMem {i : Nat} (h : i ∈ [22,39,50,51]) : i ∈ digitSaved := by
  simp only [digitSaved, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
  omega

theorem digitWidthsAfter {b c : Registers}
    (before : ∀ i : Fin Reg.count, i.val ∈ digitGprSaved → b[i].width = 64)
    (keep : ∀ i : Fin Reg.count, i.val ∈ digitSaved → c[i] = b[i])
    (bp : c[5].width = 64) (r15 : c[15].width = 64) :
    ∀ i : Fin Reg.count, i.val ∈ digitGprSaved → c[i].width = 64 := by
  intro ⟨i, hi⟩ h
  simp only [digitGprSaved, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl
  · exact (congrArg Value.width (keep 3 (by decide))).trans (before 3 (by decide))
  · exact bp
  · exact (congrArg Value.width (keep 12 (by decide))).trans (before 12 (by decide))
  · exact (congrArg Value.width (keep 13 (by decide))).trans (before 13 (by decide))
  · exact (congrArg Value.width (keep 14 (by decide))).trans (before 14 (by decide))
  · exact r15

theorem digitControlAfter {a b c : Registers}
    (control : ∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → b[i] = a[i])
    (keep : ∀ i : Fin Reg.count, i.val ∈ digitSaved → c[i] = b[i]) :
    ∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → c[i] = a[i] :=
  fun i h => (keep i (digitControlMem h)).trans (control i h)

private theorem digitBelowWindow {a : Registers} {m n : Ram} {sp digits : BitVec 64}
    (entry : RoutineEntry a m sp 0x558) (frame : RamWriteFrame m n (digitWhole sp digits))
    {off : BitVec 64} {len : Nat} (lower : off.toNat ≤ 0x558) (upper : len ≤ off.toNat) :
    Writable Extracted.programImage n (sp - off) len :=
  (Recode.stackSlot entry lower upper).of_frame frame

theorem digitPushWrite {a : Registers} {m n : Ram} {sp digits : BitVec 64}
    (entry : RoutineEntry a m sp 0x558) (frame : RamWriteFrame m n (digitWhole sp digits)) :
    Writable Extracted.programImage n (digitCallSp sp) 8 := by
  rw [show digitCallSp sp = sp - 0x2c0 by unfold digitCallSp frameSp; bv_omega]
  exact digitBelowWindow entry frame (by decide) (by decide)

private theorem digitCallNat {sp : BitVec 64} (room : 0x558 ≤ sp.toNat) :
    (digitCallSp sp).toNat = sp.toNat - 0x2c0 := by
  rw [show digitCallSp sp = sp - 0x2c0 by unfold digitCallSp frameSp; bv_omega]
  exact digitStackNat room (by decide)

private theorem digitReturnRsp (sp : BitVec 64) : digitCallSp sp + 8 = frameSp sp :=
  BitVec.sub_add_cancel _ _

private theorem magnitudeLoad {m : Ram} {p : BitVec 64} {v : Nat}
    (bound : v < 2^128) (w : WordsAt m p 64 (scalarWords v)) :
    memLoad m p 128 = BitVec.ofNat 128 v := by
  have wl : (memLoad m p 128).extractLsb' 0 64 = BitVec.ofNat 64 v := by
    rw [extractLsb'_memLoad _ _ _ _ (by decide) (by decide) (by decide)]
    change memLoad m (p + 0) 64 = _
    have h : memLoad m (p + 0) 64 = BitVec.ofNat 64 (v / 1) := w 0 (by decide)
    rwa [Nat.div_one] at h
  have wh : (memLoad m p 128).extractLsb' 64 64 = BitVec.ofNat 64 (v / 2^64) := by
    rw [extractLsb'_memLoad _ _ _ _ (by decide) (by decide) (by decide)]
    change memLoad m (p + 8) 64 = _
    exact w 1 (by decide)
  apply BitVec.eq_of_toNat_eq
  have lo := congrArg BitVec.toNat wl
  have hi := congrArg BitVec.toNat wh
  have fit := (memLoad m p 128).isLt
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.pow_zero, Nat.div_one] at lo hi
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
  rw [Nat.mod_eq_of_lt (by omega : (memLoad m p 128).toNat / 2^64 < 2^64),
    Nat.mod_eq_of_lt (by omega : v / 2^64 < 2^64)] at hi
  have l := Nat.mod_add_div ((memLoad m p 128).toNat) (2^64)
  have r := Nat.mod_add_div v (2^64)
  omega

set_option maxRecDepth 1600 in
theorem serializeDigitCall {a b c : Registers} {m n start : Ram} {sp digits : BitVec 64}
    {site after : Label} {off v : Nat} {ret : BitVec 64}
    (entry : RoutineEntry a m sp 0x558) (frame : RamWriteFrame m n (digitWhole sp digits))
    (fit : off + 32 ≤ 0x2b8) (apart : 0x58 ≤ off)
    (widths : ∀ i : Fin Reg.count, i.val ∈ digitGprSaved → b[i].width = 64)
    (control : ∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → b[i] = a[i])
    (words : WordsAt n (frameSp sp + BitVec.ofNat 64 off) 64 (scalarWords v))
    (bound : v < 2^128) (small : ret.toNat < 2^32)
    (dispatch : program.runBlock (dialect Extracted.programImage) ⟨site,b,start⟩ =
      .call ⟨.l10a2f0,c,memStore n (digitCallSp sp) ret⟩ (callResume after ret))
    (args : SerializeArgs b c sp (frameSp sp + BitVec.ofNat 64 off)) :
    ∃ d t, Reaches site b start after d t ∧ d[4] = ⟨64, frameSp sp⟩ ∧
      d[5] = b[5] ∧ d[15] = ⟨64, digitTemp sp⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ digitSaved → d[i] = b[i]) ∧
      RamWriteFrame n t (serializeWrites sp) ∧ memLoad t (digitTemp sp) 128 = BitVec.ofNat 128 v := by
  let pushed := memStore n (digitCallSp sp) ret
  have pf : RamWriteFrame n pushed (serializeWrites sp) :=
    digitPushFrame entry.room ret (.head _)
  have keepControl := digitControlAfter control args.keep
  have keepWidths := digitWidthsAfter widths args.keep
    ((congrArg Value.width args.bp).trans (widths 5 (by decide))) (congrArg Value.width args.temp)
  have pw : WordsAt pushed (frameSp sp + BitVec.ofNat 64 off) 64 (scalarWords v) := by
    intro i hi
    simp only [wordAddr]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add,
      pf.memLoad_eq (stackOutsideSerialize entry.room (off := off + 8*i) (by omega) (Or.inr (by omega))),
      BitVec.ofNat_add, ← BitVec.add_assoc]
    exact words i hi
  have addr := digitFrameNat entry.room (off := off) (by omega)
  have tmp := digitFrameNat entry.room (off := 0x38) (by decide)
  change (digitTemp sp).toNat = _ at tmp
  have top := digitCallNat entry.room
  have room := entry.room
  have modulus := entry.aligned
  have rwRet : memLoad pushed (digitCallSp sp) 64 = ret :=
    memLoad_memStore_same _ _ _ (by decide) (by decide)
  obtain ⟨out, run, tag, rsp, keep, sf, w⟩ := serializeForDigits args.rsp args.si args.di keepWidths
    ((keepControl 22 (by decide)).trans entry.df)
    ((congrArg Value.width (keepControl 39 (by decide))).trans entry.mxcsr)
    ((congrArg Value.width (keepControl 50 (by decide))).trans entry.ftw)
    ((congrArg Value.width (keepControl 51 (by decide))).trans entry.fcw)
    (show (digitCallSp sp).toNat % 16 = 8 by omega)
    ((digitPushWrite entry frame).readable.of_frame pf) rwRet small
    ((digitScratchWindow entry frame fit).readable.of_frame pf)
    ((digitScratchWindow entry frame (off := 0x38) (len := 32) (by decide)).of_frame pf)
    pw (Or.inl (by omega)) (Or.inr (by omega))
  refine ⟨_, _, reachesCall dispatch run tag, (digitReturnRsp sp ▸ rsp),
    (keep 5 (by decide)).trans args.bp, (keep 15 (by decide)).trans args.temp,
    fun i h => (keep i (digitFixedMem h)).trans (args.keep i h), ?_, magnitudeLoad bound w⟩
  apply pf.trans sf
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact ⟨_, .tail _ (.head _), Nat.le_refl _, Nat.le_refl _⟩

set_option maxRecDepth 1600 in
theorem recodeDigitCall {a b c : Registers} {m n : Ram} {sp digits : BitVec 64}
    {site after : Label} {off v : Nat} {ret : BitVec 64}
    (entry : RoutineEntry a m sp 0x558) (digitsWrite : Writable Extracted.programImage m digits 544)
    (apart : Outside [scratch sp 0x558, ⟨sp.toNat, 8⟩] digits 544)
    (frame : RamWriteFrame m n (digitWhole sp digits))
    (fit : off + 257 ≤ 544) (control : ∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → b[i] = a[i])
    (widths : ∀ i : Fin Reg.count, i.val ∈ digitGprSaved → b[i].width = 64)
    (input : memLoad n (digitTemp sp) 128 = BitVec.ofNat 128 v)
    (zero : DigitBytes n (digits + BitVec.ofNat 64 off) [])
    (bound : v < 2^128) (small : ret.toNat < 2^32)
    (dispatch : program.runBlock (dialect Extracted.programImage) ⟨site,b,n⟩ =
      .call ⟨.l1107b0,c,memStore n (digitCallSp sp) ret⟩ (callResume after ret))
    (args : RecodeArgs b c sp digits (digits + BitVec.ofNat 64 off)) :
    ∃ d t, Reaches site b n after d t ∧ d[4] = ⟨64, frameSp sp⟩ ∧
      d[5] = ⟨64, digits⟩ ∧ d[15] = b[15] ∧
      (∀ i : Fin Reg.count, i.val ∈ digitSaved → d[i] = b[i]) ∧
      RamWriteFrame n t (recodeWrites sp (digits + BitVec.ofNat 64 off)) ∧
      d[0] = ⟨64, BitVec.ofNat 64 (Naf.digits v).length⟩ ∧
      DigitBytes t (digits + BitVec.ofNat 64 off) (Naf.digits v) := by
  let pushed := memStore n (digitCallSp sp) ret
  let dst := digits + BitVec.ofNat 64 off
  have room := entry.room
  have pf : RamWriteFrame n pushed (recodeWrites sp dst) := digitPushFrame room ret (.head _)
  have low := apart.1
  have dstNat : dst.toNat = digits.toNat + off :=
    digitOffsetNat low (by omega)
  have whole := frame.trans pf (recodeWithin room (by omega) (by omega))
  have keepControl := digitControlAfter control args.keep
  have keepWidths := digitWidthsAfter widths args.keep
    (congrArg Value.width args.bp) ((congrArg Value.width args.temp).trans (widths 15 (by decide)))
  have top := digitCallNat room
  have base := digitStackNat room (off := 0x2b8) (by decide)
  change (frameSp sp).toNat = sp.toNat - 0x2b8 at base
  have alignment := entry.aligned
  have slotRet : memLoad pushed (digitCallSp sp) 64 = ret :=
    memLoad_memStore_same _ _ _ (by decide) (by decide)
  have childWin : Writable Extracted.programImage pushed (digitCallSp sp - 0x110) 0x110 := by
    rw [show digitCallSp sp - 0x110 = sp - 0x3d0 by unfold digitCallSp frameSp; bv_omega]
    exact digitBelowWindow entry whole (by decide) (by decide)
  have child : RoutineEntry c pushed (digitCallSp sp) 0x110 :=
    ⟨args.rsp, keepWidths, (keepControl 22 (by decide)).trans entry.df,
      (congrArg Value.width (keepControl 39 (by decide))).trans entry.mxcsr,
      (congrArg Value.width (keepControl 50 (by decide))).trans entry.ftw,
      (congrArg Value.width (keepControl 51 (by decide))).trans entry.fcw, by omega, by omega, childWin,
      (digitPushWrite entry whole).readable, by rw [slotRet]; exact small, digitImage entry digitsWrite whole⟩
  have safeTemp := stackOutsideRecode room apart (dst := dst) (by omega) (by omega)
    (off := 0x38) (len := 16) (by decide)
  have dstZero : DigitBytes pushed dst [] := by
    apply Recode.digitBytes_of_frame (digitPushFrame room ret (.head _) :
      RamWriteFrame n pushed [scratch (frameSp sp) 0x118]) _ zero
    have sep := apart.2 _ (List.mem_cons_self ..)
    change Outside [scratch (frameSp sp) 0x118] dst 257
    refine ⟨by omega, fun r hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    dsimp only [scratch] at sep ⊢
    omega
  have source : Outside [scratch (digitCallSp sp) 0x110, ⟨dst.toNat, 257⟩] (digitTemp sp) 16 := by
    refine ⟨safeTemp.1, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · have tmp := digitFrameNat room (off := 0x38) (by decide)
      change (digitTemp sp).toNat = sp.toNat - 0x2b8 + 0x38 at tmp
      right
      dsimp only [scratch]
      omega
    · exact safeTemp.2 _ (.tail _ (.head _))
  have dest : Outside [scratch (digitCallSp sp) 0x110, ⟨(digitCallSp sp).toNat, 8⟩] dst 257 := by
    have sep := apart.2 _ (List.mem_cons_self ..)
    refine ⟨by omega, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    dsimp only [scratch] at sep
    rcases hr with rfl | rfl
    · dsimp only [scratch]; omega
    · dsimp only; omega
  obtain ⟨out, run, result, len, bytes⟩ := recode child args.di args.si args.dx args.cx args.r8 args.r9
    bound ((pf.memLoad_eq safeTemp).trans input)
    (digitScratchWindow entry whole (off := 0x38) (len := 16) (by decide)).readable
    dstZero (digitBufferWindow digitsWrite whole (by omega) fit) source dest
  have tag := result.tag.trans (congrArg (fun x => some (Value.mk 64 x)) slotRet)
  refine ⟨_, _, reachesCall dispatch run tag, digitReturnRsp sp ▸ result.rsp,
    (result.saved 5 (by decide)).trans args.bp, (result.saved 15 (by decide)).trans args.temp,
    fun i h => (result.saved i (digitFixedMem h)).trans (args.keep i h), ?_, len, bytes⟩
  apply pf.trans result.frame
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, .head _, by dsimp only [scratch]; omega, by dsimp only [scratch]; omega⟩
  · exact ⟨_, .tail _ (.head _), Nat.le_refl _, Nat.le_refl _⟩

end K256.Proofs.Verify.Core.Lincomb.Prepare
