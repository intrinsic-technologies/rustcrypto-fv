import K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.FullBlock.State
import K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.Copy
import K256.Proofs.ParseSignature.Memory

namespace K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.FullBlock

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  K256.Proofs.Verify.Hash Standards.NIST.SHA2

private def testAt (second : Bool) : Label := if second then .l10481a else .l10424a
private def fillCopyAt (second : Bool) : Label := if second then .l104823 else .l104253
private def fillRet (second : Bool) : BitVec 64 := if second then 0x104830 else 0x104263
private def fillOffset (second : Bool) : Nat := if second then 425 else 257

local macro "fill_kept" : tactic => `(tactic|
  (rintro ⟨i, hi⟩ h
   simp only [List.mem_cons, List.not_mem_nil, or_false] at h
   repeat' first | (subst i; rfl) | (rcases h with h | h)))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1200000 in
private theorem fillHeader {fr : Activation} {a : Verify.Core.Registers} {m : Ram}
    (second : Bool) (regs : Cursor second fr a 0) (rsp : a[4].get 64 = sp fr)
    (headRead : LoadOk m fr.rsi 8) (lenRead : LoadOk m (fr.rsi + 8) 8)
    (headWord : memLoad m fr.rsi 64 = fr.rsp + 320)
    (lenWord : memLoad m (fr.rsi + 8) 64 = 32)
    (markRead : LoadOk m (context fr second + 127) 1)
    (mark : memLoad m (context fr second + 127) 8 = 33) :
    ∃ b : Verify.Core.Registers, program.runBlock (dialect Extracted.programImage) ⟨loopAt second,a,m⟩ =
        .jump ⟨testAt second,b,m⟩ ∧
      b[2] = ⟨64,31⟩ ∧ b[7] = ⟨64,33⟩ ∧
      (if second then b[6] else b[3]) = ⟨64,fr.rsp + 320⟩ ∧
      (if second then b[12] else b[5]) = ⟨64,1⟩ ∧
      (second = true → b[5] = a[5]) ∧
      (∀ i : Fin Reg.count, i.val ∈ [4,13,14,15,22,39,50,51] → b[i] = a[i]) := by
  have slice : (if second then a[14] else a[15]).get 64 = fr.rsi := by
    rw [regs.slice]
    change fr.rsi + 0 = fr.rsi
    exact BitVec.add_zero _
  have cf : (subSpec (32 : BitVec 64) (64 - BitVec.setWidth 64 (33 : BitVec 8))).snd.CF = false := by decide
  cases second <;>
    simp only [loopAt, testAt, context, Bool.false_eq_true, ite_false, ite_true,
      BitVec.add_assoc, BitVec.reduceAdd] at slice markRead mark ⊢
  all_goals
    refine Exists.intro ?_ ?_
    rotate_left
    constructor
    · first
      | change program.runBlock _ ⟨.l10422b,a,m⟩ = _
      | change program.runBlock _ ⟨.l1047fb,a,m⟩ = _
      first
      | change LoadOk m (sp fr + 287) 1 at markRead
        change memLoad m (sp fr + 287) 8 = 33 at mark
      | change LoadOk m (sp fr + 455) 1 at markRead
        change memLoad m (sp fr + 455) 8 = 33 at mark
      cfg_eval [rsp, slice, headRead, lenRead, headWord, lenWord, markRead, mark, cf]
      first | rfl | simp only [markRead, mark, cf, Bool.false_eq_true, ↓reduceIte] <;> rfl
    · refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
      · intro h
        cases h <;> rfl
      · fill_kept

set_option maxRecDepth 4096 in
private theorem fillTest {a : Verify.Core.Registers} {m : Ram}
    (second : Bool) (mark : a[7].get 64 = 33) :
    ∃ b : Verify.Core.Registers, program.runBlock (dialect Extracted.programImage) ⟨testAt second,a,m⟩ =
        .jump ⟨fillCopyAt second,b,m⟩ ∧
      (if second then b[6] else b[3]) = (if second then a[6] else a[3]) ∧
      ∀ i : Fin Reg.count, i.val ∈ [2,4,5,7,12,13,14,15,22,39,50,51] →
        b[i] = a[i] := by
  have zf : (testFlags (33 : BitVec 64)).ZF.getD false = false := by decide
  cases second
  all_goals
    refine Exists.intro ?_ ?_
    rotate_left
    constructor
    · first
      | change program.runBlock _ ⟨.l10424a,a,m⟩ = _
      | change program.runBlock _ ⟨.l10481a,a,m⟩ = _
      cfg_eval [mark, zf] <;> rfl
    · exact ⟨rfl, by fill_kept⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem fillEnter {fr : Activation} {a : Verify.Core.Registers} {m : Ram}
    (second : Bool) (rsp : a[4].get 64 = sp fr) (buf : a[13].get 64 = context fr second + 64)
    (src : (if second then a[6] else a[3]) = ⟨64,fr.rsp + 320⟩)
    (mark : a[7].get 64 = 33) (copyLen : a[2].get 64 = 31)
    (pushWrite : Writable Extracted.programImage m (sp fr - 8) 8)
    (gotRead : LoadOk m 0x203dd0 8) (got : memLoad m 0x203dd0 64 = 0x12a820) :
    ∃ c : Verify.Core.Registers,
      program.runBlock (dialect Extracted.programImage) ⟨fillCopyAt second,a,m⟩ =
        .call ⟨.l12a820,c,memStore m (sp fr - 8) (fillRet second)⟩
          (Verify.Core.Lincomb.callResume (compressAt second) (fillRet second)) ∧
      c[4].get 64 = sp fr - 8 ∧ c[7].get 64 = sp fr + BitVec.ofNat 64 (fillOffset second) ∧
      c[6].get 64 = fr.rsp + 320 ∧ c[3].width = 64 ∧
      (if second then c[3] else c[12]) = ⟨64,fr.rsp + 351⟩ ∧
      (second = true → c[12] = a[12]) ∧
      (∀ i : Fin Reg.count, i.val ∈ [2,5,13,14,15,22,39,50,51] → c[i] = a[i]) := by
  have nextAddress : fr.rsp + 320 + 31 = fr.rsp + 351 := by bv_omega
  have dstAddress : 33 + (context fr second + 64) = sp fr + BitVec.ofNat 64 (fillOffset second) := by
    cases second <;> simp only [context, fillOffset, Bool.false_eq_true, ite_false, ite_true] <;> bv_omega
  cases second
  all_goals
    simp only [Bool.false_eq_true, ite_false, ite_true] at src
    have srcGet := congrArg (Value.get 64) src
    refine Exists.intro ?_ ?_
    rotate_left
    constructor
    · first
      | change program.runBlock _ ⟨.l104253,a,m⟩ = _
        have push : StoreOk Extracted.programImage m (sp fr - 8) 8 0x10425d 6 :=
          ParseSignature.storeOk_of_codeRange (off := 10) pushWrite
            (fun x hx => Common.fnCode_subset_programImage x (code_l104253 x hx)) (by decide +kernel)
      | change program.runBlock _ ⟨.l104823,a,m⟩ = _
        have push : StoreOk Extracted.programImage m (sp fr - 8) 8 0x10482a 6 :=
          ParseSignature.storeOk_of_codeRange (off := 7) pushWrite
            (fun x hx => Common.fnCode_subset_programImage x (code_l104823 x hx)) (by decide +kernel)
      cfg_eval [rsp, buf, srcGet, src, mark, copyLen, push, gotRead, got, nextAddress, dstAddress] <;> rfl
    · refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, by fill_kept⟩
      · first | exact dstAddress | rfl
      · first | exact srcGet | rfl
      · first | exact congrArg Value.width src | rfl
      · first | rfl | congr 1; bv_omega
      · intro h
        cases h <;> rfl

private theorem fillDestination (fr : Activation) (second : Bool) :
    sp fr + BitVec.ofNat 64 (fillOffset second) = context fr second + 64 + 33 := by
  cases second <;> simp only [fillOffset, context, ite_true, Bool.false_eq_true, ite_false] <;> bv_omega

private theorem fillMarkAddress (fr : Activation) (second : Bool) :
    context fr second + 127 = sp fr + BitVec.ofNat 64 (fillOffset second + 30) := by
  rw [BitVec.ofNat_add, ← BitVec.add_assoc, fillDestination]
  bv_omega

private theorem secretPrefix {fr : Activation} {m : Ram} {secret : ByteArray}
    (sec : (⟨(fr.rsp + 320).toNat,32⟩ : MemoryRegion).HasBytes m secret) :
    (⟨(fr.rsp + 320).toNat,31⟩ : MemoryRegion).HasBytes m (secret.extract 0 31) := by
  have len : secret.size = 32 := sec.1
  have cutLen : (secret.extract 0 31).size = 31 := by rw [ByteArray.size_extract, len]; decide
  refine ⟨cutLen, fun i => ?_⟩
  have hi : i.val < 31 := by simpa only [cutLen] using i.isLt
  simpa only [ByteArray.getElem_extract, Nat.zero_add] using sec.2 ⟨i.val, by omega⟩

set_option maxHeartbeats 600000 in
private theorem fillMemory {fr : Activation} {input : Input} {m : Ram} {state : State}
    {secret : ByteArray} (second : Bool) (env : Environment fr input)
    (slots : Slots fr m) (taggedLen : (taggedValue second state).size = 33)
    (ctx : UpdateV.HmacStateAt m (context fr second) state.key (taggedValue second state))
    (srcBytes : (⟨(fr.rsp + 320).toNat,31⟩ : MemoryRegion).HasBytes m (secret.extract 0 31)) :
    let dst := sp fr + BitVec.ofNat 64 (fillOffset second)
    let src := fr.rsp + 320
    let slot := sp fr - 8
    let rs := copyRegions (sp fr) dst 31
    let n := memCopy (memStore m slot (fillRet second)) dst src 31
    RamWriteFrame m n rs → LocalWrites fr rs ∧ Slots fr n ∧ Filled second fr n state secret := by
  dsimp only
  intro frame
  let dst := sp fr + BitVec.ofNat 64 (fillOffset second)
  let src := fr.rsp + 320
  let slot := sp fr - 8
  let rs := copyRegions (sp fr) dst 31
  let u := memStore m slot (fillRet second)
  let n := memCopy u dst src 31
  let p := context fr second
  let k : Nat := if second then 328 else 160
  have dep := env.depth
  have lim := env.limit
  have base := spNat env
  have hk : k = 160 ∨ k = 328 := by cases second <;> decide
  have offset : fillOffset second = k + 97 := by cases second <;> rfl
  have bottom : fr.low.toNat = fr.rsp.toNat - 1920 := by
    rw [env.low, BitVec.toNat_sub_of_le (show (1920 : BitVec 64) ≤ fr.rsp from dep)]
    rfl
  have pn : p.toNat = (sp fr).toNat + k := by cases second <;> exact spAddNat env _ (by decide)
  have addr (off : BitVec 64) (h : off.toNat ≤ 168) :
      (p + off).toNat = (sp fr).toNat + k + off.toNat := by
    rw [BitVec.toNat_add, pn, Nat.mod_eq_of_lt (by omega)]
  have destN : dst.toNat = (sp fr).toNat + k + 97 := by
    dsimp only [dst]
    rw [spAddNat env _ (by omega), offset, Nat.add_assoc]
  have slotN : slot.toNat = (sp fr).toNat - 8 := BitVec.toNat_sub_of_le
    (show (8 : BitVec 64) ≤ sp fr from (by change 8 ≤ (sp fr).toNat; omega))
  have srcN : src.toNat = fr.rsp.toNat + 320 := by
    change (fr.rsp+320).toNat = _
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by change fr.rsp.toNat + 320 < 2^64; omega)]
    rfl
  have localWrites : LocalWrites fr rs := by
    intro r hr
    rcases List.mem_cons.mp hr with rfl | h
    · change fr.low.toNat ≤ slot.toNat ∧ slot.toNat + 8 ≤ fr.rsp.toNat - 48
      omega
    · obtain rfl := List.mem_singleton.mp h
      change fr.low.toNat ≤ dst.toNat ∧ dst.toNat + 31 ≤ fr.rsp.toNat - 48
      omega
  have outside {q : BitVec 64} {len : Nat} (lim : q.toNat + len ≤ 2^64)
      (above : slot.toNat + 8 ≤ q.toNat)
      (away : q.toNat + len ≤ dst.toNat ∨ dst.toNat + 31 ≤ q.toNat) :
      Outside rs q len := by
    refine ⟨lim, fun r hr => ?_⟩
    rcases List.mem_cons.mp hr with rfl | h
    · exact Or.inr above
    · obtain rfl := List.mem_singleton.mp h
      exact away
  have slotOutside (off : BitVec 64) (bound : off.toNat ≤ 120) : Outside rs (sp fr + off) 8 := by
    have adr : (sp fr + off).toNat = (sp fr).toNat + off.toNat := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
    exact outside (by omega) (by omega) (.inl (by omega))
  have slots' := slotsAfter slots frame (slotOutside 8 (by decide)) (slotOutside 112 (by decide))
    (slotOutside 120 (by decide))
  have pushed : RamWriteFrame m u [⟨slot.toNat,8⟩] := (RamWriteFrame.refl m _).memStore _
    ⟨_, List.mem_singleton_self _, Nat.le_refl _, Nat.le_refl _, by change slot.toNat + 8 ≤ 2^64; omega⟩
  have pushedBytes := UpdateV.Finalize.bytesAfter pushed (p := src)
    ⟨by omega, fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact .inr (by change slot.toNat + 8 ≤ src.toNat; omega)⟩
    srcBytes
  have copied := Sec1.Wrapper.Copy.memCopy_hasBytes (dst := dst) (by decide : 31 ≤ 2^64) pushedBytes
  have paddedLen : (padded second state).size = 97 := by
    rw [padded, ByteArray.size_append, UpdateV.keyPad_size, taggedLen]
  have remLen : (remainderBytes (padded second state)).size = 33 := by rw [remainderBytes_size, paddedLen]
  have bufN := addr 64 (by decide)
  have hashN := addr 128 (by decide)
  have countN := addr 160 (by decide)
  simp only [BitVec.reduceToNat] at bufN hashN countN
  have bufferPrefix := UpdateV.Finalize.bytesAfter frame (p := p + 64) (n := 33)
    (outside (by omega) (by omega) (.inl (by omega))) (by simpa only [taggedLen] using ctx.buffer)
  have combined := appendBytes (address := p + 64) (first := remainderBytes (padded second state))
    (second := secret.extract 0 31) (by rw [remLen]; exact bufferPrefix) (by
      rw [remLen, srcBytes.1]
      exact fillDestination fr second ▸ copied)
  have cutLen : (secret.extract 0 31).size = 31 := srcBytes.1
  refine ⟨localWrites, slots', UpdateV.Finalize.bytesAfter frame
    (outside (q := p) (by omega) (by omega) (.inl (by omega))) ctx.outer, ?_, ?_, ?_⟩
  · change (⟨(p+64).toNat,64⟩ : MemoryRegion).HasBytes n (blockBytes second state secret)
    simpa only [blockBytes, ByteArray.size_append, remLen, cutLen, Nat.reduceAdd] using combined
  · exact UpdateV.Finalize.stateAfter frame (outside (q := p+128) (by omega) (by omega)
      (.inr (by omega))) ctx.hash
  · rw [frame.memLoad_eq (outside (q := p+160) (len := 8) (by omega) (by omega) (.inr (by omega)))]
    simpa only [taggedLen, show BitVec.ofNat 64 (1 + 33 / 64) = (1 : BitVec 64) by decide] using ctx.count


set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem fill {fr : Activation} {state : State} {secret reduced : ByteArray}
    {a : Verify.Core.Registers} {m : Ram} (second : Bool) (env : Environment fr (.seeded secret reduced))
    (live : Live (loopAt second) fr a m state) (slots : Slots fr m)
    (regs : Cursor second fr a 0) (ctx : UpdateV.HmacStateAt m (context fr second) state.key (taggedValue second state)) :
    ∃ b n, Verify.Core.Reaches (loopAt second) a m (compressAt second) b n ∧
      Live (compressAt second) fr b n state ∧ Slots fr n ∧ Pending second fr b ∧
      Filled second fr n state secret := by
  have rsp : a[4] = ⟨64,sp fr⟩ := by cases second <;> exact live.atoms.1
  have df : a[22] = ⟨1,0⟩ := by cases second <;> exact live.atoms.2.1
  have tail : FrameTail fr a m := by
    cases second
    · exact live.atoms.2.2.2.2.2.2.2
    · exact live.atoms.2.2.2.2.2
  have tailAccess := tail
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,gotRead,got,_⟩ := tailAccess
  obtain ⟨_, _, _, inputLimit, desRead, ptr, len, _, _, _, _, sec, _⟩ := env.slicesAt live.writes
  change fr.rsp.toNat + 352 < 2^32 at inputLimit
  have rd : Readable m fr.rsi 48 := desRead
  have headRead : LoadOk m fr.rsi 8 := LoadOk.of_region rd (Nat.le_refl _) (by have := rd.low; omega)
  have lenRead : LoadOk m (fr.rsi+8) 8 := LoadOk.of_offsets rd
    rfl (BitVec.add_zero _).symm (by decide)
  have taggedLen : (taggedValue second state).size = 33 := by
    rw [taggedValue, ByteArray.size_append, live.bytes.value.1]
    rfl
  have used : memLoad m (context fr second + 127) 8 = 33 := by
    simpa only [taggedLen, show BitVec.ofNat 8 (33 % 64) = (33 : BitVec 8) by decide] using ctx.used
  have dep := env.depth
  have base := spNat env
  have offBound : fillOffset second + 31 ≤ 664 := by cases second <;> decide
  have bottom : fr.low.toNat = fr.rsp.toNat - 1920 := by
    rw [env.low, BitVec.toNat_sub_of_le (show (1920 : BitVec 64) ≤ fr.rsp from dep)]
    rfl
  have slotN : (sp fr-8).toNat = (sp fr).toNat - 8 := BitVec.toNat_sub_of_le
    (show (8 : BitVec 64) ≤ sp fr from (by change 8 ≤ (sp fr).toNat; omega))
  have markN : (context fr second+127).toNat = (sp fr).toNat + (fillOffset second + 30) := by
    rw [fillMarkAddress, spAddNat env _ (by omega)]
  have push : Writable Extracted.programImage m (sp fr-8) 8 := stackWritable env live.writes (by omega) (by omega)
  have markW : Writable Extracted.programImage m (context fr second + 127) 1 :=
    stackWritable env live.writes (by omega) (by omega)
  have markRead : LoadOk m (context fr second + 127) 1 := ⟨markW.readable.low, markW.readable.present⟩
  have srcN : (fr.rsp+320).toNat = fr.rsp.toNat + 320 := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by change fr.rsp.toNat + 320 < 2^64; omega)]
    rfl
  have srcBytes := secretPrefix sec
  have srcRead := Readable.of_hasBytes srcBytes (by
    change (fr.rsp+320).toNat + 31 < 2^32
    omega)
  change Readable m (BitVec.ofNat 64 (fr.rsp+320).toNat) (secret.extract 0 31).size at srcRead
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, srcBytes.1] at srcRead
  obtain ⟨h, start, hxLen, hxMark, hxSrc, hxLeft, hxHash, hxKept⟩ :=
    fillHeader second regs (congrArg (Value.get 64) rsp) headRead lenRead ptr len markRead used
  obtain ⟨d, branch, dxSrc, dxKept⟩ := fillTest (m := m) second (congrArg (Value.get 64) hxMark)
  have dRsp := congrArg (Value.get 64) ((dxKept 4 (by decide)).trans ((hxKept 4 (by decide)).trans rsp))
  have dBuf := congrArg (Value.get 64) ((dxKept 13 (by decide)).trans ((hxKept 13 (by decide)).trans regs.buf))
  have dMark := congrArg (Value.get 64) ((dxKept 7 (by decide)).trans hxMark)
  have dLen := congrArg (Value.get 64) ((dxKept 2 (by decide)).trans hxLen)
  obtain ⟨c, called, crsp, cdi, csi, c3Width, cNext, c12, cKept⟩ :=
    fillEnter second dRsp dBuf (dxSrc.trans hxSrc) dMark dLen push ⟨gotRead.low,gotRead.present⟩ got
  have cLen := congrArg (Value.get 64) ((cKept 2 (by decide)).trans ((dxKept 2 (by decide)).trans hxLen))
  have cDf := congrArg (Value.get 1)
    ((cKept 22 (by decide)).trans ((dxKept 22 (by decide)).trans ((hxKept 22 (by decide)).trans df)))
  obtain ⟨b, copyRun, brsp, bKept, frame⟩ := copyCall env live.writes offBound
    (show (fillRet second).toNat < 2^32 by cases second <;> decide)
    called crsp cdi csi cLen cDf srcRead (Or.inr (by omega))
  obtain ⟨locality, newSlots, filled⟩ := fillMemory second env slots taggedLen ctx srcBytes frame
  have keep (i : Fin Reg.count) (hi : i.val ∈ [13,14,15,22,39,50,51]) : b[i] = a[i] := by
    obtain ⟨i, hi'⟩ := i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi | hi | hi | hi | hi | hi <;> subst i
    all_goals
      exact (bKept _ (by dsimp only; decide)).trans ((cKept _ (by dsimp only; decide)).trans
        ((dxKept _ (by dsimp only; decide)).trans (hxKept _ (by dsimp only; decide))))
  have b5 : b[5] = d[5] := (bKept 5 (by decide)).trans (cKept 5 (by decide))
  have pending : Pending second fr b := by
    refine ⟨⟨(keep 13 (by decide)).trans regs.buf, ?_, ?_, ?_⟩, ?_, ?_⟩
    · cases second
      · exact (keep 15 (by decide)).trans regs.slice
      · exact (keep 14 (by decide)).trans regs.slice
    · intro hEq
      exact b5.trans ((dxKept 5 (by decide)).trans ((hxHash hEq).trans (regs.hash hEq)))
    · intro hEq
      exact (keep 15 (by decide)).trans (regs.stop hEq)
    · cases second
      · exact (bKept 12 (by decide)).trans cNext
      · exact (bKept 3 (by decide)).trans cNext
    · cases second
      · exact b5.trans ((dxKept 5 (by decide)).trans hxLeft)
      · exact (bKept 12 (by decide)).trans ((c12 rfl).trans ((dxKept 12 (by decide)).trans hxLeft))
  have w5 : b[5].width = 64 := by
    cases second
    · exact congrArg Value.width pending.length
    · exact congrArg Value.width (pending.hash rfl)
  have w12 : b[12].width = 64 := by
    cases second
    · exact congrArg Value.width pending.next
    · exact congrArg Value.width pending.length
  have widths : ∀ i : Fin Reg.count, i.val ∈ Activation.calleeSavedNumbers → b[i].width = 64 := by
    rintro ⟨i, hi⟩ h
    simp only [Activation.calleeSavedNumbers, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h <;> subst i
    · exact (congrArg Value.width (bKept 3 (by decide))).trans c3Width
    · exact w5
    · exact w12
    all_goals rw [keep _ (by dsimp only; decide)]; exact live.savedWidths _ (by dsimp only; decide)
  let n := memCopy (memStore m (sp fr-8) (fillRet second)) (sp fr + BitVec.ofNat 64 (fillOffset second))
    (fr.rsp + 320) 31
  have atoms : Atom.All Extracted.programImage b n (Fn103f30.frameAt (compressAt second) fr) := by
    have newTail := frameTailAfter (b := b) env tail frame locality
    cases second
    · exact ⟨brsp, (keep 22 (by decide)).trans df, (keep 14 (by decide)).trans live.atoms.2.2.1,
        (keep 39 (by decide)).trans live.atoms.2.2.2.1,
        (keep 50 (by decide)).trans live.atoms.2.2.2.2.1,
        (keep 51 (by decide)).trans live.atoms.2.2.2.2.2.1,
        (show memLoad n (fr.rsp - 0x250) 64 = fr.rdi from by
          rw [show fr.rsp - 0x250 = sp fr + 120 by bv_omega]; exact newSlots.state), newTail⟩
    · exact ⟨brsp, (keep 22 (by decide)).trans df, (keep 39 (by decide)).trans live.atoms.2.2.1,
        (keep 50 (by decide)).trans live.atoms.2.2.2.1,
        (keep 51 (by decide)).trans live.atoms.2.2.2.2.1, newTail⟩
  have newLive := liveAfter env live frame locality atoms widths (by cases second <;> intro heq <;> cases heq)
  have first : Verify.Core.Reaches (loopAt second) a m (testAt second) h m :=
    .single (congrArg (Transfer.next _ []) start)
  have next : Verify.Core.Reaches (testAt second) h m (fillCopyAt second) d m :=
    .single (congrArg (Transfer.next _ []) branch)
  exact ⟨b, n, first.trans (next.trans copyRun), newLive, newSlots, pending, filled⟩

end K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.FullBlock
