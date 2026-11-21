import K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.FullBlock.State
import K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.Copy
import K256.Proofs.Verify.Hash.Compression.Execution
import K256.Proofs.Verify.Hash.Update.State
import K256.Proofs.Verify.LIR.Generated.Values
import K256.Proofs.Verify.LIR.Fn103f30

namespace K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.FullBlock

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  K256.Proofs.Verify.Hash Standards.NIST.SHA2

private def returnPC (second : Bool) : BitVec 64 := if second then 0x104848 else 0x104280

private def counted (fr : Activation) (second : Bool) (m : Ram) :=
  memStore m (context fr second + 160) (2 : BitVec 64)

private def pushed (fr : Activation) (second : Bool) (m : Ram) :=
  memStore (counted fr second m) (sp fr - 8) (returnPC second)

set_option maxRecDepth 1024 in
private theorem callBlock {fr : Activation} {a : Verify.Core.Registers} {m : Ram}
    (second : Bool) (rsp : a[4] = ⟨64, sp fr⟩) (regs : Pending second fr a)
    (wCount : Writable Extracted.programImage m (context fr second + 160) 8)
    (wPush : Writable Extracted.programImage (counted fr second m) (sp fr - 8) 8)
    (count : memLoad m (context fr second + 160) 64 = 1) :
    ∃ b : Verify.Core.Registers, program.runBlock (dialect Extracted.programImage)
      ⟨compressAt second, a, m⟩ =
        .call ⟨.l1218e0, b, pushed fr second m⟩
          (Verify.Core.Lincomb.callResume (tailAt second) (returnPC second)) ∧
      b[4].get 64 = sp fr - 8 ∧ b[7].get 64 = context fr second + 128 ∧
      b[6].get 64 = context fr second + 64 ∧ b[2].get 64 = 1 ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15,22,39,50,51] → b[i] = a[i]) := by
  have rspGet : a[4].get 64 = sp fr := congrArg (Value.get 64) rsp
  have buf : a[13].get 64 = context fr second + 64 := congrArg (Value.get 64) regs.buf
  cases second
  · refine ⟨?b, ?run, ?_⟩
    case run =>
      have countAddr : context fr false + 160 = sp fr + 320 := by
        change (sp fr + 160) + 160 = _
        bv_omega
      simp only [counted, countAddr] at wPush
      rw [countAddr] at wCount count
      have code := fun x hx => Common.fnCode_subset_programImage x (code_l104263 x hx)
      have first : StoreOk Extracted.programImage m (sp fr + 320) 8 0x104263 8 :=
        ParseSignature.storeOk_of_codeRange (off := 0) (len := 8) wCount code (by decide)
      have push := ParseSignature.storeOk_of_codeRange (off := 24) (len := 5) wPush code (by decide)
      simp only [BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at push
      change program.runBlock (dialect Extracted.programImage) ⟨.l104263, a, m⟩ = _
      have tally : memLoad m (sp fr + 320) 64 + 1 = 2 := by rw [count]; rfl
      cfg_eval [rspGet, buf, first, tally, push, tailAt, returnPC, pushed, counted, countAddr]
      refine (ite_eq_left ?_).trans ?_
      · exact push
      · simp only [pushed, counted, countAddr]
        rfl
    refine ⟨rfl, ?_, rfl, rfl, ?_⟩
    · change sp fr + 288 = (sp fr + 160) + 128
      bv_omega
    · intro ⟨i, bound⟩ hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · refine ⟨?bSecond, ?runSecond, ?_⟩
    case runSecond =>
      have countAddr : context fr true + 160 = sp fr + 488 := by
        change (sp fr + 328) + 160 = _
        bv_omega
      simp only [counted, countAddr] at wPush
      rw [countAddr] at wCount count
      have code := fun x hx => Common.fnCode_subset_programImage x (code_l104830 x hx)
      have first : StoreOk Extracted.programImage m (sp fr + 488) 8 0x104830 8 :=
        ParseSignature.storeOk_of_codeRange (off := 0) (len := 8) wCount code (by decide)
      have push := ParseSignature.storeOk_of_codeRange (off := 19) (len := 5) wPush code (by decide)
      simp only [BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at push
      have dst : a[5].get 64 = context fr true + 128 := congrArg (Value.get 64) (regs.hash rfl)
      change program.runBlock (dialect Extracted.programImage) ⟨.l104830, a, m⟩ = _
      have tally : memLoad m (sp fr + 488) 64 + 1 = 2 := by rw [count]; rfl
      cfg_eval [rspGet, buf, dst, first, tally, push, tailAt, returnPC, pushed, counted, countAddr]
      refine (ite_eq_left ?_).trans ?_
      · exact push
      · simp only [pushed, counted, countAddr]
        rfl
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    · intro ⟨i, bound⟩ hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem resumeLive {fr : Activation} {state : State} {input : Input}
    {a b : Verify.Core.Registers} {m n : Ram} {rs : List MemoryRegion}
    (second : Bool) (env : Environment fr input)
    (live : Live (compressAt second) fr a m state) (slots : Slots fr n)
    (frame : RamWriteFrame m n rs) (locality : LocalWrites fr rs)
    (rsp : b[4] = ⟨64, sp fr⟩)
    (kept : ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15,22,39,50,51] → b[i] = a[i]) :
    Live (tailAt second) fr b n state := by
  apply liveAfter env live frame locality _ (fun i hi => ?_) (by cases second <;> intro h <;> cases h)
  · cases second
    · obtain ⟨_,df,slice,mx,ft,fc,_,tail⟩ := live.atoms
      have slot : memLoad n (fr.rsp - 0x250) 64 = fr.rdi := by
        rw [show fr.rsp - 0x250 = sp fr + 120 by bv_omega]
        exact slots.state
      exact ⟨rsp, (kept 22 (by decide)).trans df, (kept 14 (by decide)).trans slice,
        (kept 39 (by decide)).trans mx, (kept 50 (by decide)).trans ft,
        (kept 51 (by decide)).trans fc, slot, frameTailAfter env tail frame locality⟩
    · obtain ⟨_,df,mx,ft,fc,tail⟩ := live.atoms
      exact ⟨rsp, (kept 22 (by decide)).trans df, (kept 39 (by decide)).trans mx,
        (kept 50 (by decide)).trans ft, (kept 51 (by decide)).trans fc,
        frameTailAfter env tail frame locality⟩
  · rw [kept i (by simp only [Activation.calleeSavedNumbers, List.mem_cons,
      List.not_mem_nil, or_false] at hi ⊢; omega)]
    exact live.savedWidths i hi

private theorem resumePending {second : Bool} {fr : Activation}
    {a b : Verify.Core.Registers} (regs : Pending second fr a)
    (kept : ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15,22,39,50,51] → b[i] = a[i]) :
    Pending second fr b := by
  have buf := (kept 13 (by decide)).trans regs.buf
  cases second
  · exact ⟨⟨buf, (kept 15 (by decide)).trans regs.slice,
      (fun h => by cases h), (fun h => by cases h)⟩,
      (kept 12 (by decide)).trans regs.next, (kept 5 (by decide)).trans regs.length⟩
  · exact ⟨⟨buf, (kept 14 (by decide)).trans regs.slice,
      fun h => (kept 5 (by decide)).trans (regs.hash h),
      fun h => (kept 15 (by decide)).trans (regs.stop h)⟩,
      (kept 3 (by decide)).trans regs.next, (kept 12 (by decide)).trans regs.length⟩

theorem compress {fr : Activation} {state : State} {secret reduced : ByteArray}
    {a : Verify.Core.Registers} {m : Ram} (second : Bool) (env : Environment fr (.seeded secret reduced))
    (live : Live (compressAt second) fr a m state) (slots : Slots fr m)
    (regs : Pending second fr a) (ctx : Filled second fr m state secret) :
    ∃ b n, Verify.Core.Reaches (compressAt second) a m (tailAt second) b n ∧
      Live (tailAt second) fr b n state ∧ Slots fr n ∧ Pending second fr b ∧
      Compressed second fr n state secret := by
  let s := sp fr
  let p := context fr second
  let src := p + 64
  let dst := p + 128
  let count := p + 160
  let child := pushed fr second m
  let regions : List MemoryRegion := [⟨(s - 344).toNat,344⟩, ⟨dst.toNat,32⟩, ⟨count.toNat,8⟩]
  have dep := env.depth
  have lim := env.limit
  have base : s.toNat = fr.rsp.toNat - 712 := spNat env
  have bottom : fr.low.toNat = fr.rsp.toNat - 1920 := by
    rw [env.low, BitVec.toNat_sub_of_le (show (1920 : BitVec 64) ≤ fr.rsp from dep)]
    rfl
  have pushN : (s - 8).toNat = s.toNat - 8 :=
    BitVec.toNat_sub_of_le (show (8 : BitVec 64) ≤ s from (by change 8 ≤ s.toNat; omega))
  have spillN : (s - 344).toNat = s.toNat - 344 :=
    BitVec.toNat_sub_of_le (show (344 : BitVec 64) ≤ s from (by change 344 ≤ s.toNat; omega))
  have pn : p.toNat = s.toNat + (if second then 328 else 160) := by
    cases second
    · exact spAddNat env 160 (by decide)
    · exact spAddNat env 328 (by decide)
  have lowOff : 160 ≤ (if second then 328 else 160 : Nat) := by cases second <;> decide
  have highOff : (if second then 328 else 160 : Nat) ≤ 328 := by cases second <;> decide
  have addr (off : BitVec 64) (h : off.toNat ≤ 168) :
      (p + off).toNat = p.toNat + off.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have srcN : src.toNat = p.toNat + 64 := addr 64 (by decide)
  have dstN : dst.toNat = p.toNat + 128 := addr 128 (by decide)
  have countN : count.toNat = p.toNat + 160 := addr 160 (by decide)
  have lowP : s.toNat + 160 ≤ p.toNat := by omega
  have highP : p.toNat ≤ s.toNat + 328 := by omega
  have storeCount : InRegions regions count 8 :=
    ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)),
      Nat.le_refl _, Nat.le_refl _, by omega⟩
  have storePush : InRegions regions (s - 8) 8 :=
    ⟨_, List.mem_cons_self, by change (s-344).toNat ≤ (s-8).toNat; omega,
      by change (s-8).toNat + 8 ≤ (s-344).toNat + 344; omega, by omega⟩
  have countFrame : RamWriteFrame m (counted fr second m) regions :=
    (RamWriteFrame.refl _ _).memStore (2 : BitVec 64) storeCount
  have stage : RamWriteFrame m child regions := countFrame.memStore (returnPC second) storePush
  have writable {q : BitVec 64} {len : Nat}
      (lo : fr.low.toNat ≤ q.toNat) (hi : q.toNat + len ≤ fr.rsp.toNat) :
      Writable Extracted.programImage m q len := stackWritable env live.writes lo hi
  have rsp : a[4] = ⟨64,s⟩ := by
    cases second <;> exact live.atoms.1
  obtain ⟨c, called, crsp, cdst, csrc, cblocks, csaved⟩ :=
    callBlock second rsp regs (writable (q := count) (by omega) (by omega))
      ((writable (q := s - 8) (by omega) (by omega)).of_frame countFrame) ctx.count
  have beforeHash (q : BitVec 64) (n : Nat) (lo : s.toNat ≤ q.toNat) (hi : q.toNat + n ≤ dst.toNat) :
      Outside regions q n := by
    refine ⟨by omega, fun r hr => ?_⟩
    simp only [regions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · right; change (s-344).toNat + 344 ≤ q.toNat; omega
    · left; exact hi
    · left; change q.toNat + n ≤ count.toNat; omega
  have apartOfBefore {q r : BitVec 64} {k l : Nat}
      (hq : q.toNat + k ≤ 2^64) (hr : r.toNat + l ≤ 2^64) (apart : q.toNat + k ≤ r.toNat) :
      RangeApart q k r l := by
    intro i hi j hj eq
    have h := congrArg BitVec.toNat eq
    rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at h
    omega
  have hash : Compression.StateAt child dst (compressBlocks initialHash (padded second state)) := by
    apply Verify.Hash.Update.stateStore
    · exact Verify.Hash.Update.stateStore ctx.hash (2 : BitVec 64)
        (RangeApart.of_offsets (x := p) rfl rfl (by decide))
    · exact apartOfBefore (q := s - 8) (r := dst) (by omega) (by omega) (by omega)
  have size : (blockBytes second state secret).size = 64 := ctx.bytes.1
  have widths (i : Fin Reg.count) (hi : i.val ∈ Activation.calleeSavedNumbers) : c[i].width = 64 := by
    rw [csaved i (by simp only [Activation.calleeSavedNumbers, List.mem_cons,
      List.not_mem_nil, or_false] at hi ⊢; omega)]
    exact live.savedWidths i hi
  have tag : memLoad child (s - 8) 64 = returnPC second :=
    memLoad_memStore_same _ _ _ (by decide) (by decide)
  have contract : Compression.Call c child (s-8) dst src
      (compressBlocks initialHash (padded second state)) (blockBytes second state secret) := by
    refine ⟨crsp, cdst, csrc, by rw [size]; exact cblocks, widths, hash,
      by rw [size]; exact UpdateV.Finalize.bytesAfter stage (beforeHash src 64 (by omega) (by omega)) ctx.bytes,
      by rw [size]; exact ((writable (q := src) (by omega) (by omega)).of_frame stage).readable,
      (writable (q := dst) (by omega) (by omega)).of_frame stage, by omega, ?_,
      ((writable (q := s - 8) (by omega) (by omega)).of_frame stage).readable,
      by rw [tag]; cases second <;> decide, .inr (by omega), .inr (by omega)⟩
    rw [show s - 8 - 336 = s - 344 by bv_omega]
    exact (writable (q := s - 344) (by omega) (by omega)).of_frame stage
  obtain ⟨out, ran, post⟩ := Compression.execute contract
  have returned := Verify.Core.Lincomb.reachesCall called ran (post.tag.trans (congrArg (fun q => some (Value.mk 64 q)) tag))
  have frame : RamWriteFrame m out.store regions := by
    apply stage.trans post.writes
    intro r hr
    simp only [Compression.footprint, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · refine ⟨_, List.mem_cons_self, ?_⟩
      change (s-344).toNat ≤ (s-8).toNat - 336 ∧ (s-8).toNat - 336 + 336 ≤ (s-344).toNat + 344
      omega
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Nat.le_refl _, Nat.le_refl _⟩
  have locality : LocalWrites fr regions := by
    intro r hr
    simp only [regions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change fr.low.toNat ≤ (s-344).toNat ∧ (s-344).toNat + 344 ≤ fr.rsp.toNat - 48
      omega
    · change fr.low.toNat ≤ dst.toNat ∧ dst.toNat + 32 ≤ fr.rsp.toNat - 48
      omega
    · change fr.low.toNat ≤ count.toNat ∧ count.toNat + 8 ≤ fr.rsp.toNat - 48
      omega
  have keepSlot (off : Nat) (h : off ≤ 120) : Outside regions (s + BitVec.ofNat 64 off) 8 := by
    have eq : (s + BitVec.ofNat 64 off).toNat = s.toNat + off := spAddNat env off (by omega)
    exact beforeHash _ _ (by change s.toNat ≤ (s + BitVec.ofNat 64 off).toNat; omega)
      (by change (s + BitVec.ofNat 64 off).toNat + 8 ≤ dst.toNat; omega)
  have remaining := slotsAfter slots frame (keepSlot 8 (by decide)) (keepSlot 112 (by decide)) (keepSlot 120 (by decide))
  have kept (i : Fin Reg.count) (hi : i.val ∈ [3,5,12,13,14,15,22,39,50,51]) :
      out.values[i] = a[i] := (post.preserved i hi).trans (csaved i hi)
  have restored : out.values[4] = ⟨64,s⟩ := by rw [post.rsp, BitVec.sub_add_cancel]
  refine ⟨out.values, out.store, returned, resumeLive second env live remaining frame locality restored kept,
    remaining, resumePending regs kept, UpdateV.Finalize.bytesAfter frame (beforeHash p 64 (by omega) (by omega)) ctx.outer,
    ?_, ?_⟩
  · exact (compressBlocks_single _ _ size) ▸ post.state
  · change memLoad out.store count 64 = 2
    have outside : Outside (Compression.footprint (s-8) dst) count 8 := by
      refine ⟨by omega, fun r hr => ?_⟩
      simp only [Compression.footprint, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · right; change (s-8).toNat - 336 + 336 ≤ count.toNat; omega
      · right; change dst.toNat + 32 ≤ count.toNat; omega
    rw [post.writes.memLoad_eq outside]
    change memLoad (memStore (counted fr second m) (s-8) (returnPC second)) count 64 = 2
    have apart : RangeApart (s-8) 8 count 8 := apartOfBefore (by omega) (by omega) (by omega)
    rw [memLoad_memStore_of_rangeApart _ _ _ _ _ apart]
    exact memLoad_memStore_same _ _ _ (by decide) (by decide)

end K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.FullBlock
