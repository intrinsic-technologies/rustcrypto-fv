import K256.Proofs.Signing.UpdateV.State
import K256.Proofs.Common.Tactic
import K256.Proofs.Verify.LIR.Generated.Values
import K256.Proofs.Verify.Hash.Compression.Execution
import K256.Proofs.ParseSignature.Call

namespace K256.Proofs.Signing.UpdateV

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.RFC Standards.NIST.SHA2 K256.Proofs.Verify.Hash

private def padResume : StackFrame Value Label signature Reg.count :=
  ⟨.l104a94, #v[], rfl, some ⟨64, 0x104a94⟩⟩

private def padWrites (sp : BitVec 64) : List MemoryRegion :=
  [⟨(sp - 344#64).toNat, 344⟩, ⟨(sp + 167#64).toNat, 41⟩]

private theorem padStackNat {sp : BitVec 64} (depth : 344 ≤ sp.toNat) (off : Nat) (h : off ≤ 344) :
    (sp - BitVec.ofNat 64 off).toNat = sp.toNat - off := by
  have lit : (BitVec.ofNat 64 off).toNat = off := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toNat_sub_of_le (show BitVec.ofNat 64 off ≤ sp from by
    change (BitVec.ofNat 64 off).toNat ≤ sp.toNat
    rw [lit]
    omega), lit]

private theorem padAddrNat {sp : BitVec 64} (limit : sp.toNat + 208 < 2^32) (off : Nat) (h : off ≤ 208) :
    (sp + BitVec.ofNat 64 off).toNat = sp.toNat + off := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := off) (by omega),
    Nat.mod_eq_of_lt (by omega)]

private theorem padSlot {sp : BitVec 64} (limit : sp.toNat + 208 < 2^32) {off n : Nat}
    (lo : 167 ≤ off) (hi : off + n ≤ 208) :
    InRegions (padWrites sp) (sp + BitVec.ofNat 64 off) n := by
  refine ⟨_,List.mem_cons_of_mem _ (List.mem_singleton_self _),?_⟩
  change (sp + 167#64).toNat ≤ (sp + BitVec.ofNat 64 off).toNat ∧
    (sp + BitVec.ofNat 64 off).toNat + n ≤ (sp + 167#64).toNat + 41 ∧ _
  rw [padAddrNat limit 167 (by decide), padAddrNat limit off (by omega)]
  omega

private theorem padPush {sp : BitVec 64} (depth : 344 ≤ sp.toNat) (limit : sp.toNat + 208 < 2^32) :
    InRegions (padWrites sp) (sp - 8#64) 8 := by
  refine ⟨_,List.mem_cons_self,?_⟩
  change (sp - 344#64).toNat ≤ (sp - 8#64).toNat ∧ (sp - 8#64).toNat + 8 ≤ (sp - 344#64).toNat + 344 ∧ _
  rw [padStackNat depth 344 (by decide), padStackNat depth 8 (by decide)]
  omega

private def padCallMemory (m : Ram) (sp : BitVec 64) : Ram :=
  memStore (memStore (memStore (memStore (memStore (memStore (memStore m
    (sp + 192#64) (0x5be0cd191f83d9ab : BitVec 64))
    (sp + 184#64) (0x9b05688c510e527f : BitVec 64))
    (sp + 176#64) (0xa54ff53a3c6ef372 : BitVec 64))
    (sp + 168#64) (0xbb67ae856a09e667 : BitVec 64))
    (sp + 167#64) (0 : BitVec 8))
    (sp + 200#64) (1 : BitVec 64))
    (sp - 8#64) (0x104a94 : BitVec 64)

private theorem padCall {a : Values Value Reg.count} {m : Ram} {sp : BitVec 64}
    (rsp : a[4].get 64 = sp)
    (stack : Writable Extracted.programImage m (sp - 8#64) 216) :
    ∃ b : Values Value Reg.count, program.runBlock (dialect Extracted.programImage) ⟨.l104a1e,a,m⟩ =
      .call ⟨.l1218e0,b,padCallMemory m sp⟩ padResume ∧
      b[4].get 64 = sp - 8#64 ∧ b[7].get 64 = sp + 168#64 ∧ b[6].get 64 = sp + 8#64 ∧
      b[2].get 64 = 1 ∧ b[14] = ⟨64, sp + 168#64⟩ ∧
      ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,15,22,39,50,51] → b[i] = a[i] := by
  refine ⟨?b, ?step, ?post⟩
  case step =>
    cfg_eval [rsp]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l104a1e)
    rfl
  case post =>
    refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
    rintro ⟨i,_⟩ hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem padResumeBlock {a : Values Value Reg.count} {m : Ram} {sp : BitVec 64}
    (rsp : a[4].get 64 = sp) (stack : Writable Extracted.programImage m (sp + 167#64) 1) :
    ∃ b : Values Value Reg.count, program.runBlock (dialect Extracted.programImage) ⟨.l104a94,a,m⟩ =
      .jump ⟨.l104ab0,b,memStore m (sp + 167#64) (0 : BitVec 8)⟩ ∧
      b[0] = ⟨64,3⟩ ∧
      ∀ i : Fin Reg.count, i.val ∈ [3,4,5,12,13,14,15,22,39,50,51] → b[i] = a[i] := by
  refine ⟨?b, ?step, ?post⟩
  case step =>
    cfg_eval [rsp]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l104a94)
    rfl
  case post =>
    refine ⟨rfl,?_⟩
    rintro ⟨i,_⟩ hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem padCallWrites (m : Ram) (sp : BitVec 64)
    (depth : 344 ≤ sp.toNat) (limit : sp.toNat + 208 < 2^32) :
    RamWriteFrame m (padCallMemory m sp) (padWrites sp) := by
  unfold padCallMemory
  apply RamWriteFrame.memStore _ _ (padPush depth limit)
  repeat' apply RamWriteFrame.memStore _ _ (padSlot limit (by decide) (by decide))
  exact RamWriteFrame.refl _ _

private theorem padInitialState (m : Ram) (sp : BitVec 64) :
    Compression.StateAt (padCallMemory m sp) (sp + 168#64) initialHash := by
  let child := padCallMemory m sp
  have packed :
      memLoad child (sp + 168#64) 64 = 0xbb67ae856a09e667 ∧
      memLoad child (sp + 176#64) 64 = 0xa54ff53a3c6ef372 ∧
      memLoad child (sp + 184#64) 64 = 0x9b05688c510e527f ∧
      memLoad child (sp + 192#64) 64 = 0x5be0cd191f83d9ab := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp (disch := first | decide | (apply RangeApart.of_offsets rfl rfl; decide))
        only [child, padCallMemory, addr_sub sp (8#64), memLoad_memStore_of_rangeApart, memLoad_memStore_same]
  obtain ⟨h0,h1,h2,h3⟩ := packed
  have words : (Vector.ofFn fun i : Fin 8 => initialHash[i.val]!.toBitVec) = SHA256.«H⁽⁰⁾» := by
    decide +kernel
  refine ⟨by decide +kernel, ?_⟩
  rw [words]
  have half {off : Nat} {v : BitVec 64} (k : Nat) (hk : k ≤ 1)
      (w : memLoad child (sp + BitVec.ofNat 64 off) 64 = v) :
      memLoad child (sp + BitVec.ofNat 64 (off + 4*k)) 32 = v.extractLsb' (32*k) 32 := by
    have read := extractLsb'_memLoad child (sp + BitVec.ofNat 64 off)
      (n := 64) (32*k) 32 (by omega) (by decide) (by omega)
    rw [w, show 32*k/8 = 4*k by omega, BitVec.add_assoc, ← BitVec.ofNat_add] at read
    exact read.symm
  intro i hi
  have addr : wordAddr (sp + 168#64) 32 i = sp + BitVec.ofNat 64 (168 + 4*i) := by
    simp only [wordAddr, Nat.reduceDiv, BitVec.ofNat_add, BitVec.add_assoc]
  rw [addr]
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact half (off := 168) 0 (by decide) h0
  · exact half (off := 168) 1 (by decide) h0
  · exact half (off := 176) 0 (by decide) h1
  · exact half (off := 176) 1 (by decide) h1
  · exact half (off := 184) 0 (by decide) h2
  · exact half (off := 184) 1 (by decide) h2
  · exact half (off := 192) 0 (by decide) h3
  · exact half (off := 192) 1 (by decide) h3

private theorem padBytesAfter {m t : Ram} {sp : BitVec 64} {bytes : ByteArray}
    (h : RamWriteFrame m t (padWrites sp)) (depth : 344 ≤ sp.toNat)
    (limit : sp.toNat + 208 < 2^32)
    (bytesAt : (⟨(sp + 8#64).toNat,64⟩ : MemoryRegion).HasBytes m bytes) :
    (⟨(sp + 8#64).toNat,64⟩ : MemoryRegion).HasBytes t bytes := by
  refine ⟨bytesAt.1, fun i => ?_⟩
  have size : bytes.size = 64 := bytesAt.1
  have hi : i.val < 64 := size ▸ i.isLt
  rw [h.outside]
  · exact bytesAt.2 i
  have addr : (BitVec.ofNat 64 ((sp + 8#64).toNat + i.val)).toNat = sp.toNat + 8 + i.val := by
    rw [padAddrNat limit 8 (by decide), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine ⟨by rw [addr]; omega, fun r hr => ?_⟩
  simp only [padWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl
  · right
    change (sp - 344#64).toNat + 344 ≤ _
    rw [padStackNat depth 344 (by decide), addr]
    omega
  · left
    change _ ≤ (sp + 167#64).toNat
    rw [padAddrNat limit 167 (by decide), addr]
    omega

set_option linter.unusedVariables false in
theorem compressPad {fr : Activation} {a : Values Value Reg.count} {key : ByteArray} {m : Ram}
    (entry : Atom.All Extracted.programImage a m (Fn104970.frameAt .l104a1e fr))
    (writes : RamWriteFrame fr.original m [fr.region])
    (image : ∀ b ∈ Extracted.programImage, fr.original[b.1]? = some b.2)
    (low : fr.low = fr.rsp - 1200) (depth : 1200 ≤ fr.rsp.toNat)
    (limit : fr.rsp.toNat + 8 < 2^32)
    (pad : (⟨(fr.rsp - 488 + 8).toNat, 64⟩ : MemoryRegion).HasBytes m (keyPad key 0x36)) :
    ∃ b t, (program.sem (dialect Extracted.programImage)).Reaches
      ⟨⟨.l104a1e, a, m⟩, []⟩ ⟨⟨.l104ab0, b, t⟩, []⟩ ∧
      Atom.All Extracted.programImage b t (Fn104970.frameAt .l104ab0 fr) ∧
      RamWriteFrame fr.original t [fr.region] ∧
      b[0] = ⟨64, 3⟩ ∧ b[14] = ⟨64, fr.rsp - 488 + 168⟩ ∧
      (⟨(fr.rsp - 488 + 8).toNat, 64⟩ : MemoryRegion).HasBytes t (keyPad key 0x36) ∧
      Compression.StateAt t (fr.rsp - 488 + 168) (compressBlocks initialHash (keyPad key 0x36)) ∧
      memLoad t (fr.rsp - 488 + 167) 8 = 0 ∧ memLoad t (fr.rsp - 488 + 200) 64 = 1 := by
  obtain ⟨rsp, df, rbx, rbp, _, _, _, r12, r13, _, r15, mxcsr, ftw, fcw,
    save3, save12, save13, save14, save15, save5, retRead, retWord, retLow, stack, stackLow,
    align, slot1Read, slot1Word, slot2Read, slot2Word, slotsApart, _⟩ := entry
  let sp := fr.rsp - 488
  let child := padCallMemory m sp
  have spNat : sp.toNat = fr.rsp.toNat - 488 :=
    BitVec.toNat_sub_of_le (show (488 : BitVec 64) ≤ fr.rsp from (by omega : 488 ≤ fr.rsp.toNat))
  have lowNat : fr.low.toNat = fr.rsp.toNat - 1200 := by
    rw [low, BitVec.toNat_sub_of_le (show (1200 : BitVec 64) ≤ fr.rsp from depth)]
    rfl
  have dep : 344 ≤ sp.toNat := by omega
  have room : sp.toNat + 208 < 2^32 := by omega
  have addr (off : Nat) (ho : off ≤ 208) := padAddrNat room off ho
  have down (off : Nat) (ho : off ≤ 344) := padStackNat dep off ho
  have addr8 := addr 8 (by decide)
  have addr167 := addr 167 (by decide)
  have addr168 := addr 168 (by decide)
  have addr200 := addr 200 (by decide)
  have down8 := down 8 (by decide)
  have down344 := down 344 (by decide)
  have writable {u : Ram} (w : RamWriteFrame m u (padWrites sp)) {p : BitVec 64} {n : Nat}
      (lo : fr.low.toNat ≤ p.toNat) (hi : p.toNat + n ≤ fr.rsp.toNat) :
      Writable Extracted.programImage u p n := by
    change Writable Extracted.programImage m (fr.rsp - 1200) 1200 at stack
    apply (stack.of_frame w).sub
    all_goals rw [← low]
    · exact lo
    · omega
  obtain ⟨b, enter, brsp, bdst, bsrc, bcount, bctx, saved⟩ := padCall (sp := sp)
    (congrArg (Value.get 64) rsp) (writable (.refl _ _) (by omega) (by omega))
  have stage : RamWriteFrame m child (padWrites sp) := padCallWrites m sp dep room
  have ret : memLoad child (sp - 8#64) 64 = 0x104a94 :=
    memLoad_memStore_same _ _ _ (by decide) (by decide)
  have childLow : 336 ≤ (sp - 8#64).toNat := by omega
  have childSp : sp - 8#64 - 336#64 = sp - 344#64 := by bv_omega
  have size := keyPad_size key 0x36
  have contract : Compression.Call b child (sp - 8#64) (sp + 168#64) (sp + 8#64)
      initialHash (keyPad key 0x36) := by
    refine ⟨brsp, bdst, bsrc, by rw [size]; exact bcount, ?_, padInitialState m sp,
      by rw [size]; exact padBytesAfter stage dep room pad, ?_, ?_, childLow, ?_, ?_, ?_,
      Or.inr (by omega), Or.inr (by omega)⟩
    · rintro ⟨i,_⟩ hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
      · exact congrArg Value.width ((saved 3 (by decide)).trans rbx)
      · exact congrArg Value.width ((saved 5 (by decide)).trans rbp)
      · exact congrArg Value.width ((saved 12 (by decide)).trans r12)
      · exact congrArg Value.width ((saved 13 (by decide)).trans r13)
      · exact congrArg Value.width bctx
      · exact congrArg Value.width ((saved 15 (by decide)).trans r15)
    · rw [size]
      exact (writable stage (by omega) (by omega)).readable
    · exact writable stage (by omega) (by omega)
    · change Writable Extracted.programImage child (sp - 8#64 - 336#64) 336
      rw [childSp]
      exact writable stage (by omega) (by omega)
    · exact (writable stage (by omega) (by omega)).readable
    · rw [ret]; decide
  obtain ⟨out, exec, post⟩ := Compression.execute contract
  have back := ParseSignature.exec_reaches_resume exec padResume [] (by rw [post.tag, ret]; rfl)
  have bounds {r : MemoryRegion} (hr : r ∈ padWrites sp) :
      fr.low.toNat ≤ r.start ∧ r.start + r.size ≤ fr.rsp.toNat := by
    simp only [padWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · change fr.low.toNat ≤ (sp - 344#64).toNat ∧ (sp - 344#64).toNat + 344 ≤ _
      omega
    · change fr.low.toNat ≤ (sp + 167#64).toNat ∧ (sp + 167#64).toNat + 41 ≤ _
      omega
  have within : RegionsWithin (padWrites sp) [fr.region] := by
    intro r hr
    obtain ⟨l,h⟩ := bounds hr
    refine ⟨_, List.mem_cons_self, l, ?_⟩
    change _ ≤ fr.low.toNat + (fr.rsp.toNat - fr.low.toNat)
    omega
  have compressed := stage.trans post.writes (by
    intro r hr
    simp only [Compression.footprint,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · refine ⟨_,List.mem_cons_self,?_⟩
      change (sp - 344#64).toNat ≤ (sp - 8#64).toNat - 336 ∧
        (sp - 8#64).toNat - 336 + 336 ≤ (sp - 344#64).toNat + 344
      omega
    · refine ⟨_,List.mem_cons_of_mem _ (List.mem_singleton_self _),?_⟩
      change (sp + 167#64).toNat ≤ (sp + 168#64).toNat ∧
        (sp + 168#64).toNat + 32 ≤ (sp + 167#64).toNat + 41
      omega)
  have restored : out.values[4] = ⟨64,sp⟩ := by
    rw [post.rsp]; congr 1; bv_omega
  obtain ⟨c, finish, index, kept⟩ := padResumeBlock (sp := sp) (congrArg (Value.get 64) restored)
    (writable compressed (by omega) (by omega))
  have keep (i : Fin Reg.count) (hi : i.val ∈ [3,5,12,13,15,22,39,50,51]) :
      c[i] = a[i] := (kept i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega)).trans
      ((post.preserved i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega)).trans
        (saved i hi))
  have finalWrites := compressed.memStore (0 : BitVec 8) (padSlot room (off := 167) (n := 1)
    (by decide) (by decide))
  have keepMem {p : BitVec 64} (apart : p.toNat + 8 ≤ sp.toNat - 344 ∨
      sp.toNat + 208 ≤ p.toNat) (lo : p.toNat + 8 ≤ 2^64) :
      memLoad (memStore out.store (sp + 167#64) (0 : BitVec 8)) p 64 = memLoad m p 64 := by
    apply finalWrites.memLoad_eq
    refine ⟨lo,fun r hr => ?_⟩
    simp only [padWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · change _ ≤ (sp - 344#64).toNat ∨ (sp - 344#64).toNat + 344 ≤ _
      omega
    · change _ ≤ (sp + 167#64).toNat ∨ (sp + 167#64).toNat + 41 ≤ _
      omega
  have savedWord (off : Nat) (hi : off ≤ 48) :
      memLoad (memStore out.store (sp + 167#64) (0 : BitVec 8))
        (fr.rsp - BitVec.ofNat 64 off) 64 = memLoad m (fr.rsp - BitVec.ofNat 64 off) 64 := by
    have offset : (fr.rsp - BitVec.ofNat 64 off).toNat = fr.rsp.toNat - off :=
      padStackNat (sp := fr.rsp) (by omega) off (by omega)
    exact keepMem (Or.inr (by omega)) (by omega)
  have slotApart : 0x2042c8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203dd0 := slotsApart
  have slot1 : memLoad (memStore out.store (sp + 167#64) (0 : BitVec 8)) 0x203dd0 64 =
      memLoad m 0x203dd0 64 :=
    keepMem (by change 0x203dd0 + 8 ≤ _ ∨ _ ≤ 0x203dd0; omega) (by decide)
  have slot2 : memLoad (memStore out.store (sp + 167#64) (0 : BitVec 8)) 0x203e10 64 =
      memLoad m 0x203e10 64 :=
    keepMem (by change 0x203e10 + 8 ≤ _ ∨ _ ≤ 0x203e10; omega) (by decide)
  refine ⟨c,_,.step (congrArg (Transfer.next _ []) enter)
    (back.trans (.step (congrArg (Transfer.next _ []) finish) (.refl _))), ?_,
    writes.trans finalWrites within, index,
    (kept 14 (by decide)).trans ((post.preserved 14 (by decide)).trans bctx),
    padBytesAfter finalWrites dep room pad, ?_, memLoad_memStore_same _ _ _ (by decide) (by decide), ?_⟩
  · exact ⟨(kept 4 (by decide)).trans restored, (keep 22 (by decide)).trans df,
      (keep 3 (by decide)).trans rbx, (keep 5 (by decide)).trans rbp, (keep 12 (by decide)).trans r12,
      (keep 13 (by decide)).trans r13, (keep 15 (by decide)).trans r15, (keep 39 (by decide)).trans mxcsr,
      (keep 50 (by decide)).trans ftw, (keep 51 (by decide)).trans fcw,
      (savedWord 48 (by decide)).trans save3, (savedWord 40 (by decide)).trans save12,
      (savedWord 32 (by decide)).trans save13, (savedWord 24 (by decide)).trans save14,
      (savedWord 16 (by decide)).trans save15, (savedWord 8 (by decide)).trans save5,
      retRead.of_frame finalWrites, (keepMem (Or.inr (by omega)) (by omega)).trans retWord,
      retLow, stack.of_frame finalWrites, stackLow, align, slot1Read.of_frame finalWrites,
      slot1.trans slot1Word, slot2Read.of_frame finalWrites, slot2.trans slot2Word, slotsApart, trivial⟩
  · exact ⟨post.state.1, post.state.2.write_apart _ _ (RangeApart.of_offsets rfl rfl (by decide))⟩
  · change memLoad (memStore out.store (sp + 167#64) (0 : BitVec 8)) (sp + 200#64) 64 = _
    rw [memLoad_memStore_of_rangeApart _ _ _ _ _ (RangeApart.of_offsets rfl rfl (by decide)),
      post.writes.memLoad_eq]
    · simp (disch := first | decide | (apply RangeApart.of_offsets rfl rfl; decide))
        only [child, padCallMemory, addr_sub sp (8#64), memLoad_memStore_of_rangeApart, memLoad_memStore_same]
    · refine ⟨by omega, fun r hr => ?_⟩
      simp only [Compression.footprint,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · right
        change (sp - 8#64).toNat - 336 + 336 ≤ (sp + 200#64).toNat
        omega
      · right
        change (sp + 168#64).toNat + 32 ≤ (sp + 200#64).toNat
        omega

end K256.Proofs.Signing.UpdateV
