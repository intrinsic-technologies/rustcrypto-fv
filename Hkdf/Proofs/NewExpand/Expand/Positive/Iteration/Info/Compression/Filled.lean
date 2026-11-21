import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Info.Compression.Frame
import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Info.Compression.Control
import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Info.Compression.Copy
import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Info.Compression.Input
import Hkdf.Proofs.Common.Streaming

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Expand.Info

open Hkdf.Spec.Program Hkdf.Proofs.Program Hkdf.Proofs.Common
open Hkdf.Proofs.Common.CallFrame Hkdf.Proofs.Common.Machine Hkdf.Proofs.Common.SHA256
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

private theorem bytesOfAgreement {s t : RamState} {p : BitVec 64} {n : Nat} {b : ByteArray}
    (bytes : (⟨p.toNat, n⟩ : MemoryRegion).HasBytes s.external b)
    (agree : (Component.mem p n).Agrees s t) :
    (⟨p.toNat, n⟩ : MemoryRegion).HasBytes t.external b := by
  refine ⟨bytes.1, fun i => ?_⟩
  have size : b.size = n := bytes.1
  have hi := i.isLt
  simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
    (agree i.val (by omega)).trans (by
      simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using bytes.2 i)

private theorem filledBuffer {s t : RamState} {p : BitVec 64} {message part : ByteArray}
    (old : StreamAt s p message)
    (size : part.size = 64 - message.size % 64)
    (front : (Component.mem p (message.size % 64)).Agrees s t)
    (back : (⟨(p + BitVec.ofNat 64 (message.size % 64)).toNat, part.size⟩ :
      MemoryRegion).HasBytes t.external part) :
    (⟨p.toNat, 64⟩ : MemoryRegion).HasBytes t.external (remainderBytes message ++ part) := by
  let tail := remainderBytes message
  have len : tail.size = message.size % 64 := remainderBytes_size _
  have sum : tail.size + part.size = 64 := by omega
  have leftBytes := bytesOfAgreement old.tail front
  change (⟨p.toNat, message.size % 64⟩ : MemoryRegion).HasBytes t.external tail at leftBytes
  rw [← len] at back
  refine ⟨by change (tail ++ part).size = 64; rwa [ByteArray.size_append], fun i => ?_⟩
  change t.external[BitVec.ofNat 64 (p.toNat + i.val)]? = some ((tail ++ part)[i.val])
  by_cases hi : i.val < tail.size
  · simpa only [ByteArray.getElem_append_left hi] using leftBytes.2 ⟨i.val, hi⟩
  · have bound : i.val < tail.size + part.size := by simpa only [ByteArray.size_append] using i.isLt
    have byte := back.2 ⟨i.val - tail.size, by omega⟩
    change t.external[BitVec.ofNat 64 ((p + BitVec.ofNat 64 tail.size).toNat + (i.val - tail.size))]? = _ at byte
    rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_assoc,
      ← BitVec.ofNat_add, Nat.add_sub_of_le (by omega : tail.size ≤ i.val)] at byte
    simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      ByteArray.getElem_append_right (by omega : tail.size ≤ i.val)] using byte

private theorem filledHmac {s t : RamState} {p : BitVec 64} {key previous part : ByteArray}
    (old : HmacAt s p key previous)
    (size : part.size = 64 - previous.size % 64)
    (hash : let m := HMAC.xorPad (HMAC.keyBlock key) 0x36 ++ previous
      HashStateAt t (p + 64)
        (compressBlocks (compressBlocks Hkdf.Proofs.NIST.SHA256.initialHash m) (remainderBytes m ++ part)))
    (index : t.external[p + 63]? = some 0)
    (count : let m := HMAC.xorPad (HMAC.keyBlock key) 0x36 ++ previous
      loadBytes t.external (p + 96) 8 = .ok (BitVec.ofNat 64 (m.size / 64) + 1))
    (outer : (Component.mem (p + 104) 32).Agrees s t)
    (outerCount : (Component.mem (p + 136) 8).Agrees s t) :
    HmacAt t p key (previous ++ part) := by
  let m := HMAC.xorPad (HMAC.keyBlock key) 0x36 ++ previous
  have mSize : m.size = 64 + previous.size := by simp [m, HMAC.xorPad_keyBlock_size]
  have align : (m ++ part).size % 64 = 0 := by rw [ByteArray.size_append, mSize, size]; omega
  have inc : (m ++ part).size / 64 = m.size / 64 + 1 := by
    rw [ByteArray.size_append, mSize, size]; omega
  refine ⟨?_, hashState_of_bytes old.outerHash outer, (agrees_loadBytes outerCount).trans old.outerBlocks⟩
  rw [← ByteArray.append_assoc]
  change StreamAt t p (m ++ part)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rwa [compressBlocks_append_buffered]
  · have e : 64 * ((m ++ part).size / 64) = (m ++ part).size := by omega
    have vac : (⟨p.toNat, 0⟩ : MemoryRegion).HasBytes t.external ByteArray.empty :=
      ⟨rfl, fun i => Fin.elim0 i⟩
    simpa only [align, e, ByteArray.extract_same] using vac
  · simpa only [align, show UInt8.ofNat 0 = (0 : UInt8) by decide +kernel] using index
  · simpa only [inc, BitVec.ofNat_add, BitVec.ofNat_eq_ofNat] using count

private theorem copyPrefix [Bindings] {entry s : RamState} {boundary : ReturnBoundary}
    {key info : ByteArray} {ptr : BitVec 64} {length idx : Nat}
    (pre : ExpandPre entry boundary key info ptr length) (pos : 0 < length) (limit : length ≤ 8160)
    (saved : SavedFrame entry s boundary length) (pc : s.RIP = 0x10f74b)
    (src : s.regValue .rbx = ptr) (index : s.regValue .r14 = BitVec.ofNat 64 idx)
    (bound : idx < 64) (roomArg : s.regValue .rdx = BitVec.ofNat 64 (64 - idx))
    (fits : 64 - idx ≤ info.size) (copyPtr : s.regValue .r12 = 0x10dd60) :
    ∃ t, SavedFrame entry t boundary length ∧ (∃ fuel, Advances boundary fuel s t) ∧
      t.RIP = 0x10f760 ∧ t.regValue .rbp = ptr + BitVec.ofNat 64 (64 - idx) ∧
      t.regValue .r12 = s.regValue .r12 ∧ t.regValue .r13 = s.regValue .r13 ∧
      t.regValue .r15 = s.regValue .r15 ∧
      MemoryWriteFrame s t (localRegions (stackPtr s) (272 + idx) (64 - idx) 8) ∧
      (⟨(stackPtr s + 272 + BitVec.ofNat 64 idx).toNat, 64 - idx⟩ : MemoryRegion).HasBytes
        t.external (info.extract 0 (64 - idx)) := by
  obtain ⟨na, a, ha, ready, eff⟩ := fillArguments (supportedMachine_readyToStep saved.machine)
    saved.loaded pre.call.outerBoundary pc
  have ag : AgreesExcept [.reg 5, .reg 7, .reg 6, .flags, .rip] s a := eff.agrees
  have noMem {n : Nat} (regions : Vector MemoryRegion n) :
      WritesWithin [.reg 5, .reg 7, .reg 6, .flags, .rip] regions := by
    intro c hc x hx
    simp at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl <;> exact hx.elim
  have sa := savedOfLocal pre pos limit saved ha ready ag (noMem _) (by simp)
  have spa : stackPtr a = stackPtr s := sa.sp.trans saved.sp.symm
  have bp : a.regValue .rbp = ptr + BitVec.ofNat 64 (64 - idx) := by
    simpa only [src, roomArg] using (show a.regValue .rbp = s.regValue .rbx + s.regValue .rdx from eff.writes.1)
  have dest : a.regValue .rdi = stackPtr a + BitVec.ofNat 64 (272 + idx) := by
    rw [spa, BitVec.ofNat_add]
    have h : a.regValue .rdi = stackPtr s + s.regValue .r14 + 272 := eff.writes.2.1
    rw [h, index]; bv_omega
  have source : a.regValue .rsi = ptr := eff.writes.2.2.trans src
  obtain ⟨bounded, _, apart, bytes⟩ := inputSlice pre pos limit sa (offset := 0) (count := 64 - idx)
    (by simpa using source) (by simpa using fits)
  obtain ⟨t, st, ⟨nb, hb⟩, rip, abi, frame, copied⟩ := copyCall pre sa true eff.rip
    ((ag.read (r := 12) (n := 64) (by simp)).trans copyPtr) dest
    ((ag.read (r := 2) (n := 64) (by simp)).trans roomArg) (by omega) (by omega)
    bounded apart bytes
  refine ⟨t, st, ⟨_, ha.trans hb⟩, rip, (abi.1 .rbp (by simp)).trans bp,
    (abi.1 .r12 (by simp)).trans (ag.read (r := 12) (n := 64) (by simp)),
    (abi.1 .r13 (by simp)).trans (ag.read (r := 13) (n := 64) (by simp)),
    (abi.1 .r15 (by simp)).trans (ag.read (r := 15) (n := 64) (by simp)),
    memoryWriteFrame_trans (ag.memoryWriteFrame (noMem _)) ?_, ?_⟩
  · simpa only [spa] using copyLocalFrame (workBounds pre.call.stack sa) dest frame
  · simpa only [registerRegion, dest, spa, BitVec.ofNat_add, BitVec.ofNat_eq_ofNat,
      BitVec.add_assoc, Nat.zero_add] using copied

set_option maxRecDepth 2048 in
theorem fillInfoBlock [Bindings] {entry s : RamState} {boundary : ReturnBoundary}
    {key info previous : ByteArray} {ptr : BitVec 64} {length : Nat}
    (pre : ExpandPre entry boundary key info ptr length) (pos : 0 < length) (limit : length ≤ 8160)
    (saved : SavedFrame entry s boundary length) (pc : s.RIP = 0x10f74b)
    (input : HmacAt s (stackPtr s + 272) key previous) (src : s.regValue .rbx = ptr)
    (index : s.regValue .r14 = BitVec.ofNat 64 (previous.size % 64))
    (roomArg : s.regValue .rdx = BitVec.ofNat 64 (64 - previous.size % 64))
    (leftArg : s.regValue .r15 = BitVec.ofNat 64 (info.size - (64 - previous.size % 64)))
    (fits : 64 - previous.size % 64 ≤ info.size) (copyPtr : s.regValue .r12 = 0x10dd60) :
    let room := 64 - previous.size % 64
    let remaining := info.size - room
    ∃ t, SavedFrame entry t boundary length ∧ (∃ fuel, Advances boundary fuel s t) ∧
      t.RIP = (if remaining / 64 = 0 then 0x10f7ae else 0x10f796) ∧
      HmacAt t (stackPtr t + 272) key (previous ++ info.extract 0 room) ∧
      t.regValue .rbx = ptr + BitVec.ofNat 64 room ∧ t.regValue .r15 = BitVec.ofNat 64 remaining ∧
      t.regValue .rdx = BitVec.ofNat 64 (remaining / 64) ∧
      t.regValue .r12 = s.regValue .r12 ∧ t.regValue .r13 = s.regValue .r13 ∧
      MemoryWriteFrame s t (longRegions s) := by
  intro room remaining
  let idx := previous.size % 64
  let part := info.extract 0 room
  let m := HMAC.xorPad (HMAC.keyBlock key) 0x36 ++ previous
  let block := remainderBytes m ++ part
  have im : idx < 64 := Nat.mod_lt _ (by decide)
  have sum : idx + room = 64 := by change idx + (64 - idx) = 64; omega
  have size : part.size = room := by dsimp only [part]; rw [ByteArray.size_extract]; omega
  have mm : m.size % 64 = idx := by
    simp only [m, idx, ByteArray.size_append, HMAC.xorPad_keyBlock_size]; omega
  have bounds := workBounds pre.call.stack saved
  obtain ⟨b, sb, ⟨nb, hb⟩, pcb, bp, r12b, r13b, r15b, fb, copied⟩ := copyPrefix pre pos limit
    saved pc src index im roomArg fits copyPtr
  change MemoryWriteFrame s b (localRegions (stackPtr s) (272 + idx) room 8) at fb
  have spb : stackPtr b = stackPtr s := sb.sp.trans saved.sp.symm
  have keepB (k n : Nat) (fit : k + n ≤ 544) (apart : k + n ≤ 272 + idx ∨ 336 ≤ k) :=
    localAgrees bounds fb (keep := k) (size := n) (by omega) (by decide) fit (by omega)
  have bytesB : (⟨(stackPtr s + 272).toNat, 64⟩ : MemoryRegion).HasBytes b.external block := by
    apply filledBuffer input.inner
    · change part.size = 64 - m.size % 64
      rw [mm, size]
    · change (Component.mem (stackPtr s + 272) (m.size % 64)).Agrees s b
      rw [mm]
      exact keepB 272 idx (by omega) (.inl (by omega))
    · change (⟨(stackPtr s + 272 + BitVec.ofNat 64 (m.size % 64)).toNat, part.size⟩ :
        MemoryRegion).HasBytes b.external part
      rw [mm, size]
      exact copied
  have addrB : rspOf b + 368 = stackPtr entry - 168 := by
    change stackPtr b + 368 = _
    rw [show stackPtr b = stackPtr entry - 536 from sb.sp]; bv_omega
  have writableB : MemWritable b (rspOf b + 368) 8 := by
    rw [addrB]
    exact stack_writable8 pre.call.stack pre.call.stackAvoid sb.allocated (by decide) (by decide)
  obtain ⟨nc, c, hc, rc, ec⟩ := filledArguments (supportedMachine_readyToStep sb.machine)
    sb.loaded pre.call.outerBoundary pcb writableB (by
      rw [addrB]
      exact stack_codeApart pre.call.stack (fun a ha hp => pre.call.stackAvoid a ha (.inl hp))
        (offset := 168) (codeOffset := 0xf760) (by decide) (by decide) (by decide))
  have ac : AgreesExcept [.mem (stackPtr b + 368) 8, .reg 2, .reg 7, .reg 6, .flags, .rip] b c := by
    simpa [filledEffect, x86_compose, stackPtr] using ec.agrees
  obtain ⟨sc, fc⟩ := savedOfStore pre pos limit sb hc rc ac (off := 368) (n := 8)
    (by decide) (by decide) (by
      intro comp member addr cover
      simp at member
      rcases member with rfl|rfl|rfl|rfl|rfl|rfl <;> first | exact cover | exact cover.elim) (by simp)
  rw [spb] at fc
  have spc : stackPtr c = stackPtr s := sc.sp.trans saved.sp.symm
  have keepC (k n : Nat) (fit : k + n ≤ 544) (apart : k + n ≤ 368 ∨ 376 ≤ k) :=
    localAgrees bounds fc (keep := k) (size := n) (by decide) (by decide) fit apart
  have oldCount : loadBytes s.external (stackPtr s + 368) 8 = .ok (BitVec.ofNat 64 (m.size / 64)) := by
    simpa only [BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using input.inner.blocks
  have oldHash : HashStateAt s (stackPtr s + 336)
      (compressBlocks Hkdf.Proofs.NIST.SHA256.initialHash m) := by
    simpa only [BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using input.inner.hashWords
  have cntB := (agrees_loadBytes (keepB 368 8 (by decide) (.inr (by decide)))).trans oldCount
  have cntC : loadBytes c.external (stackPtr s + 368) 8 = .ok (BitVec.ofNat 64 (m.size / 64) + 1) := by
    have byte := Bytes.of_memLoad (n := 64) (a := stackPtr b + 368)
      (fun i hi => ac.grow _ (writableB.mem i hi))
    have written : memLoad c.external (stackPtr b + 368) 64 = memLoad b.external (stackPtr b + 368) 64 + 1 :=
      ec.writes.1
    have read : memLoad b.external (stackPtr s + 368) 64 = BitVec.ofNat 64 (m.size / 64) := Memory.memLoad_of_loadBytes64 cntB
    rw [written, spb, read] at byte
    exact byte.loadBytes64
  have hashC := hashState_of_bytes (hashState_of_bytes oldHash (keepB 336 32 (by decide) (.inr (by decide))))
    (keepC 336 32 (by decide) (.inl (by decide)))
  have srcC : c.regValue .rsi = stackPtr s + 272 := by
    rw [← spb]; exact ec.writes.2.2.2
  obtain ⟨d, sd, ⟨nd, hd⟩, pcd, abi, fd, hashD⟩ := compressionCall pre sc true ec.rip
    (by rw [spc, ← spb]; exact ec.writes.2.2.1) (count := 1) ec.writes.2.1
    (by rwa [spc]) (input := block) (by
      simpa only [registerRegion, srcC] using bytesOfAgreement bytesB (keepC 272 64 (by decide) (.inl (by decide))))
    (.inl ⟨by rwa [spc], rfl⟩)
  change MemoryWriteFrame c d (localRegions (stackPtr c) 336 32 344) at fd
  rw [spc] at hashD fd
  have spd : stackPtr d = stackPtr s := sd.sp.trans saved.sp.symm
  have addrD : rspOf d + 335 = stackPtr entry - 201 := by
    change stackPtr d + 335 = _
    rw [show stackPtr d = stackPtr entry - 536 from sd.sp]; bv_omega
  have writableD : MemWritable d (rspOf d + 335) 1 := by
    rw [addrD]; exact stack_writable1 pre.call.stack pre.call.stackAvoid sd.allocated (by decide)
  obtain ⟨nt, t, ht, rt, et⟩ := bufferedDispatch (supportedMachine_readyToStep sd.machine)
    sd.loaded pre.call.outerBoundary pcd writableD (by
      rw [addrD]
      exact stack_codeApart pre.call.stack (fun a ha hp => pre.call.stackAvoid a ha (.inl hp))
        (offset := 201) (codeOffset := 0xf782) (by decide) (by decide) (by decide))
  have at' : AgreesExcept [.mem (stackPtr d + 335) 1, .reg 3, .reg 2, .flags, .rip] d t := by
    simpa [bufferedEffect, x86_compose, stackPtr] using et.agrees
  obtain ⟨st, ft⟩ := savedOfStore pre pos limit sd ht rt at' (off := 335) (n := 1)
    (by decide) (by decide) (by
      intro comp member addr cover
      simp at member
      rcases member with rfl|rfl|rfl|rfl|rfl <;> first | exact cover | exact cover.elim) (by simp)
  rw [spd] at ft
  have spt : stackPtr t = stackPtr s := st.sp.trans saved.sp.symm
  have keepT (k n : Nat) (fit : k + n ≤ 544) (apart : k + n ≤ 335 ∨ 336 ≤ k) :=
    localAgrees bounds ft (keep := k) (size := n) (by decide) (by decide) fit apart
  have fr : MemoryWriteFrame s t (longRegions s) :=
    memoryWriteFrame_trans (memoryWriteFrame_trans (memoryWriteFrame_trans
      (widenLocal bounds fb (by omega) (by omega) (by decide) (by decide) (by decide))
      (widenLocal bounds fc (by decide) (by decide) (by decide) (by decide) (by decide)))
      (widenLocal bounds fd (by decide) (by decide) (by decide) (by decide) (by decide)))
      (widenLocal bounds ft (by decide) (by decide) (by decide) (by decide) (by decide))
  have countT := (agrees_loadBytes (keepT 368 8 (by decide) (.inr (by decide)))).trans
    ((agrees_loadBytes (localAgrees bounds fd (keep := 368) (size := 8) (by decide) (by decide)
      (by decide) (.inr (by decide)))).trans cntC)
  have hashT := hashState_of_bytes hashD (keepT 336 32 (by decide) (.inr (by decide)))
  have zeroT : t.external[stackPtr s + 335]? = some 0 := by
    have byte := Bytes.of_memLoad (n := 8) (a := stackPtr d + 335)
      (fun i hi => at'.grow _ (writableD.mem i hi))
    have stored : memLoad t.external (stackPtr d + 335) 8 = 0 := et.writes.1
    rw [stored, spd] at byte
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero,
      show storedByte (0#8) 0 = (0 : UInt8) by decide +kernel] using byte 0 (by decide)
  have r15d : d.regValue .r15 = BitVec.ofNat 64 remaining :=
    (abi.1 .r15 (by simp)).trans ((ac.read (r := 15) (n := 64) (by simp)).trans (r15b.trans leftArg))
  have remBound : remaining < 2^64 := Nat.lt_of_le_of_lt (Nat.sub_le _ _) pre.lengthFits
  have r15nat : (d.regValue .r15).toNat = remaining := by
    rw [r15d, BitVec.toNat_ofNat, Nat.mod_eq_of_lt remBound]
  refine ⟨t, st, ⟨_, ((hb.trans hc).trans hd).trans ht⟩, ?_, ?_, ?_,
    (at'.read (r := 15) (n := 64) (by simp)).trans r15d, ?_,
    (at'.read (r := 12) (n := 64) (by simp)).trans
      ((abi.1 .r12 (by simp)).trans ((ac.read (r := 12) (n := 64) (by simp)).trans r12b)),
    (at'.read (r := 13) (n := 64) (by simp)).trans
      ((abi.1 .r13 (by simp)).trans ((ac.read (r := 13) (n := 64) (by simp)).trans r13b)), fr⟩
  · have h : t.RIP = (if (d.regValue .r15).toNat < 64 then 0x10f7ae else 0x10f796) := et.rip
    simpa only [r15nat, show remaining < 64 ↔ remaining / 64 = 0 by omega] using h
  · rw [spt]
    apply filledHmac (part := part) input size <;>
      simp only [BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd]
    · exact hashT
    · exact zeroT
    · exact countT
    · exact localAgrees bounds fr (keep := 376) (size := 32) (by decide) (by decide) (by decide) (.inr (by decide))
    · exact localAgrees bounds fr (keep := 408) (size := 8) (by decide) (by decide) (by decide) (.inr (by decide))
  · exact et.writes.2.1.trans ((abi.1 .rbp (by simp)).trans
      ((ac.read (r := 5) (n := 64) (by simp)).trans bp))
  · have dx : t.regValue .rdx = d.regValue .r15 >>> 6 := et.writes.2.2
    apply BitVec.eq_of_toNat_eq
    rw [dx, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, r15nat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : remaining / 64 < 2^64)]

end Hkdf.Proofs.NewExpand.Expand.Info
