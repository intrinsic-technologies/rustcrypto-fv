import K256.Proofs.Sec1.Parser.Packing.CopyInput
import K256.Proofs.ParseSignature.Contract
import K256.Proofs.Sec1.Parser.Packing.ZeroFill

namespace K256.Proofs.Verify.Transfer.PublicKey

open K256.Proofs.Sec1.Parser.Packing

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Spec.Program
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Sec1.LIR
open K256.Proofs.ParseSignature (buffer)


private theorem callOfGuard {c : Prop} [Decidable c] {t : Transfer Value Ram Label signature Reg.count}
    {l f} (h : (if c then t else .stuck) = .call l f) : t = .call l f := by
  split at h <;> simp_all

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
private theorem affineCallPreserves {a b : Values Value Reg.count} {m n : Ram}
    (h : program.runBlock (dialect Extracted.programImage) ⟨.l10641d, a, m⟩ =
      .call ⟨.l121480, b, n⟩ affineResume) :
    b[8] = a[8] ∧ b[9] = a[9] := by
  cfg_eval at h
  repeat' replace h := callOfGuard h
  obtain ⟨_, rfl, _⟩ := Location.mk.inj (Transfer.call.inj h).1
  exact ⟨rfl, rfl⟩

private theorem memcpyR8 {a : Values Value Reg.count} {m : Ram} {out : Output Value Ram Reg.count}
    (run : program.Exec (dialect Extracted.programImage) ⟨⟨.l12a820, a, m⟩, []⟩ out) :
    out.values[8].width = 64 := by
  cases run with
  | done h =>
    change (program.runBlock _ ⟨.l12a820,a,m⟩).next _ [] = .done out at h
    cfg_eval [b_l12a820] at h
    repeat' (split at h)
    all_goals simp only [Transfer.next, Outcome.done.injEq, reduceCtorEq] at h
    all_goals subst out; rfl
  | next h _ =>
    change (program.runBlock _ ⟨.l12a820,a,m⟩).next _ [] = .next _ at h
    cfg_eval [b_l12a820] at h
    repeat' (split at h)
    all_goals simp only [Transfer.next, reduceCtorEq] at h

private theorem copyFrame {sp src : BitVec 64} {mem : Ram} {n : Nat}
    (win : Writable Extracted.programImage mem (sp - 8) 233) (hn : n ≤ 65) :
    let pushed := memStore mem (sp - 8) (0x10641d : BitVec 64)
    let copied := memCopy pushed (sp + 160) src n
    RamWriteFrame mem (affineMemory sp copied) [packingWindow sp] := by
  dsimp only
  let slot := sp - 8
  have hs : slot.toNat + 8 = sp.toNat := by
    have eq : slot + 8 = sp := BitVec.sub_add_cancel ..
    have low := win.readable.low
    change slot.toNat + 233 ≤ 2^32 at low
    have := congrArg BitVec.toNat eq
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by change slot.toNat + 8 < 2^64; omega)] at this
    exact this
  have low := win.readable.low
  change slot.toNat + 233 ≤ 2^32 at low
  have hd : (sp + 160).toNat = sp.toNat + 160 := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by change sp.toNat + 160 < 2^64; omega)]
    rfl
  have inside : InRegions [packingWindow sp] (sp - 8) (64 / 8) :=
    ⟨_, List.mem_singleton_self _, Nat.le_refl _, by change slot.toNat + 8 ≤ slot.toNat + 233; omega,
      by change slot.toNat + 8 ≤ 2^64; omega⟩
  have dstIn : InRegions [packingWindow sp] (sp + 160) ((8 * n) / 8) := by
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    change slot.toNat ≤ _ ∧ _ + _ ≤ slot.toNat + 233 ∧ _ + _ ≤ 2^64
    rw [hd]
    omega
  let pushed := memStore mem (sp - 8) (0x10641d : BitVec 64)
  let copied := memCopy pushed (sp + 160) src n
  have f : RamWriteFrame mem copied [packingWindow sp] :=
    ((RamWriteFrame.refl _ _).memStore (0x10641d : BitVec 64) inside).memStore _ dstIn
  apply (f.trans (rearranged_frame sp copied (by omega)) ?_).memStore _ inside
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact ⟨_, List.mem_singleton_self _, by change slot.toNat ≤ sp.toNat; omega,
    by change sp.toNat + 126 ≤ slot.toNat + 233; omega⟩

private theorem copyAndPackWidths {regs : Values Value Reg.count} {mem : Ram} {sp src n : BitVec 64}
    {bytes : ByteArray} (stack : List (StackFrame Value Label signature Reg.count))
    (hsp : regs[4].get 64 = sp) (hsrc : regs[3].get 64 = src)
    (hn : regs[14].get 64 = n) (hdf : regs[22].get 1 = 0)
    (hsize : n.toNat = bytes.size) (hsmall : bytes.size ≤ 65)
    (win : Writable Extracted.programImage mem (sp - 8) 233)
    (read : Readable mem src bytes.size) (sep : Outside [packingWindow sp] src bytes.size)
    (input : ∀ i (hi : i < bytes.size), memByte mem (src + BitVec.ofNat 64 i) = bytes[i])
    (zero : ∀ i, bytes.size ≤ i → i < 65 → memByte mem (sp + 160 + BitVec.ofNat 64 i) = 0)
    (hc : ∀ x ∈ fnCode, x ∈ Extracted.programImage)
    (got : LoadOk mem 0x203dd0 8) (target : memLoad mem 0x203dd0 64 = 0x12a820) :
    ∃ args m,
      (program.sem (dialect Extracted.programImage)).Reaches
        ⟨⟨.l106409, regs, mem⟩, stack⟩ ⟨⟨.l121480, args, m⟩, affineResume :: stack⟩ ∧
      args[8].width = 64 ∧ args[9] = regs[9] ∧
      args[3] = ⟨64, sp + 160⟩ ∧ args[4] = ⟨64, sp - 8⟩ ∧ args[6] = ⟨64, sp + 4⟩ ∧ args[7] = ⟨64, sp + 160⟩ ∧
      (∀ i < 65, memByte m (sp + 4 + BitVec.ofNat 64 i) = bytes.data[i]?.getD 0) ∧
      memLoad m (sp - 8) 64 = 0x1064f4 ∧ RamWriteFrame mem m [packingWindow sp] ∧
      (∀ r ∈ [5, 12, 13, 14, 15, 22, 39, 50, 51], ∀ hr : r < Reg.count, args[r] = regs[r]) := by
  let slot := sp - 8
  let pushed := memStore mem slot (0x10641d : BitVec 64)
  let copied := memCopy pushed (sp + 160) src n.toNat
  change Writable _ mem slot 233 at win
  have hslot := win.sub (a := slot) (n := 8) (Nat.le_refl _) (by change slot.toNat + 8 ≤ slot.toNat + 233; omega)
  have guard := memcpyCallStoreOk hslot hc
  obtain ⟨callArgs, callRun, len, sp₁, src₁, dst₁, keep₁⟩ :=
    memcpyCall sp src n hsp hsrc hn guard got target
  have hd : (sp + 160).toNat = slot.toNat + 168 :=
    toNat_of_offsets (x := sp) (c := 160) (d := 0 - 8) (n := 65)
      rfl (addr_sub _ _) win.readable.low (by decide)
  have outside := sep.2 (packingWindow sp) (List.mem_singleton_self _)
  change src.toNat + bytes.size ≤ slot.toNat ∨ slot.toNat + 233 ≤ src.toNat at outside
  have sep' : src.toNat + n.toNat ≤ (sp + 160).toNat ∨ (sp + 160).toNat + n.toNat ≤ src.toNat := by omega
  have hwrite : Writable Extracted.programImage pushed (sp + 160) n.toNat :=
    (win.sub (by omega) (by omega)).memStore _ _
  have ret : memLoad pushed slot 64 = 0x10641d :=
    memLoad_memStore_same _ _ _ (by decide) (by decide)
  have ap : RangeApart (sp + 160) n.toNat slot 8 := by
    apply RangeApart.of_offsets (x := sp) (c := 160) (d := 0 - 8) rfl (addr_sub _ _)
    constructor
    · change n.toNat ≤ 18446744073709551448
      omega
    · decide
  have read' : Readable pushed src n.toNat := hsize ▸ read.memStore _ _
  have df₁ := (congrArg (Value.get 1) (keep₁ 22 (by decide) (by decide))).trans hdf
  obtain ⟨out, exec, store, tag, _, sp₂, keep₂⟩ :=
    K256.Proofs.Sec1.Wrapper.Copy.memcpy (mem := pushed) (rsp := slot) (dst := sp + 160) (src := src) (count := n) (congrArg (Value.get 64) dst₁)
      (congrArg (Value.get 64) src₁) (congrArg (Value.get 64) len)
      (congrArg (Value.get 64) sp₁) df₁ read' hwrite sep' ap (hslot.readable.memStore _ _)
      (by rw [ret]; decide)
  have resume : (program.sem (dialect Extracted.programImage)).Reaches
      ⟨⟨.l106409, regs, mem⟩, stack⟩ ⟨⟨.l10641d, out.values, copied⟩, stack⟩ := by
    refine .step (b := ⟨⟨.l12a820, callArgs, pushed⟩, memcpyResume :: stack⟩) ?_ ?_
    · change (program.runBlock _ _).next _ _ = _
      rw [callRun]
      rfl
    have back := ParseSignature.exec_reaches_resume exec memcpyResume stack (by rw [tag, ret]; rfl)
    have same := ParseSignature.resume_arguments memcpyResume out
    dsimp only [StackFrame.resume] at same
    simp only [List.nil_append, StackFrame.resume, same, store] at back
    exact back
  have wincopy : Writable Extracted.programImage copied slot 233 :=
    (win.memStore _ _).memStore _ _
  obtain ⟨args, run, bx, sf, si, di, keep₃⟩ :=
    affineCall out.values copied sp (by rw [sp₂]; exact BitVec.sub_add_cancel ..) wincopy hc
  have preserved := affineCallPreserves run
  have remain (x : BitVec 64) (h : ∀ j < 8, slot + BitVec.ofNat 64 j ≠ x) :
      memByte pushed x = memByte mem x :=
    congrArg (fun z : Option UInt8 => z.getD 0)
      (memStore_getElem?_of_ne mem slot (0x10641d : BitVec 64) x h)
  have srcApart : RangeApart slot 8 src bytes.size := by
    apply RangeApart.of_toNat
    · have := hslot.readable.low; omega
    · have := read.low; omega
    · omega
  have tailApart : RangeApart slot 8 (sp + 160) 65 := RangeApart.of_offsets
    (x := sp) (c := 0 - 8) (d := 160) (addr_sub _ _) rfl (by decide)
  refine ⟨args, affineMemory sp copied, resume.trans (.step ?_ (.refl _)),
    (congrArg Value.width preserved.1).trans (memcpyR8 exec),
    preserved.2.trans ((keep₂ 9 (by decide)).trans (keep₁ 9 (by decide) _)), bx, sf, si, di, ?_,
    memLoad_memStore_same _ _ _ (by decide) (by decide), ?_, ?_⟩
  · change (program.runBlock _ _).next _ _ = _
    rw [run]
    rfl
  · dsimp only [copied]
    rw [hsize]
    apply affineInput hsmall
    · intro i hi
      exact (remain _ (fun j hj => srcApart j hj i hi)).trans (input i hi)
    · intro i h hi
      exact (remain _ (fun j hj => tailApart j hj i hi)).trans (zero i h hi)
  · exact copyFrame win (hsize ▸ hsmall)
  · intro r hr hr'
    have ok : r ∈ ([3, 5, 9, 10, 11, 12, 13, 14, 15, 22, 39, 50, 51] : List Nat) := by
      simp_all only [List.mem_cons, List.not_mem_nil, or_false]
      grind
    exact (keep₃ r hr hr').trans ((keep₂ ⟨r,hr'⟩ ok).trans (keep₁ r ok hr'))


theorem acceptedEncodingWidths {regs : Values Value Reg.count} {mem : Ram} {sp src dst n : BitVec 64}
    {bytes : ByteArray} (stack : List (StackFrame Value Label signature Reg.count))
    (_wr8 : regs[8].width = 64) (wr9 : regs[9].width = 64)
    (hsp : regs[4].get 64 = sp) (hsrc : regs[6].get 64 = src)
    (hdst : regs[7].get 64 = dst) (hn : regs[2].get 64 = n) (hdf : regs[22].get 1 = 0)
    (hsize : n.toNat = bytes.size) (sizes : n = 1 ∨ n = 33 ∨ n = 65)
    (align : sp.toNat % 16 = 0)
    (win : Writable Extracted.programImage mem (sp - 8) 233)
    (read : Readable mem src bytes.size) (sep : Outside [packingWindow sp] src bytes.size)
    (input : ∀ i (hi : i < bytes.size), memByte mem (src + BitVec.ofNat 64 i) = bytes[i])
    (hc : ∀ x ∈ fnCode, x ∈ Extracted.programImage)
    (gSet : LoadOk mem 0x203e10 8) (tSet : memLoad mem 0x203e10 64 = 0x12a700)
    (gCopy : Readable mem 0x203dd0 8) (tCopy : memLoad mem 0x203dd0 64 = 0x12a820)
    (apart : Outside [packingWindow sp] 0x203dd0 8) :
    ∃ args m,
      (program.sem (dialect Extracted.programImage)).Reaches
        ⟨⟨.l1063d2, regs, mem⟩, stack⟩ ⟨⟨.l121480, args, m⟩, affineResume :: stack⟩ ∧
      args[8].width = 64 ∧ args[9].width = 64 ∧
      args[3] = ⟨64, sp + 160⟩ ∧ args[4] = ⟨64, sp - 8⟩ ∧
      args[6] = ⟨64, sp + 4⟩ ∧ args[7] = ⟨64, sp + 160⟩ ∧ args[12] = ⟨64, 0⟩ ∧
      args[14] = ⟨64, n⟩ ∧ args[15] = ⟨64, dst⟩ ∧
      (∀ i < 65, memByte m (sp + 4 + BitVec.ofNat 64 i) = bytes.data[i]?.getD 0) ∧
      memLoad m (sp - 8) 64 = 0x1064f4 ∧ RamWriteFrame mem m [packingWindow sp] ∧
      (∀ r ∈ [5, 13, 22, 39, 50, 51], ∀ hr : r < Reg.count, args[r] = regs[r]) := by
  let slot := sp - 8
  let pushed := memStore mem slot (0x106409 : BitVec 64)
  change Writable _ mem slot 233 at win
  have small : n.toNat ≤ 65 := by rcases sizes with rfl | rfl | rfl <;> decide
  have fillCount : (65 - n).toNat = 65 - n.toNat := by rcases sizes with rfl | rfl | rfl <;> decide
  have sd : (sp + 160).toNat = slot.toNat + 168 :=
    toNat_of_offsets (x := sp) (c := 160) (d := 0 - 8) (n := 65)
      rfl (addr_sub _ _) win.readable.low (by decide)
  have low := win.readable.low
  have fillBase : (sp + 160 + n).toNat = slot.toNat + 168 + n.toNat := by
    rw [BitVec.toNat_add, sd, Nat.mod_eq_of_lt (by omega)]
  have slotWrite : Writable Extracted.programImage mem slot 8 :=
    win.sub (Nat.le_refl _) (by omega)
  have guard := memsetCallStoreOk slotWrite hc
  obtain ⟨callArgs, callRun, count, bx, sp₁, byte, fillDst, r12, r14, r15, keep₁⟩ :=
    memsetCall sp src dst n hsp hsrc hdst hn sizes guard gSet tSet
  have df₁ := (congrArg (Value.get 1) (keep₁ 22 (by decide) (by decide))).trans hdf
  have writable : Writable Extracted.programImage pushed (sp + 160 + n) (65 - n).toNat :=
    (win.sub (by omega) (by omega)).memStore _ _
  have slotRead := slotWrite.readable.memStore slot (0x106409 : BitVec 64)
  have ret : memLoad pushed slot 64 = 0x106409 :=
    memLoad_memStore_same _ _ _ (by decide) (by decide)
  have hs : Outside [buffer (sp + 160 + n) (65 - n).toNat] slot 8 := by
    refine ⟨by omega, ?_⟩
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact Or.inl (by change slot.toNat + 8 ≤ (sp + 160 + n).toNat; omega)
  obtain ⟨filled, fillRun, tag, sp₂, keep₂, f, zero⟩ :=
    memsetBlock hc sizes align sp₁ count byte fillDst df₁ writable
      ⟨slotRead.low, slotRead.present⟩ ret hs
  have resume : (program.sem (dialect Extracted.programImage)).Reaches
      ⟨⟨.l1063d2, regs, mem⟩, stack⟩ ⟨⟨.l106409, filled.values, filled.store⟩, stack⟩ := by
    refine .step (b := ⟨⟨.l12a700, callArgs, pushed⟩, memsetResume :: stack⟩) ?_ (.step ?_ (.refl _))
    · change (program.runBlock _ _).next _ _ = _
      rw [callRun]
      rfl
    · change (program.runBlock _ _).next _ _ = _
      rw [fillRun]
      have he : memsetResume.Accepts (dialect Extracted.programImage) filled.tag = true := by rw [tag]; rfl
      have same := ParseSignature.resume_arguments memsetResume filled
      dsimp only [StackFrame.resume] at same
      simp only [Transfer.next, he, ite_true, StackFrame.resume, same]
      rfl
  have sf : RamWriteFrame mem pushed [packingWindow sp] := by
    apply (RamWriteFrame.refl _ _).memStore
    exact ⟨_, List.mem_singleton_self _, Nat.le_refl _, by change slot.toNat + 8 ≤ slot.toNat + 233; omega,
      by change slot.toNat + 8 ≤ 2^64; omega⟩
  have frame : RamWriteFrame mem filled.store [packingWindow sp] := by
    apply sf.trans f
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨_, List.mem_singleton_self _, ?_, ?_⟩
    · change slot.toNat ≤ (sp + 160 + n).toNat
      omega
    · change (sp + 160 + n).toNat + (65 - n).toNat ≤ slot.toNat + 233
      omega
  have srcBytes (i : Nat) (hi : i < bytes.size) :
      memByte filled.store (src + BitVec.ofNat 64 i) = bytes[i] := by
    have srclow := read.low
    have pos : (src + BitVec.ofNat 64 i).toNat = src.toNat + i := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := i) (by omega),
        Nat.mod_eq_of_lt (by omega)]
    refine (congrArg (fun z : Option UInt8 => z.getD 0) (frame.outside _ ?_)).trans (input i hi)
    refine ⟨by omega, fun r hr => ?_⟩
    rcases sep.2 r hr with left | right <;> omega
  have zeros (i : Nat) (hb : bytes.size ≤ i) (hi : i < 65) :
      memByte filled.store (sp + 160 + BitVec.ofNat 64 i) = 0 := by
    have h := zero (i - bytes.size) (by omega)
    have he : n + BitVec.ofNat 64 (i - bytes.size) = BitVec.ofNat 64 i := by
      have eq := congrArg (BitVec.ofNat 64) (Nat.add_sub_of_le hb)
      rw [← hsize, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at eq
      simpa only [hsize] using eq
    rwa [BitVec.add_assoc, he] at h
  have fsrc := (keep₂ 3 (by decide) (by decide)).trans bx
  have flen := (keep₂ 14 (by decide) (by decide)).trans r14
  have fdf := (congrArg (Value.get 1) (keep₂ 22 (by decide) (by decide))).trans df₁
  have got := gCopy.of_frame frame
  obtain ⟨args, m, reach, width, kept9, outBx, outSp, outSi, outDi, encoded, retWord, frame', keep₃⟩ :=
    copyAndPackWidths stack (sp := sp) (n := n) (src := src) (congrArg (Value.get 64) sp₂)
      (congrArg (Value.get 64) fsrc) (congrArg (Value.get 64) flen) fdf hsize (by omega)
      (win.of_frame frame) (read.of_frame frame) sep srcBytes zeros hc ⟨got.low, got.present⟩
      ((frame.memLoad_eq apart).trans tCopy)
  refine ⟨args, m, resume.trans reach, width,
    (congrArg Value.width (kept9.trans ((keep₂ 9 (by decide) _).trans (keep₁ 9 (by decide) _)))).trans wr9,
    outBx, outSp, outSi, outDi,
    (keep₃ 12 (by decide) _).trans ((keep₂ 12 (by decide) _).trans r12),
    (keep₃ 14 (by decide) _).trans flen,
    (keep₃ 15 (by decide) _).trans ((keep₂ 15 (by decide) _).trans r15),
    encoded, retWord, frame.trans frame' (fun r hr => ⟨r, hr, Nat.le_refl _, Nat.le_refl _⟩), ?_⟩
  intro r hr hlt
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact (keep₃ _ (by decide) hlt).trans ((keep₂ _ (by decide) hlt).trans (keep₁ _ (by decide) hlt))

end K256.Proofs.Verify.Transfer.PublicKey
