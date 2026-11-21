import K256.Proofs.Sec1.Parser.Packing.CopyInput
import K256.Proofs.ParseSignature.Contract
import K256.Proofs.Sec1.Parser.Packing.ZeroFill

namespace K256.Proofs.Sec1.Parser.Packing

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Spec.Program
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Sec1.LIR
open K256.Proofs.ParseSignature (buffer)

theorem acceptedEncoding {regs : Values Value Reg.count} {mem : Ram} {sp src dst n : BitVec 64}
    {bytes : ByteArray} (stack : List (StackFrame Value Label signature Reg.count))
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
  obtain ⟨args, m, reach, outBx, outSp, outSi, outDi, encoded, retWord, frame', keep₃⟩ :=
    copyAndPack stack (sp := sp) (n := n) (src := src) (congrArg (Value.get 64) sp₂)
      (congrArg (Value.get 64) fsrc) (congrArg (Value.get 64) flen) fdf hsize (by omega)
      (win.of_frame frame) (read.of_frame frame) sep srcBytes zeros hc ⟨got.low, got.present⟩
      ((frame.memLoad_eq apart).trans tCopy)
  refine ⟨args, m, resume.trans reach, outBx, outSp, outSi, outDi,
    (keep₃ 12 (by decide) _).trans ((keep₂ 12 (by decide) _).trans r12),
    (keep₃ 14 (by decide) _).trans flen,
    (keep₃ 15 (by decide) _).trans ((keep₂ 15 (by decide) _).trans r15),
    encoded, retWord, frame.trans frame' (fun r hr => ⟨r, hr, Nat.le_refl _, Nat.le_refl _⟩), ?_⟩
  intro r hr hlt
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact (keep₃ _ (by decide) hlt).trans ((keep₂ _ (by decide) hlt).trans (keep₁ _ (by decide) hlt))

end K256.Proofs.Sec1.Parser.Packing
