import K256.Proofs.Sec1.Parser.Packing.AffineCall
import K256.Proofs.Sec1.Parser.Packing.CallSetup
import K256.Proofs.Sec1.Parser.Packing.PaddedInput
import K256.Proofs.Sec1.Wrapper.Copy.Execution
import K256.Proofs.ParseSignature.Call

namespace K256.Proofs.Sec1.Parser.Packing

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Spec.Program
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Sec1.LIR

def packingWindow (sp : BitVec 64) : MemoryRegion := ⟨(sp - 8).toNat, 233⟩

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

theorem copyAndPack {regs : Values Value Reg.count} {mem : Ram} {sp src n : BitVec 64}
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
    Wrapper.Copy.memcpy (mem := pushed) (rsp := slot) (dst := sp + 160) (src := src) (count := n) (congrArg (Value.get 64) dst₁)
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
  refine ⟨args, affineMemory sp copied, resume.trans (.step ?_ (.refl _)), bx, sf, si, di, ?_,
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

end K256.Proofs.Sec1.Parser.Packing
