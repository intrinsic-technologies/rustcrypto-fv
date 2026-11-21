import K256.Proofs.Sec1.Serialize.Assemble.Memory
import K256.Proofs.Sec1.LIR.Fn1215e0
import K256.Proofs.Common.Refine.Lemma.Region

namespace K256.Proofs.Sec1.Serialize.Assemble

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine LIR

def assemblyResume : StackFrame Value Label signature Reg.count :=
  { target := .l121831, kept := #v[], arity := rfl, guard := some ⟨64, 0x121831⟩ }

def assemblyBuffers (sp : BitVec 64) : List MemoryRegion :=
  [⟨(sp + 215).toNat, 65⟩, ⟨(sp + 8).toNat, 65⟩]

def assemblyWrites (sp : BitVec 64) : List MemoryRegion :=
  ⟨(sp - 8).toNat, 8⟩ :: assemblyBuffers sp

private theorem stackLoadAfterStore {m : Ram} {sp c d : BitVec 64} {w n : Nat} (v : BitVec n)
    (h₁ : n / 8 ≤ (d - c).toNat) (h₂ : w / 8 ≤ (c - d).toNat) :
    memLoad (memStore m (sp + c) v) (sp + d) w = memLoad m (sp + d) w :=
  memLoad_memStore_of_rangeApart m _ _ _ _ (RangeApart.of_offsets rfl rfl ⟨h₁, h₂⟩)

private theorem pointLoadAfterStore {mem : Ram} {a point : BitVec 64} {w : Nat}
    {v : BitVec w} {regs : List MemoryRegion}
    (apart : Outside regs (point + 80) 4) (slot : InRegions regs a (w / 8)) :
    memLoad (memStore mem a v) (point + 80) 32 = memLoad mem (point + 80) 32 :=
  ((RamWriteFrame.refl _ _).memStore v slot).memLoad_eq apart

private theorem byteAt {mem : Ram} {a : BitVec 64} {v : BitVec 8}
    (hr : Readable mem a 1) (h : memLoad mem a 8 = v) :
    mem[a]? = some (UInt8.ofBitVec v) := by
  have hp : ∀ i < 8 / 8, (mem[a + BitVec.ofNat 64 i]?).isSome := hr.present
  have hb := Bytes.of_memLoad (n := 8) hp
  rw [h] at hb
  have h0 := hb 0 (by decide)
  have hv : UInt8.ofNat v.toNat = UInt8.ofBitVec v := UInt8.ofNat_toNat (x := UInt8.ofBitVec v)
  simpa only [BitVec.add_zero, storedByte, Nat.mul_zero, Nat.shiftRight_zero, hv] using h0

set_option hygiene false in
local macro "in_assembly_buffer" : tactic =>
  `(tactic| (
    unfold InRegions assemblyBuffers
    first
    | (refine ⟨(⟨(sp + 215).toNat, 65⟩ : MemoryRegion), List.mem_cons_self, ?_⟩
       apply inStackRegionOffsets stack rfl rfl <;> decide)
    | (refine ⟨(⟨(sp + 8).toNat, 65⟩ : MemoryRegion),
        List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩
       apply inStackRegionOffsets stack rfl rfl <;> decide)))

set_option hygiene false in
local macro "read_assembly_word" : tactic =>
  `(tactic| simp
    (disch := first | decide | (apply RangeApart.of_offsets (addr_sub sp 8) rfl; decide) |
      (apply RangeApart.of_offsets rfl rfl; decide))
    only [memLoad_memStore_same, memLoad_memStore_of_rangeApart, Lift.reduceAddOffset])

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
theorem assembleCoordinates {code : CodeMap} {args : Values Value Reg.count} {mem : Ram}
    {sp point : BitVec 64} {x y : Vector (BitVec 64) 4}
    (hcode : ∀ entry ∈ fnCode, entry ∈ code)
    (rsp : args[4].get 64 = sp) (r14 : args[14].get 64 = point) (tag : args[0].get 8 = 4)
    (stack : Writable code mem (sp - 8) 288)
    (pointRead : Readable mem (point + 80) 4)
    (pointApart : Outside (assemblyBuffers sp) (point + 80) 4)
    (infinity : memLoad mem (point + 80) 8 = 0)
    (hx : WordsAt mem (sp + 80) 64 x) (hy : WordsAt mem (sp + 8) 64 y) :
    ∃ (next : Values Value Reg.count) (written : Ram),
      program.runBlock (dialect code) ⟨.l12176c, args, mem⟩ =
        .call ⟨.l127d50, next, written⟩ assemblyResume ∧
      next[4] = ⟨64, sp - 8⟩ ∧ next[7].get 8 = 0 ∧
      (∀ i : Fin Reg.count, i.val ∈ [2,3,5,6,8,9,10,11,12,13,14,15,22,39,50,51] →
        next[i] = args[i]) ∧
      RamWriteFrame mem written (assemblyWrites sp) ∧
      memLoad written (sp - 8) 64 = 0x121831 ∧ written[sp + 215]? = some 4 ∧
      WordsAt written (sp + 216) 64 x ∧ WordsAt written (sp + 248) 64 y ∧
      Bytes written (sp + 8) 65 (fun _ => 0) := by
  have htag : (args[0].get 64).setWidth 8 = 4 := by
    simpa only [Value.get, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64)] using tag
  have hload {a c : BitVec 64} (ha : a = sp + c) (h : (c - (0 - 8)).toNat + 8 ≤ 288) :
      LoadOk mem a 8 :=
    let slot := (stackSlot stack ha h).readable
    ⟨slot.low, slot.present⟩
  have hpLoad : LoadOk mem (point + 80) 4 := ⟨pointRead.low, pointRead.present⟩
  have hstore {a c pc : BitVec 64} {n len : Nat} (ha : a = sp + c)
      (h : (c - (0 - 8)).toNat + n ≤ 288)
      (hp : (pc - 0x12176c).toNat + len ≤ bytes_l12176c.length) :
      StoreOk code mem a n pc len :=
    storeOk_inBlock (stackSlot stack ha h) (fun entry he => hcode entry (code_l12176c entry he)) hp
  have x0 : memLoad mem (sp + 80) 64 = x[0] := wordsAtOffset hx 0 (by decide)
  have x1 : memLoad mem (sp + 88) 64 = x[1] := wordsAtOffset hx 1 (by decide)
  have x2 : memLoad mem (sp + 96) 64 = x[2] := wordsAtOffset hx 2 (by decide)
  have x3 : memLoad mem (sp + 104) 64 = x[3] := wordsAtOffset hx 3 (by decide)
  have y0 : memLoad mem (sp + 8) 64 = y[0] := wordsAtOffset hy 0 (by decide)
  have y1 : memLoad mem (sp + 16) 64 = y[1] := wordsAtOffset hy 1 (by decide)
  have y2 : memLoad mem (sp + 24) 64 = y[2] := wordsAtOffset hy 2 (by decide)
  have y3 : memLoad mem (sp + 32) 64 = y[3] := wordsAtOffset hy 3 (by decide)
  obtain ⟨next, written, step, stackReg, arg, keeps, frame⟩ :
      ∃ (next : Values Value Reg.count) (written : Ram),
        program.runBlock (dialect code) ⟨.l12176c, args, mem⟩ =
          .call ⟨.l127d50, next, written⟩ assemblyResume ∧
        next[4] = ⟨64, sp - 8⟩ ∧ next[7] = ⟨64, (memLoad mem (point + 80) 32).setWidth 64⟩ ∧
        (∀ i : Fin Reg.count, i.val ∈ [2,3,5,6,8,9,10,11,12,13,14,15,22,39,50,51] →
          next[i] = args[i]) ∧
        RamWriteFrame mem written (assemblyWrites sp) ∧
        memLoad written (sp - 8) 64 = 0x121831 ∧ memLoad written (sp + 215) 8 = 4 ∧
        WordsAt written (sp + 216) 64 x ∧ WordsAt written (sp + 248) 64 y ∧
        WordsAt written (sp + 8) 64 (Vector.replicate 8 0) ∧ memLoad written (sp + 72) 8 = 0 := by
    refine ⟨?next, ?written, ?step, ?stackReg, ?arg, ?keeps, ?frame, ?ret, ?tag, ?x, ?y, ?zero, ?tail⟩
    case step =>
      cfg_eval [b_l12176c_1, rsp, r14, htag, stackLoadAfterStore,
        BitVec.reduceSub, x0, x1, x2, x3, y0, y1, y2, y3]
      iterate 28
        refine (ite_eq_left ?_).trans ?_
        · repeat first | apply loadOk_memStore | apply storeOk_memStore
          first
          | exact hpLoad
          | apply hload rfl <;> decide
          | apply hstore rfl <;> decide
          | apply hstore (addr_sub sp 8) <;> decide
      simp (config := {maxSteps := 1000000})
        (disch := first | (apply RangeApart.of_offsets rfl rfl; decide) | in_assembly_buffer) only
        [memLoad_memStore_of_rangeApart, pointLoadAfterStore pointApart, x2, x3, y0, y1, y2, y3]
      rfl
    case stackReg => rfl
    case arg => rfl
    case keeps =>
      intro ⟨i, _⟩ hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    case frame =>
      apply RamWriteFrame.memStore
      case hin => exact ⟨_, List.mem_cons_self,
        inStackRegionOffsets stack (addr_sub sp 8) (addr_sub sp 8) (by decide) (by decide)⟩
      have inWrites {a : BitVec 64} {n : Nat} (h : InRegions (assemblyBuffers sp) a n) :
          InRegions (assemblyWrites sp) a n := by
        obtain ⟨region, hregion, hin⟩ := h
        exact ⟨region, List.mem_cons_of_mem _ hregion, hin⟩
      iterate 18
        apply RamWriteFrame.memStore
        case hin =>
          apply inWrites
          in_assembly_buffer
      exact RamWriteFrame.refl _ _
    case ret => exact memLoad_memStore_same _ _ _ (by decide) (by decide)
    case tag => read_assembly_word
    case x => apply fourWordsAt <;> read_assembly_word
    case y => apply fourWordsAt <;> read_assembly_word
    case zero =>
      intro i hi
      have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
      rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [wordAddr, Vector.getElem_replicate, Nat.reduceDiv, Nat.reduceMul, Lift.reduceAddOffset] <;>
        read_assembly_word
    case tail => read_assembly_word
  obtain ⟨frame, ret, tagWord, xWords, yWords, zeroWords, tailWord⟩ := frame
  have hchoice : next[7].get 8 = 0 := by
    rw [arg]
    change ((memLoad mem (point + 80) 32).setWidth 64).setWidth 8 = 0
    rw [BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64),
      BitVec.setWidth_eq_extractLsb' (by decide : 8 ≤ 32)]
    simpa only [Nat.reduceDiv, BitVec.add_zero, infinity] using
      extractLsb'_memLoad mem (point + 80) (n := 32) 0 8 (by decide) (by decide) (by decide)
  have hi : Readable written (sp + 215) 1 :=
    (stackSlot stack rfl (by decide)).readable.of_frame frame
  have hz : Readable written (sp + 8) 64 :=
    (stackSlot stack rfl (by decide)).readable.of_frame frame
  have ht : Readable written (sp + 72) 1 :=
    (stackSlot stack rfl (by decide)).readable.of_frame frame
  refine ⟨next, written, step, stackReg, hchoice, keeps, frame, ret, byteAt hi tagWord,
    xWords, yWords, ?_⟩
  intro i hi
  by_cases h : i < 64
  · have hb := (zeroWords.bytes hz) i h
    have zeroByte (j : Nat) : storedByte (0 : BitVec 64) j = 0 := by
      change UInt8.ofNat (0 >>> (8 * j)) = 0
      rw [Nat.zero_shiftRight]
      rfl
    simpa only [show i / (64 / 8) < 8 by omega, ↓reduceDIte, Vector.getElem_replicate,
      zeroByte] using hb
  · have h64 : i = 64 := by omega
    subst i
    have hb := byteAt ht tailWord
    have hzero : UInt8.ofBitVec (0 : BitVec 8) = 0 := by decide
    simpa only [Lift.reduceAddOffset, hzero] using hb

end K256.Proofs.Sec1.Serialize.Assemble
