import K256.Proofs.Signing.Nonce.Initialize.Seed.Parse.Shift.State

namespace K256.Proofs.Signing.Nonce.Initialize.DigestShift

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open CFG Lift Refine Verify.LIR Verify.Core

theorem computeMasksFrom {base source : BitVec 64} {a : Registers} {m : Ram}
    {w : Vector (BitVec 64) 4} (area : Writable Extracted.programImage m base 24)
    (input : Readable m source 32) (apart : RangeApart (base + 16) 8 source 32)
    (words : WordsAt m source 64 w) (sp : a[4] = ⟨64,base⟩)
    (src : a[6] = ⟨64,source⟩) (dst : a[7] = ⟨64,base + 88⟩) (shift : a[2] = ⟨64,0⟩) :
    ∃ b n, Reaches .l1065ca a m .l106667 b n ∧ Masks b w ∧ b[4] = ⟨64,base⟩ ∧
      memLoad n (base + 16) 64 = base + 88 ∧ FlagsKept a b ∧
      RamWriteFrame m n [⟨base.toNat,24⟩] := by
  have lim := area.readable.low
  have loaded (i : Nat) (hi : i < 4) :
      memLoad (memStore m (base + 16) (base + 88)) (wordAddr source 64 i) 64 = w[i] := by
    have within : 64 / 8 * i + 8 ≤ 32 := by omega
    exact (memLoad_memStore_of_rangeApart m _ _ _ 64 (RangeApart.right_sub apart within)).trans (words i hi)
  have word0 := loaded 0 (by decide)
  have word1 := loaded 1 (by decide)
  have word2 := loaded 2 (by decide)
  have word3 := loaded 3 (by decide)
  rw [show wordAddr source 64 0 = source from BitVec.add_zero _] at word0
  simp only [wordAddr, Nat.reduceDiv, Nat.reduceMul, ← BitVec.ofNat_eq_ofNat]
    at word1 word2 word3
  have run : ∃ (b : Registers) (n : Ram),
      program.runBlock (dialect Extracted.programImage) ⟨.l1065ca, a, m⟩ =
        .jump ⟨.l106667, b, n⟩ ∧ Masks b w ∧ b[4] = ⟨64, base⟩ ∧
      memLoad n (base + 16) 64 = base + 88 ∧ FlagsKept a b ∧
      RamWriteFrame m n [⟨base.toNat, 24⟩] := by
    refine ⟨?_, ?_, ?step, ?post⟩
    case step =>
      have rsp : a[4].get 64 = base := congrArg (Value.get 64) sp
      have rsi : a[6].get 64 = source := congrArg (Value.get 64) src
      have rdi : a[7].get 64 = base + 88 := congrArg (Value.get 64) dst
      have rdx : a[2].get 64 = 0 := congrArg (Value.get 64) shift
      cfg_eval [rsp, rsi, rdi, rdx, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceUShiftRight,
        BitVec.reduceAnd, setWidth_mergeGPR8]
      segment_words [word0, word1, word2, word3]
      repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l1065ca)
      rfl
    case post =>
      refine ⟨⟨?zero, ?byte, rfl, rfl, rfl, rfl, rfl⟩, sp, ?dest, ?flags, ?frame⟩
      case zero =>
        rintro ⟨i, _⟩ hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
      case byte =>
        change (mergeGPR 8 _ _).setWidth 8 = 0
        rw [setWidth_mergeGPR8]
        rfl
      case flags =>
        rintro ⟨i, _⟩ hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl <;> rfl
      case frame => slot_state region
      case dest => segment_words []
  obtain ⟨b, n, jump, masks, rsp, destination, flags, frame⟩ := run
  refine ⟨b, n, .single ?_, masks, rsp, destination, flags, frame⟩
  change (program.runBlock _ _).next _ [] = _
  rw [jump]
  rfl

theorem computeMasks {base : BitVec 64} {a : Registers} {m : Ram}
    {w : Vector (BitVec 64) 4} (area : Writable Extracted.programImage m base 216)
    (words : WordsAt m (base + 152) 64 w) (sp : a[4] = ⟨64,base⟩)
    (src : a[6] = ⟨64,base + 152⟩) (dst : a[7] = ⟨64,base + 88⟩) (shift : a[2] = ⟨64,0⟩) :
    ∃ b n, Reaches .l1065ca a m .l106667 b n ∧ Masks b w ∧ b[4] = ⟨64,base⟩ ∧
      memLoad n (base + 16) 64 = base + 88 ∧ FlagsKept a b ∧
      RamWriteFrame m n [⟨base.toNat,24⟩] := by
  have scratch : Writable Extracted.programImage m base 24 := area.sub (Nat.le_refl _) (by omega)
  have input : Readable m (base + 152) 32 :=
    area.readable.of_offsets rfl (BitVec.add_zero _).symm (by decide)
  have apart : RangeApart (base + 16) 8 (base + 152) 32 :=
    RangeApart.of_offsets rfl rfl (by decide)
  exact computeMasksFrom scratch input apart words sp src dst shift

end K256.Proofs.Signing.Nonce.Initialize.DigestShift
