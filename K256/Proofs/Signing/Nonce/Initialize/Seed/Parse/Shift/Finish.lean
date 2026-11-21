import K256.Proofs.Signing.Nonce.Initialize.Seed.Parse.Shift.State
import K256.Proofs.Sec1.Serialize.Assemble.Memory
import K256.Proofs.Verify.Core.Affine.Call

namespace K256.Proofs.Signing.Nonce.Initialize.DigestShift

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open CFG Lift Refine Verify.LIR Verify.Core

theorem finishFrom {base : BitVec 64} {a : Registers} {m : Ram}
    {w : Vector (BitVec 64) 4} (area : Writable Extracted.programImage m base 216)
    {caller : Registers} {returnTag : BitVec 64} (sp : a[4] = ⟨64,base⟩) (masks : Masks a w)
    (dst : memLoad m (base + 16) 64 = base + 88) (saved : Saved base caller m returnTag)
    (returnLow : returnTag.toNat < 2^32 := by decide) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l106667,a,m⟩,[]⟩ out ∧
      out.tag = some ⟨64,returnTag⟩ ∧ RamWriteFrame m out.store [⟨base.toNat, 24⟩, ⟨(base + 88).toNat, 32⟩] ∧
      WordsAt out.store (base + 88) 64 w ∧ out.values[4] = ⟨64,base + 80⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15] → out.values[i] = ⟨64,caller[i].get 64⟩) ∧
      FlagsKept a out.values ∧ ParseSignature.ArgumentWidths out.values := by
  have lim := area.readable.low
  have rsp : a[4].get 64 = base := congrArg (Value.get 64) sp
  have di : (a[7].get 64).setWidth 8 = 0 :=
    (BitVec.setWidth_setWidth_of_le _ (by decide)).trans masks.byte
  have z0 : a[0].get 64 = 0 := congrArg (Value.get 64) (masks.zeroReg 0 (by decide))
  have z2 : a[2].get 64 = 0 := congrArg (Value.get 64) (masks.zeroReg 2 (by decide))
  have z5 : a[5].get 64 = 0 := congrArg (Value.get 64) (masks.zeroReg 5 (by decide))
  have z6 : a[6].get 64 = 0 := congrArg (Value.get 64) (masks.zeroReg 6 (by decide))
  have z8 : a[8].get 64 = 0 := congrArg (Value.get 64) (masks.zeroReg 8 (by decide))
  have z9 : a[9].get 64 = 0 := congrArg (Value.get 64) (masks.zeroReg 9 (by decide))
  have z11 : a[11].get 64 = 0 := congrArg (Value.get 64) (masks.zeroReg 11 (by decide))
  have z12 : a[12].get 64 = 0 := congrArg (Value.get 64) (masks.zeroReg 12 (by decide))
  have z14 : a[14].get 64 = 0 := congrArg (Value.get 64) (masks.zeroReg 14 (by decide))
  have w0 : a[10].get 64 = w[0] := congrArg (Value.get 64) masks.w0
  have w1 : a[3].get 64 = w[1] := congrArg (Value.get 64) masks.w1
  have w2 : a[15].get 64 = w[2] := congrArg (Value.get 64) masks.w2
  have w3 : a[13].get 64 = w[3] := congrArg (Value.get 64) masks.w3
  obtain ⟨bx, r12, r13, r14, r15, bp, ret⟩ := saved
  suffices ∃ out, program.runBlock (dialect Extracted.programImage) ⟨.l106667,a,m⟩ = .returned out ∧
      out.tag = some ⟨64,returnTag⟩ ∧ RamWriteFrame m out.store [⟨base.toNat, 24⟩, ⟨(base + 88).toNat, 32⟩] ∧
      WordsAt out.store (base + 88) 64 w ∧ out.values[4] = ⟨64,base + 80⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15] → out.values[i] = ⟨64,caller[i].get 64⟩) ∧
      FlagsKept a out.values ∧ ParseSignature.ArgumentWidths out.values by
    obtain ⟨out, step, post⟩ := this
    exact ⟨out, .done (by simp only [Program.step, step, CFG.Transfer.next]), post⟩
  cfg_eval [rsp, z0, z2, z5, z6, z8, z9, z11, z12, z14, w0, w1,
    w2, w3, di, BitVec.add_assoc, BitVec.reduceAdd, Lift.reduceAddOffset]
  segment_words [dst, bx, r12, r13, r14, r15, bp, ret]
  have zeroAnd (v : BitVec 64) : (0 : BitVec 64) &&& v = 0 := BitVec.zero_and
  have zeroXor (v : BitVec 64) : (0 : BitVec 64) ^^^ v = v := BitVec.zero_xor
  have onesAnd (v : BitVec 64) : (0xffffffffffffffff : BitVec 64) &&& v = v :=
    BitVec.allOnes_and
  simp only [BitVec.reduceNeg, BitVec.and_zero, zeroAnd, zeroXor, onesAnd,
    BitVec.zero_xor]
  have code : ∀ x ∈ codeRange 0x106667 bytes_l106667, x ∈ Extracted.programImage :=
    fun x hx => Verify.Core.Affine.coreText x (code_l106667 x hx)
  simp (disch := first | (refine ⟨?_, returnLow⟩; slot_guard using code) |
    slot_guard using code) only [ite_eq_left]
  refine ⟨_, rfl, rfl, ?_, ?_, rfl, ?_, ?_, ?_⟩
  · dsimp only [Output.store]
    slot_state region
  · apply Sec1.Serialize.Assemble.fourWordsAt <;> segment_words [BitVec.add_assoc, BitVec.reduceAdd]
  · rintro ⟨i, _⟩ hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · rintro ⟨i, _⟩ hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> rfl
  · rintro ⟨i, _⟩ hi
    simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> first | rfl | exact masks.width

theorem finish {base : BitVec 64} {a : Registers} {m : Ram}
    {w : Vector (BitVec 64) 4} (area : Writable Extracted.programImage m base 216)
    {caller : Registers} {returnTag : BitVec 64} (sp : a[4] = ⟨64,base⟩) (masks : Masks a w)
    (dst : memLoad m (base + 16) 64 = base + 88) (saved : Saved base caller m returnTag)
    (returnLow : returnTag.toNat < 2^32 := by decide) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l106667,a,m⟩,[]⟩ out ∧
      out.tag = some ⟨64,returnTag⟩ ∧ RamWriteFrame m out.store (footprint base) ∧
      WordsAt out.store (base + 88) 64 w ∧ out.values[4] = ⟨64,base + 80⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15] → out.values[i] = ⟨64,caller[i].get 64⟩) ∧
      FlagsKept a out.values ∧ ParseSignature.ArgumentWidths out.values := by
  obtain ⟨out, run, tag, writes, words, rsp, restores, flags, widths⟩ :=
    finishFrom area sp masks dst saved returnLow
  have limit := area.readable.low
  have offset : (base + 88).toNat = base.toNat + 88 := by
    simp only [BitVec.toNat_add, BitVec.reduceToNat, Nat.reducePow]
    omega
  have within : RegionsWithin [⟨base.toNat, 24⟩, ⟨(base + 88).toNat, 32⟩] (footprint base) := by
    intro r member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact ⟨_, List.mem_singleton_self _, Nat.le_refl _, Nat.add_le_add_left (by decide : 24 ≤ 184) _⟩
    · refine ⟨_, List.mem_singleton_self _, ?_, ?_⟩ <;>
        simp only [offset] <;> omega
  exact ⟨out, run, tag, (RamWriteFrame.refl m _).trans writes within, words, rsp, restores, flags, widths⟩

end K256.Proofs.Signing.Nonce.Initialize.DigestShift
