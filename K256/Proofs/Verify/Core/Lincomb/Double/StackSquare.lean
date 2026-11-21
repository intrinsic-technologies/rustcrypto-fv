import K256.Proofs.Verify.Core.Lincomb.Double.Square
import K256.Proofs.Verify.Core.Lincomb.Double.StackFrame

namespace K256.Proofs.Verify.Core.Lincomb.Double

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  K256.Proofs.Verify.LIR Common.Field
open Generate.Generator.Multiply (SavedWidths)

abbrev childSp (sp : BitVec 64) : BitVec 64 := sp - 0x230

set_option maxRecDepth 1200 in
theorem squareOnStack {initial a : Registers} {orig m : Ram} {sp ret : BitVec 64}
    {input : Limbs} {s d : Nat}
    (e : RoutineEntry initial orig sp 0x298) (frame : RamWriteFrame orig m [scratch sp 0x298])
    (keep : ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15,22,39,50,51] → a[i] = initial[i])
    (rsp : a[4] = ⟨64,childSp sp⟩)
    (rsi : a[6] = ⟨64,(childSp sp + BitVec.ofNat 64 s)⟩)
    (rdi : a[7] = ⟨64,(childSp sp + BitVec.ofNat 64 d)⟩)
    (sMin : 8 ≤ s) (dMin : 8 ≤ d) (sFit : s + 40 ≤ 0x230) (dFit : d + 40 ≤ 0x230)
    (disjoint : s + 40 ≤ d ∨ d + 40 ≤ s) (dAligned : d % 8 = 0)
    (retAt : memLoad m (childSp sp) 64 = ret) (retLow : ret.toNat < 2^32)
    (words : WordsAt m (childSp sp + BitVec.ofNat 64 s) 64 input) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l1145f0, a, m⟩, []⟩ out ∧
      out.tag = some ⟨64,ret⟩ ∧ out.values[4] = ⟨64,childSp sp + 8⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15,22,39,50,51] → out.values[i] = initial[i]) ∧
      RamWriteFrame m out.store [⟨(sp - 0x298).toNat,104⟩,
        ⟨(childSp sp + BitVec.ofNat 64 d).toNat,40⟩] ∧
      RamWriteFrame orig out.store [scratch sp 0x298] ∧
      WordsAt out.store (childSp sp + BitVec.ofNat 64 d) 64 (squareWords input) := by
  have room := e.room
  have spNat : (childSp sp).toNat = sp.toNat - 0x230 :=
    BitVec.toNat_sub_of_le (by exact show 0x230 ≤ sp.toNat by omega)
  have lowNat : (sp - 0x298).toNat = sp.toNat - 0x298 := BitVec.toNat_sub_of_le (by exact room)
  have high := e.stack.readable.low
  change (sp - 0x298).toNat + 0x298 ≤ 2^32 at high
  rw [lowNat] at high
  have offset (k : Nat) (hk : k ≤ 0x230) :
      (childSp sp + BitVec.ofNat 64 k).toNat = sp.toNat - 0x230 + k := by
    rw [BitVec.toNat_add, spNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt (by omega)]
  have lo : childSp sp - 104 = sp - 0x298 := by dsimp only [childSp]; bv_omega
  have area : Writable Extracted.programImage m (sp - 0x298) 0x298 := e.stack.of_frame frame
  have win : Writable Extracted.programImage m (childSp sp - 104) 112 := by
    rw [lo]
    exact area.sub (Nat.le_refl _) (Nat.add_le_add_left (by decide : 112 ≤ 0x298) _)
  have small (k : Nat) (hk : k + 40 ≤ 0x230) :
      Writable Extracted.programImage m (childSp sp + BitVec.ofNat 64 k) 40 := by
    apply area.sub
    all_goals
      change _ ≤ _
      rw [offset k (by omega), lowNat]
      omega
  have widths : SavedWidths a := by
    intro i hi
    have hs : i.val ∈ [3,5,12,13,14,15] := hi
    have hk : i.val ∈ [3,5,12,13,14,15,22,39,50,51] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs ⊢
      omega
    exact (congrArg Value.width (keep i hk)).trans (e.saved i hs)
  have align := e.aligned
  obtain ⟨out, run, tag, stack, kept, writes, result⟩ :=
    squareCall rsp rsi rdi ((keep 22 (by decide)).trans e.df) widths
      ((congrArg Value.width (keep 39 (by decide))).trans e.mxcsr)
      ((congrArg Value.width (keep 50 (by decide))).trans e.ftw)
      ((congrArg Value.width (keep 51 (by decide))).trans e.fcw)
      win (small s sFit).readable (small d dFit)
      (by rw [spNat, offset s (by omega)]; omega)
      (by rw [spNat, offset d (by omega)]; omega)
      (by rw [offset d (by omega), offset s (by omega)]; omega)
      (by rw [offset d (by omega)]; omega)
      (by rw [spNat]; omega) (by rw [spNat]; omega) retAt retLow words
  rw [lo] at writes
  have map : windows sp [(0,104),(104+d,40)] =
      [⟨(sp - 0x298).toNat,104⟩, ⟨(childSp sp + BitVec.ofNat 64 d).toNat,40⟩] := by
    have base : bottom sp + BitVec.ofNat 64 104 = childSp sp := by
      dsimp only [bottom,childSp]
      bv_omega
    simp only [windows,List.map_cons,List.map_nil,below,BitVec.ofNat_add,← BitVec.add_assoc,base,
      BitVec.ofNat_eq_ofNat,BitVec.add_zero]
    rfl
  have within : RegionsWithin [⟨(sp - 0x298).toNat,104⟩,
      ⟨(childSp sp + BitVec.ofNat 64 d).toNat,40⟩] [scratch sp 0x298] := by
    rw [← map]
    apply windowsWithin room e.stack.readable.low
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    rintro r (rfl|rfl) <;> change _ ≤ 0x298 <;> omega
  exact ⟨out, run, tag, stack, fun i hi => (kept i hi).trans (keep i hi),
    writes, frame.trans writes within, result⟩

end K256.Proofs.Verify.Core.Lincomb.Double
