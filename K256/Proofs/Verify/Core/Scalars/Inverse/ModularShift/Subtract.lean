import K256.Proofs.Verify.LIR.Generated.Values
import K256.Proofs.Verify.Core.Scalars.Inverse.ModularShift.State
import K256.Proofs.Generate.Generator.Multiply.Split.Parameters
import K256.Proofs.Common.Invert.LinearCombination.Core

namespace K256.Proofs.Verify.Core.Scalars.Inverse.ModularShift

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Verify.LIR
open K256.Proofs.Generate.Generator.Affine.Invert.Core (CalleeFrame)
open Correction

private theorem jump {l r : Location Value Ram Label signature}
    (eq : program.runBlock (dialect Extracted.programImage) l = .jump r) :
    Reaches l.label l.arguments l.store r.label r.arguments r.store := by
  apply Semantics.Reaches.single
  change program.step _ _ = _
  simp only [Program.step, eq, Transfer.next]

private theorem subNat {sp : Word} {d : Nat} (h : d ≤ sp.toNat) :
    (sp - BitVec.ofNat 64 d).toNat = sp.toNat - d := by
  have index : (BitVec.ofNat 64 d).toNat = d := Nat.mod_eq_of_lt (by have := sp.isLt; omega)
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, index]; exact h), index]

private theorem countNat (p : Inputs) (bound : p.shift.toNat ≤ 62) :
    (v1089a7 p).toNat = 64 - p.shift.toNat := by
  simp only [v1089a7, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
  exact BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; change p.shift.toNat ≤ 64; omega)

set_option maxRecDepth 4096 in
private theorem shiftCheck {b : Registers} {m : Ram} {q : Word} {p : Inputs}
    (rsp : b[4] = ⟨64, q⟩) (shift : b[5] = ⟨64, p.shift.setWidth 64⟩)
    (win : Writable Extracted.programImage m q 120)
    (pos : 0 < p.shift.toNat) (bound : p.shift.toNat ≤ 62) :
    ∃ c, program.runBlock (dialect Extracted.programImage) ⟨.l10899e, b, m⟩ =
      .jump ⟨.l1089b2, c, memStore m (q + 68) p.shift⟩ ∧
      c[4] = b[4] ∧ c[3] = b[3] ∧ c[1] = ⟨64, (v1089a7 p).setWidth 64⟩ ∧
      ∀ i : Fin Reg.count, i.val ∈ [22, 39, 50, 51] → c[i] = b[i] := by
  have q64 : b[4].get 64 = q := congrArg (Value.get 64) rsp
  have k64 : b[5].get 64 = p.shift.setWidth 64 := congrArg (Value.get 64) shift
  have cf : ((64 : BitVec 32) - p.shift).toNat < 64 := by
    have h := countNat p bound
    simp only [v1089a7, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq] at h
    rw [h]
    omega
  refine ⟨?_, ?run, ?post⟩
  case run =>
    cfg_eval [b_l10899e, q64, k64, cf, not_true_eq_false, ite_false]
    segment_words [q64, k64, cf, not_true_eq_false, ite_false]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; first | slot_guard using code_l10899e | assumption)
    try rfl
  case post =>
    refine ⟨rfl, rfl, ?_, ?_⟩
    · simp only [v1089a7, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
      rfl
    ·
      intro ⟨i, hi⟩ h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl <;> rfl

private theorem adcValue (c : Bool) (x y : Word) :
    (adcSpec c x y).1 = x + y + BitVec.ofNat 64 c.toNat := rfl

private theorem adcTop (p : Inputs) :
    (v108a32 p).1 = (v108a21 p).2 + BitVec.ofNat 64 (v108a2f p).2.CF.toNat := by
  unfold v108a32
  rw [adcValue]
  exact congrArg (fun x : Word => x + BitVec.ofNat 64 (v108a2f p).2.CF.toNat) (BitVec.add_zero _)

private theorem sbbValue (c : Bool) (x y : Word) :
    (sbbSpec c x y).1 = x - (y + BitVec.ofNat 64 c.toNat) := rfl

private theorem negCarry (x : Word) : (negSpec x).2.CF = decide (x ≠ 0) := by
  rfl

private def subtractAtoms (sp dst : Word) (p : Inputs) : List Atom :=
  (beforeSelect sp dst p).dropLast

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3500000 in
private theorem subtractBlock {b : Registers} {m : Ram} {sp dst : Word} {p : Inputs}
    (rsp : b[4] = ⟨64, sp - 168⟩) (dstReg : b[3] = ⟨64, dst⟩)
    (count : b[1] = ⟨64, (v1089a7 p).setWidth 64⟩)
    (win : Writable Extracted.programImage m (sp - 168) 120)
    (args : Readable m (sp + 8) 16)
    (read0 : Readable m 0x2021a0 8) (read1 : Readable m 0x2021a8 8)
    (read2 : Readable m 0x2021b0 8) (read3 : Readable m 0x2021b8 8)
    (roApart : (sp - 168).toNat + 120 ≤ 0x2021a0 ∨ 0x2021c0 ≤ (sp - 168).toNat)
    (h0 : memLoad m (sp - 0x98) 64 = p.magnitude[0])
    (h1 : memLoad m (sp - 0x90) 64 = p.magnitude[1])
    (h2 : memLoad m (sp - 0x88) 64 = p.magnitude[2])
    (h3 : memLoad m (sp - 0x80) 64 = p.magnitude[3])
    (h4 : memLoad m (sp - 0x78) 64 = p.magnitude[4])
    (sign : memLoad m (sp - 0x70) 8 = p.sign)
    (shift : memLoad m (sp - 0x64) 32 = p.shift)
    (ptr : memLoad m (sp + 8) 64 = 0x2021a0)
    (inv : memLoad m (sp + 16) 64 = p.params.inverseWord)
    (r0 : memLoad m 0x2021a0 64 = p.params.modulusWords[0])
    (r1 : memLoad m 0x2021a8 64 = p.params.modulusWords[1])
    (r2 : memLoad m 0x2021b0 64 = p.params.modulusWords[2])
    (r3 : memLoad m 0x2021b8 64 = p.params.modulusWords[3])
    (room : 304 ≤ sp.toNat) (argHigh : sp.toNat + 24 ≤ 2^32)
    (pos : 0 < p.shift.toNat) (bound : p.shift.toNat ≤ 62) :
    ∃ c m', program.runBlock (dialect Extracted.programImage) ⟨.l1089b2, b, m⟩ =
      .jump ⟨.l108bb1, c, m'⟩ ∧
      c[4] = b[4] ∧ (∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → c[i] = b[i]) ∧
      RamWriteFrame m m' [⟨(sp - 168).toNat, 120⟩] ∧
      Atom.All Extracted.programImage c m' (subtractAtoms sp dst p) := by
  have q64 : b[4].get 64 = sp - 168 := congrArg (Value.get 64) rsp
  have dst64 : b[3].get 64 = dst := congrArg (Value.get 64) dstReg
  have count64 : b[1].get 64 = (v1089a7 p).setWidth 64 := congrArg (Value.get 64) count
  have cnt8 : shiftCount 64 ((v1089a7 p).setWidth 8) = 64 - p.shift.toNat := by
    simp only [shiftCount, ite_true, BitVec.toNat_setWidth, countNat p bound]
    omega
  have cf : p.shift.toNat < 64 := by omega
  refine ⟨?_, ?_, ?run, ?post⟩
  case run =>
    cfg_eval [b_l1089b2, b_l1089b2_1, b_l1089b2_2, b_l1089b2_3, b_l1089b2_4, b_l1089b2_5, b_l1089b2_6, q64, dst64, count64, ptr, inv, h0, h1, h2, h3, h4,
      sign, shift, r0, r1, r2, r3, cnt8, cf, not_true_eq_false, ite_false]
    segment_words [q64, dst64, count64, ptr, inv, h0, h1, h2, h3, h4,
      sign, shift, r0, r1, r2, r3, cnt8, cf, not_true_eq_false, ite_false]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; first | slot_guard using code_l1089b2 | assumption)
    try rfl
  case post =>
    refine ⟨rfl, ?_, ?_, ?_⟩
    · intro ⟨i, hi⟩ h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl <;> rfl
    · slot_state region
    · simp only [subtractAtoms, beforeSelect, List.dropLast, refine_layout]
      segment_words [h0, h1, h2, h3, h4, sign, shift, r0, r1, r2, r3]
      repeat' apply And.intro
      all_goals first | exact count | rfl | trivial | skip
      all_goals try (apply congrArg (Value.mk 64))
      all_goals simp (config := { failIfUnchanged := false }) only [v108b4c, v108b3b, v108a7e, v108ade,
        v108b25, v108b44, v108b1c, v108b4f, v108aae, v108a39,
        v1089cc, v1089d0, v1089d3, v1089ec, v1089fd, v108a0f, v108a21, v108a24, v108a2c, v108a2f, adcTop,
        v108a3c, v108a42, v108a45, v108a4d, v108a50, v108a5e, v108a6f, v108a77, v108a7a,
        v108a81, v108a87, v108a8a, v108a8d, v108a90, v108a93, v108a9f, v108aa7, v108aaa,
        v108ab1, v108ab7, v108aba, v108abd, v108ac0, v108ac3, v108acf, v108ad7, v108ada,
        v108ae1, v108ae7, v108aea, v108af0, v108af3, v108af6, v108b01, v108b09, v108b0c,
        v108b12, v108b15, v108b18, v108b1f, v108b22,
        mulResult_fst, K256.Proofs.Common.Invert.LinearCombination.addSpec_low,
        adcValue, sbbValue, negCarry,
        BitVec.reduceSetWidth,
        apply_ite (BitVec.setWidth 64 : BitVec 8 → Word),
        apply_ite (BitVec.setWidth 64 : BitVec 32 → Word),
        apply_ite (BitVec.setWidth 32 : BitVec 8 → BitVec 32),
        setWidth_mergeGPR8]
      all_goals first | lifted_word_eq [] | rfl | skip
      all_goals simp only [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64),
        BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64),
        BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32), BitVec.setWidth_eq]

private def scratchRegion (sp : Word) : MemoryRegion := ⟨(sp - 168).toNat, 120⟩

private theorem preserveTail {a b c : Registers} {o m m' : Ram} {sp dst ret : Word}
    (fr : CalleeFrame a o sp dst ret 304 33) (tf : TailFrame a o sp dst ret b m)
    (window : Writable Extracted.programImage m (sp - 168) 120) (high : sp.toNat + 24 ≤ 2^32)
    (rsp : c[4] = b[4]) (controls : ∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → c[i] = b[i])
    (writes : RamWriteFrame m m' [scratchRegion sp]) : TailFrame a o sp dst ret c m' := by
  have room := fr.depthBound
  have qNat : (sp - 168).toNat = sp.toNat - 168 := subNat (d := 168) (by omega)
  have outerNat : (sp - 304).toNat = sp.toNat - 304 := subNat room
  have keepBelow (k : Nat) (hk : k ≤ 48) : Outside [scratchRegion sp] (sp - BitVec.ofNat 64 k) 8 := by
    have kn := subNat (show k ≤ sp.toNat by omega)
    simp only [Outside, scratchRegion, List.mem_singleton, forall_eq, qNat, kn]
    omega
  have keepAbove (k : Nat) (hk : k ≤ 16) : Outside [scratchRegion sp] (sp + BitVec.ofNat 64 k) 8 := by
    have kn : (sp + BitVec.ofNat 64 k).toNat = sp.toNat + k := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : k < 2^64),
        Nat.mod_eq_of_lt (by omega)]
    simp only [Outside, scratchRegion, List.mem_singleton, forall_eq, qNat, kn]
    omega
  refine ⟨rsp.trans tf.rsp, fun i hi => (controls i hi).trans (tf.controls i hi),
    ?_, tf.frame.trans writes ?_, ?_, ?_, ?_, ?_⟩
  · have saved := tf.saved
    simp only [refine_layout] at saved ⊢
    obtain ⟨h5, h15, h14, h13, h12, h3⟩ := saved
    refine ⟨(writes.memLoad_eq (keepBelow 8 (by decide))).trans h5,
      (writes.memLoad_eq (keepBelow 16 (by decide))).trans h15,
      (writes.memLoad_eq (keepBelow 24 (by decide))).trans h14,
      (writes.memLoad_eq (keepBelow 32 (by decide))).trans h13,
      (writes.memLoad_eq (keepBelow 40 (by decide))).trans h12,
      (writes.memLoad_eq (keepBelow 48 (by decide))).trans h3⟩
  · intro r hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨_, List.mem_cons_self, ?_⟩
    simp only [scratchRegion, outerNat, qNat]
    omega
  · have h := keepAbove 0 (by decide)
    rw [show sp + BitVec.ofNat 64 0 = sp by simp] at h
    exact (writes.memLoad_eq h).trans tf.returned
  · exact (writes.memLoad_eq (keepAbove 8 (by decide))).trans tf.modPtr
  · exact (writes.memLoad_eq (keepAbove 16 (by decide))).trans tf.inverse
  · exact Generate.Generator.Affine.Invert.Core.stackImage window writes tf.image

set_option maxRecDepth 4096 in
set_option maxHeartbeats 600000 in
private theorem signCheck {b : Registers} {m : Ram} {sp dst : Word} {p : Inputs}
    (rsp : b[4] = ⟨64, sp - 168⟩) (win : Writable Extracted.programImage m (sp - 168) 120)
    (room : 304 ≤ sp.toNat) (high : sp.toNat + 24 ≤ 2^32)
    (pos : 0 < p.shift.toNat) (atoms : Atom.All Extracted.programImage b m (subtractAtoms sp dst p)) :
    ∃ c m', program.runBlock (dialect Extracted.programImage) ⟨.l108bb1, b, m⟩ =
      .jump ⟨.l108bc1, c, m'⟩ ∧
      c[4] = b[4] ∧ (∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → c[i] = b[i]) ∧
      RamWriteFrame m m' [scratchRegion sp] ∧
      Atom.All Extracted.programImage c m' (beforeSelect sp dst p) := by
  have q64 : b[4].get 64 = sp - 168 := congrArg (Value.get 64) rsp
  have atomSplit := atoms
  simp only [subtractAtoms, beforeSelect, List.dropLast, refine_layout] at atomSplit
  lifted_inputs atomSplit
  have nonzero : p.shift ≠ 0 := by intro h; rw [h] at pos; exact (Nat.lt_irrefl 0) pos
  have shift32 : memLoad m (sp - 0x64) 32 = p.shift := by
    simpa only [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq] using input20
  refine ⟨?_, memStore m (sp - 154) (b[9].get 8), ?run, ?post⟩
  case run =>
    have lowEq : (b[9].get 64).setWidth 8 = b[9].get 8 := BitVec.setWidth_setWidth_of_le _ (by decide)
    cfg_eval [b_l108bb1, q64, shift32, lowEq, nonzero, ite_false]
    segment_words [q64, shift32, lowEq, nonzero, ite_false]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; first | slot_guard using code_l108bb1 | assumption)
    try rfl
  case post =>
    refine ⟨rfl, ?_, ?_, ?_⟩
    · intro ⟨i, hi⟩ h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl <;> rfl
    · unfold scratchRegion
      slot_state region
    · simp only [Bool.not_eq_true', decide_eq_false_iff_not] at input4 input5 input7 input8 input9 input13 input28
      simp only [beforeSelect, refine_layout]
      segment_words [input9, input15, input16, input17, input18, input19, input20,
        input21, input22, input23, input24, input25, input26, input27, input28]
      repeat' apply And.intro
      all_goals first | rfl | assumption

set_option maxRecDepth 4096 in
theorem subtract {a b : Registers} {m m' : Ram} {sp dst ret : Word} {p : Inputs}
    (fr : CalleeFrame a m sp dst ret 304 33)
    (params : p.params = orderParameters)
    (tf : TailFrame a m sp dst ret b m')
    (stackArgs : Readable m (sp + 8) 16)
    (argHigh : sp.toNat + 24 ≤ 2^32)
    (argApart : dst.toNat + 33 ≤ sp.toNat ∨ sp.toNat + 24 ≤ dst.toNat)
    (pos : 0 < p.shift.toNat) (bound : p.shift.toNat ≤ 62)
    (atoms : Atom.All Extracted.programImage b m' (afterLinear sp dst p)) :
    ∃ c m'', Reaches .l10899e b m' .l108bc1 c m'' ∧ TailFrame a m sp dst ret c m'' ∧
      Atom.All Extracted.programImage c m'' (beforeSelect sp dst p) := by
  have _ := argApart
  have room := fr.depthBound
  have stack := fr.stack.of_frame tf.frame
  have win : Writable Extracted.programImage m' (sp - 168) 120 := by slot_state region
  have args : Readable m' (sp + 8) 16 := stackArgs.of_frame tf.frame
  have rsp := tf.rsp
  simp only [afterLinear, refine_layout] at atoms
  obtain ⟨shift, dstReg, h0, h1, h2, h3, h4, sign⟩ := atoms
  obtain ⟨c, run0, rsp0, dst0, cnt, ctl0⟩ := shiftCheck rsp shift win pos bound
  let m0 := memStore m' (sp - 168 + 68) p.shift
  change program.runBlock _ _ = .jump ⟨.l1089b2, c, m0⟩ at run0
  have frame0 : RamWriteFrame m' m0 [scratchRegion sp] := by
    dsimp only [m0, scratchRegion]
    slot_state region
  have tf0 := preserveTail fr tf win argHigh rsp0 ctl0 frame0
  have win0 := win.of_frame frame0
  have args0 := args.of_frame frame0
  have table := Generate.Generator.Multiply.Split.parameterAt tf0.image
    (p := 0x2021a0) (x := Standards.SECG.DomainParameters.Secp256k1.domain.n) (by decide +kernel)
  have tableWord (i : Fin 4) :
      memLoad m0 (wordAddr 0x2021a0 64 i) 64 = p.params.modulusWords[i] := by
    rw [params]
    exact table.words i i.isLt
  have readable (i : Fin 4) : Readable m0 (wordAddr 0x2021a0 64 i) 8 := by
    apply table.readable.sub
    all_goals have cases4 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    all_goals rcases cases4 with rfl|rfl|rfl|rfl <;> decide
  obtain ⟨d, m1, run1, rsp1, ctl1, frame1, atoms1⟩ :=
    subtractBlock tf0.rsp (dst0.trans dstReg) cnt win0 args0 (readable 0) (readable 1) (readable 2) (readable 3)
      (table.apart win0 (by decide)).symm
      (by dsimp only [m0]; segment_words [h0])
      (by dsimp only [m0]; segment_words [h1])
      (by dsimp only [m0]; segment_words [h2])
      (by dsimp only [m0]; segment_words [h3])
      (by dsimp only [m0]; segment_words [h4])
      (by dsimp only [m0]; segment_words [sign])
      (by dsimp only [m0]; segment_words [])
      tf0.modPtr (by rw [params, order_inverseWord]; exact tf0.inverse)
      (tableWord 0) (tableWord 1) (tableWord 2) (tableWord 3) room argHigh pos bound
  have tf1 := preserveTail fr tf0 win0 argHigh rsp1 ctl1 frame1
  have win1 := win0.of_frame frame1
  obtain ⟨e, m2, run2, rsp2, ctl2, frame2, atoms2⟩ := signCheck tf1.rsp win1 room argHigh pos atoms1
  exact ⟨e, m2, (jump run0).trans ((jump run1).trans (jump run2)),
    preserveTail fr tf1 win1 argHigh rsp2 ctl2 frame2, atoms2⟩

end K256.Proofs.Verify.Core.Scalars.Inverse.ModularShift
