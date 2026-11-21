import K256.Proofs.Verify.Core.Scalars.Inverse.Batch.Update.State
import K256.Proofs.Verify.LIR.Generated.Values
import K256.Proofs.Verify.Choice
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Verify.Core.Scalars.Inverse.Batch

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Verify.LIR
open Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Affine.Invert.Core (CalleeResult signedAt)
open Generate.Generator.Affine.Invert.Core.Batch (signedAt_of_frame signedAt_of_copy)
open Generate.Generator.Affine.Invert
open SafeGcd.Batch (Words)

private structure ModularCall (c : Registers) (q : Ram) (x dst ret u v : Word) (k : Nat) : Prop where
  rsp : c[4] = ⟨64, x - 24⟩
  dstReg : c[7] = ⟨64, x + dst⟩
  left : c[6].get 64 = x + 96
  right : c[2].get 64 = x + 136
  coeffLeft : c[1].get 64 = u
  coeffRight : c[8].get 64 = v
  shift : c[9].get 32 = BitVec.ofNat 32 k
  returned : memLoad q (x - 24) 64 = ret
  ptr : memLoad q (x - 16) 64 = 0x2021a0
  inverse : memLoad q (x - 8) 64 = 0xb4f20099aa774ec1

private def pushWrites (x : Word) : List MemoryRegion :=
  [⟨(x - 24).toNat, 24⟩, ⟨(x + 7).toNat, 1⟩]

private def copyWrites (x : Word) : List MemoryRegion :=
  pushWrites x ++ [⟨(x + 8).toNat, 80⟩]

private theorem shiftWord (k : Nat) :
    (((BitVec.ofNat 64 k).setWidth 32).setWidth 64).setWidth 32 = BitVec.ofNat 32 k := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_ofNat_of_le (by decide), BitVec.setWidth_eq]

local macro "push_frame" : tactic => `(tactic| (
  repeat' apply RamWriteFrame.memStore
  all_goals first | exact RamWriteFrame.refl _ _ | (
    simp only [InRegions, copyWrites, pushWrites, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left, InRegion]
    bv_omega)))

local macro "shift_controls" : tactic => `(tactic| (
  intro ⟨i, hi⟩ hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with he | he | he | he <;> subst i <;> rfl))

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 8192 in
private theorem firstModularCall {a : Registers} {m : Ram} {x : Word} {k : Nat} {w : Words}
    (lo : 24 ≤ x.toNat) (win : Writable Extracted.programImage m (x - 24) 368)
    (rsp : a[4] = ⟨64, x⟩) (shift : a[5] = ⟨64, BitVec.ofNat 64 k⟩)
    (rows : Rows a w)
    (ptr : memLoad m (x + 88) 64 = 0x2021a0)
    (inverse : memLoad m (x + 296) 64 = 0xb4f20099aa774ec1) :
    ∃ c q, program.runBlock (dialect Extracted.programImage) ⟨.l109657, a, m⟩ =
        .call ⟨.l108980, c, q⟩ (Verify.resumeAt .l10971c 0x10971c) ∧
      ModularCall c q x 176 0x10971c w.u w.v k ∧
      c[5] = a[5] ∧ c[12] = a[12] ∧ c[13] = a[13] ∧ c[14] = a[14] ∧
      c[3] = ⟨64, 0x2021a0⟩ ∧ c[15] = ⟨64, 0xb4f20099aa774ec1⟩ ∧
      Controls a c ∧ RamWriteFrame m q (copyWrites x) ∧
      (∀ i < 5, memLoad q (wordAddr (x + 8) 64 i) 64 = memLoad m (wordAddr (x + 176) 64 i) 64) ∧
      (∀ i < 5, memLoad q (wordAddr (x + 48) 64 i) 64 = memLoad m (wordAddr (x + 216) 64 i) 64) := by
  have hi := win.readable.low
  have upper : Writable Extracted.programImage m x 344 := win.sub (by bv_omega) (by bv_omega)
  have pushes : Writable Extracted.programImage m (x - 24) 24 := win.sub (by bv_omega) (by bv_omega)
  have shiftGet := congrArg (Value.get 64) shift
  have stack : a[4].get 64 = x := congrArg (Value.get 64) rsp
  refine ⟨?_, ?_, ?run, ?post⟩
  case run =>
    have uGet := congrArg (Value.get 64) rows.u
    have vGet := congrArg (Value.get 64) rows.v
    cfg_eval [b_l109657, b_l109657_1, stack, shiftGet, uGet, vGet]
    segment_words [ptr, inverse]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l109657)
    rfl
  case post =>
    refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, shiftWord k, ?_, ?_, ?_⟩,
      rfl, rfl, rfl, rfl, rfl, rfl, by shift_controls, by push_frame, ?_, ?_⟩
    all_goals try (solve | simp (disch := store_disch) only [memLoad_memStore_same, memLoad_memStore_of_rangeApart])
    all_goals
      intro i hi
      have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
      rcases cases with rfl|rfl|rfl|rfl|rfl <;>
        simp only [wordAddr, Nat.reduceMul, Nat.reduceDiv, BitVec.ofNat_eq_ofNat, Lift.reduceAddOffset] <;>
        segment_words [] <;> rfl

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
private theorem secondModularCall {a : Registers} {m : Ram} {x u v : Word} {k : Nat}
    (lo : 24 ≤ x.toNat) (win : Writable Extracted.programImage m (x - 24) 368)
    (rsp : a[4] = ⟨64, x - 16⟩) (shift : a[5] = ⟨64, BitVec.ofNat 64 k⟩)
    (coeffLeft : a[13] = ⟨64, u⟩) (coeffRight : a[14] = ⟨64, v⟩)
    (ptr : a[3] = ⟨64, 0x2021a0⟩) (inverse : a[15] = ⟨64, 0xb4f20099aa774ec1⟩) :
    ∃ c q, program.runBlock (dialect Extracted.programImage) ⟨.l10971c, a, m⟩ =
        .call ⟨.l108980, c, q⟩ (Verify.resumeAt .l109763 0x109763) ∧
      ModularCall c q x 216 0x109763 u v k ∧
      c[5] = a[5] ∧ c[12] = a[12] ∧ Controls a c ∧ RamWriteFrame m q (pushWrites x) := by
  have hi := win.readable.low
  have upper : Writable Extracted.programImage m x 344 := win.sub (by bv_omega) (by bv_omega)
  have pushes : Writable Extracted.programImage m (x - 24) 24 := win.sub (by bv_omega) (by bv_omega)
  have shiftGet := congrArg (Value.get 64) shift
  have stack : a[4].get 64 = x - 16 := congrArg (Value.get 64) rsp
  refine ⟨?_, ?_, ?run, ?post⟩
  case run =>
    have uGet := congrArg (Value.get 64) coeffLeft
    have vGet := congrArg (Value.get 64) coeffRight
    have ptrGet := congrArg (Value.get 64) ptr
    have invGet := congrArg (Value.get 64) inverse
    cfg_eval [b_l10971c, stack, shiftGet, uGet, vGet, ptrGet, invGet,
      show x - 16 + 16 = x by bv_omega]
    segment_words []
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l10971c)
    rfl
  case post =>
    refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, shiftWord k, ?_, ?_, ?_⟩, rfl, rfl,
      by shift_controls, by push_frame⟩
    all_goals simp (disch := store_disch) only [memLoad_memStore_same, memLoad_memStore_of_rangeApart]

private theorem runModularCall (shift : ModularShift) {a c : Registers} {m q : Ram}
    {sp ret dst u v : Word} {s k : Nat} {d e : Int}
    (h : Entry a m sp s) (full : RamWriteFrame m q [⟨(sp - 720).toNat,720⟩])
    (call : ModularCall c q (base sp) dst ret u v k) (df : c[22] = ⟨1,0⟩)
    (slot : 176 ≤ dst.toNat ∧ dst.toNat ≤ 216) (retLow : ret.toNat < 2^32)
    (sd : signedAt q (base sp + 96) d) (se : signedAt q (base sp + 136) e)
    (pos : 0 < k) (small : k ≤ 62) (bound : (d*u.toInt + e*v.toInt).natAbs < 2^k * domain.n) :
    ∃ out r, program.Exec (dialect Extracted.programImage) ⟨⟨.l108980,c,q⟩,[]⟩ out ∧
      CalleeResult c q (base sp - 24) (base sp + dst) ret 304 33 out ∧
      signedAt out.store (base sp + dst) r ∧ r.natAbs < domain.n ∧
      ((2:Int)^k * r) % domain.n = (d*u.toInt + e*v.toInt) % domain.n := by
  have lo := h.depthBound
  have hi := h.high
  have win := h.stack.of_frame full
  have dstRoom : dst.toNat + 33 ≤ 392 := by omega
  have fr := shiftFrame (depth := 304) h full (Or.inr rfl) (by decide) dstRoom
    call.rsp call.dstReg df call.returned retLow
  refine shift fr ⟨?_, ?_, call.coeffLeft, call.coeffRight⟩ call.shift pos small
    (win.readable.sub ?_ ?_) ?_ (Or.inr ?_) ?_ ?_ bound
  · rw [call.left]
    exact shiftSource win lo hi (by decide) (by decide) (by change 96+33 ≤ dst.toNat; omega) dstRoom sd
  · rw [call.right]
    exact shiftSource win lo hi (by decide) (by decide) (by change 136+33 ≤ dst.toNat; omega) dstRoom se
  all_goals first | (rw [show base sp - 24 + 8 = base sp - 16 by bv_omega]; exact call.ptr)
                  | (rw [show base sp - 24 + 16 = base sp - 8 by bv_omega]; exact call.inverse)
                  | (obtain ⟨_, _⟩ := slot; unfold base; bv_omega)

local macro "slot_out" : tactic => `(tactic| (
  simp only [Outside, linearWrites, modularWrites, copyWrites, pushWrites, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    base, Nat.reduceDiv]
  bv_omega))

local macro "slot_within" : tactic => `(tactic| (
  intro r hr
  simp only [linearWrites, modularWrites, copyWrites, pushWrites, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  repeat' (rcases hr with (rfl | hr))
  all_goals try subst r
  all_goals
    simp only [modularWrites, List.mem_cons, List.not_mem_nil, or_false, exists_eq_left,
      exists_eq_or_imp, base]
    bv_omega))

private theorem rowBound {d e : Int} {u v : Word} {shift : Nat}
    (hd : d.natAbs < domain.n) (he : e.natAbs < domain.n)
    (bound : u.toInt.natAbs + v.toInt.natAbs ≤ 2^shift) :
    (d*u.toInt + e*v.toInt).natAbs < 2^shift * domain.n := by
  rw [Int.mul_comm d, Int.mul_comm e]
  exact SafeGcd.linearCombination_natAbs_lt hd he bound (Nat.two_pow_pos _)

set_option maxHeartbeats 600000 in
theorem modularRows (shift : ModularShift) {a b c : Registers} {m p q : Ram} {sp : Word}
    {s n : Nat} {d e : Int} {w : Words} (h : Entry a m sp s)
    (state : LoopState a m sp s n b p d e) (more : n < 591)
    (linear : LinearRows b p sp s n w c q)
    (bound : (SafeGcd.Batch.matrix w).Bounded (2^(count n))) :
    ∃ c' q' d' e', Reaches .l109657 c q .l109763 c' q' ∧
      ModularRows b p sp s n w c' q' d' e' ∧
      d'.natAbs < domain.n ∧ e'.natAbs < domain.n ∧
      ((2:Int)^(count n)*d') % domain.n = (d*w.u.toInt + e*w.v.toInt) % domain.n ∧
      ((2:Int)^(count n)*e') % domain.n = (d*w.q.toInt + e*w.r.toInt) % domain.n := by
  have lo := h.depthBound
  have hi := h.high
  have pos : 0 < count n := by unfold count; omega
  have small : count n ≤ 62 := Nat.min_le_left ..
  have full₀ := state.frame.trans linear.frame (by slot_within)
  have win := h.stack.of_frame full₀
  obtain ⟨c₁,m₁,step₁,args₁,bp₁,delta₁,left₁,right₁,ptr₁,inv₁,ctrl₁,writes₁,copyF,copyG⟩ :=
    firstModularCall (by unfold base; bv_omega)
      (win.sub (by unfold base; bv_omega) (by unfold base; bv_omega))
      linear.rsp linear.shift linear.rows
      ((linear.frame.memLoad_eq (by slot_out)).trans state.modulusPtr)
      ((linear.frame.memLoad_eq (by slot_out)).trans state.modulusInverse)
  have full₁ := full₀.trans writes₁ (by slot_within)
  have d₀ := signedAt_of_frame state.dValue linear.frame (by slot_out)
  have e₀ := signedAt_of_frame state.eValue linear.frame (by slot_out)
  have d₁ := signedAt_of_frame d₀ writes₁ (by slot_out)
  have e₁ := signedAt_of_frame e₀ writes₁ (by slot_out)
  have df := ((linear.controls 22 (by decide)).trans (state.kept 22 (by decide))).trans h.df
  obtain ⟨out₁,r₁,run₁,res₁,value₁,bound₁,congr₁⟩ :=
    runModularCall shift h full₁ args₁ ((ctrl₁ 22 (by decide)).trans df) (by decide) (by decide)
      d₁ e₁ pos small (rowBound state.dBound state.eBound bound.1)
  have reach₁ := Verify.reachesOfCall step₁ run₁ res₁.returned
  have fullMid := full₁.trans res₁.frame (by slot_within)
  have rspMid : out₁.values[4] = ⟨64, base sp - 16⟩ := by rw [res₁.rsp]; congr 1 <;> bv_omega
  have preserved (i : Fin Reg.count) (mem : i.val ∈ [3,5,12,13,14,15]) {v : Word}
      (vEq : c₁[i] = ⟨64,v⟩) : out₁.values[i] = ⟨64,v⟩ :=
    (res₁.kept i mem (by rw [vEq])).trans vEq
  have winMid := h.stack.of_frame fullMid
  obtain ⟨c₂,m₂,step₂,args₂,bp₂,delta₂,ctrl₂,writes₂⟩ :=
    secondModularCall (by unfold base; bv_omega)
      (winMid.sub (by unfold base; bv_omega) (by unfold base; bv_omega)) rspMid
      (preserved 5 (by decide) (bp₁.trans linear.shift))
      (preserved 13 (by decide) (left₁.trans linear.rows.q))
      (preserved 14 (by decide) (right₁.trans linear.rows.r))
      (preserved 3 (by decide) ptr₁) (preserved 15 (by decide) inv₁)
  have full₂ := fullMid.trans writes₂ (by slot_within)
  have controlsMid : Controls b c₂ := fun i hi => (ctrl₂ i hi).trans ((res₁.controls i hi).trans
    ((ctrl₁ i hi).trans (linear.controls i hi)))
  obtain ⟨out₂,r₂,run₂,res₂,value₂,bound₂,congr₂⟩ := runModularCall shift h full₂ args₂
    (((controlsMid 22 (by decide)).trans (state.kept 22 (by decide))).trans h.df)
    (by decide) (by decide)
    (signedAt_of_frame (signedAt_of_frame d₁ res₁.frame (by slot_out)) writes₂ (by slot_out))
    (signedAt_of_frame (signedAt_of_frame e₁ res₁.frame (by slot_out)) writes₂ (by slot_out))
    pos small (rowBound state.dBound state.eBound bound.2)
  have reach₂ := Verify.reachesOfCall step₂ run₂ res₂.returned
  have keep₂ (i : Fin Reg.count) (mem : i.val ∈ [3,5,12,13,14,15]) {v : Word}
      (vEq : c₂[i] = ⟨64,v⟩) : out₂.values[i] = ⟨64,v⟩ :=
    (res₂.kept i mem (by rw [vEq])).trans vEq
  refine ⟨_,_,_,_,reach₁.trans reach₂, ?_, bound₁,bound₂,congr₁,congr₂⟩
  refine ⟨?_, keep₂ 5 (by decide) (bp₂.trans (preserved 5 (by decide) (bp₁.trans linear.shift))),
    keep₂ 12 (by decide) (delta₂.trans (preserved 12 (by decide) (delta₁.trans linear.rows.delta))),
    fun i hi => (res₂.controls i hi).trans (controlsMid i hi), ?_, ?_, ?_, ?_, value₂, ?_⟩
  · rw [res₂.rsp]; congr 1 <;> bv_omega
  · exact (res₂.frame.memLoad_eq (by slot_out)).trans ((writes₂.memLoad_eq (by slot_out)).trans
      ((res₁.frame.memLoad_eq (by slot_out)).trans ((writes₁.memLoad_eq (by slot_out)).trans linear.remaining)))
  · exact signedAt_of_frame (signedAt_of_frame (signedAt_of_frame
      (signedAt_of_copy linear.fValue copyF) res₁.frame (by slot_out)) writes₂ (by slot_out)) res₂.frame (by slot_out)
  · exact signedAt_of_frame (signedAt_of_frame (signedAt_of_frame
      (signedAt_of_copy linear.gValue copyG) res₁.frame (by slot_out)) writes₂ (by slot_out)) res₂.frame (by slot_out)
  · exact signedAt_of_frame (signedAt_of_frame value₁ writes₂ (by slot_out)) res₂.frame (by slot_out)
  · exact (((((RamWriteFrame.refl p (modularWrites sp)).trans linear.frame (by slot_within)).trans
      writes₁ (by slot_within)).trans res₁.frame (by slot_within)).trans writes₂ (by slot_within)).trans
      res₂.frame (by slot_within)

end K256.Proofs.Verify.Core.Scalars.Inverse.Batch
