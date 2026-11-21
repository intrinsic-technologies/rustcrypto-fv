import K256.Proofs.Generate.Generator.Affine.Invert.Core.Batch.Update.Frame
import K256.Proofs.Generate.Generator.Sample.Decide.Nonzero.Resume.Flag
import K256.Proofs.Generate.LIR.Fn108e30
import K256.Proofs.Generate.Generator.Affine.Invert.Core.ModularShift

namespace K256.Proofs.Generate.Generator.Affine.Invert.Core.Batch

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Generate.LIR

private structure ModularCall (c : Registers) (q : Ram) (x dst ret u v : Word) (k : Nat) : Prop where
  rsp : c[4] = ⟨64, x - 24⟩
  dstReg : c[7] = ⟨64, x + dst⟩
  left : c[6].get 64 = x + 208
  right : c[2].get 64 = x + 248
  uReg : c[1].get 64 = u
  vReg : c[8].get 64 = v
  shift : c[9].get 32 = BitVec.ofNat 32 k
  returned : memLoad q (x - 24) 64 = ret
  ptr : memLoad q (x - 16) 64 = 0x2021e0
  inverse : memLoad q (x - 8) 64 = 0x27c7f6e22ddacacf

private def pushWrites (x : Word) : List MemoryRegion :=
  [⟨(x - 24).toNat, 24⟩, ⟨(x + 7).toNat, 1⟩]

private def copyWrites (x : Word) : List MemoryRegion :=
  pushWrites x ++ [⟨(x + 120).toNat, 40⟩, ⟨(x + 168).toNat, 40⟩]

private theorem shiftWord {k : Nat} (small : k ≤ 62) :
    ((BitVec.ofNat 64 k).setWidth 32).setWidth 64 = BitVec.ofNat 64 k := by
  rw [BitVec.setWidth_ofNat_of_le (by decide), BitVec.setWidth_ofNat_of_le_of_lt (by decide) (by omega)]

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
private theorem firstModularCall {a : Registers} {m : Ram} {x u v : Word} {k : Nat}
    (lo : 24 ≤ x.toNat) (win : Writable Extracted.programImage m (x - 24) 376)
    (rsp : a[4] = ⟨64, x⟩) (second : a[12] = ⟨64, x + 56⟩)
    (shift : a[14] = ⟨64, BitVec.ofNat 64 k⟩) (small : k ≤ 62)
    (uReg : a[15] = ⟨64, u⟩) (vReg : a[3] = ⟨64, v⟩)
    (ptr : memLoad m (x + 160) 64 = 0x2021e0)
    (inverse : memLoad m (x + 328) 64 = 0x27c7f6e22ddacacf) :
    ∃ c q, program.runBlock (dialect Extracted.programImage) ⟨.l109036, a, m⟩ =
        .call ⟨.l108980, c, q⟩ (callFrame .l109107 0x109107) ∧
      ModularCall c q x 16 0x109107 u v k ∧
      c[5] = a[5] ∧ c[12] = a[12] ∧ c[15] = ⟨64, BitVec.ofNat 64 k⟩ ∧
      c[3] = ⟨64, 0x2021e0⟩ ∧ c[14] = ⟨64, 0x27c7f6e22ddacacf⟩ ∧
      Controls a c ∧ RamWriteFrame m q (copyWrites x) ∧
      (∀ i < 5, memLoad q (wordAddr (x+120) 64 i) 64 = memLoad m (wordAddr (x+16) 64 i) 64) ∧
      (∀ i < 5, memLoad q (wordAddr (x+168) 64 i) 64 = memLoad m (wordAddr (x+56) 64 i) 64) := by
  have hi := win.readable.low
  have stack : a[4].get 64 = x := congrArg (Value.get 64) rsp
  have sec : a[12].get 64 = x + 56 := congrArg (Value.get 64) second
  refine ⟨?_, ?_, ?run, ?post⟩
  case run =>
    arithmetic_segment using code_l109036 [stack, sec, rsp, second, shift, ptr, inverse,
      uReg, vReg]
  case post =>
    refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩, rfl, second.symm,
      congrArg (Value.mk 64) (shiftWord small), rfl, rfl, by shift_controls, by push_frame, ?_, ?_⟩
    · change (((BitVec.ofNat 64 k).setWidth 32).setWidth 64).setWidth 32 = _
      rw [shiftWord small, BitVec.setWidth_ofNat_of_le (by decide)]
    all_goals try (solve | simp (disch := store_disch) only [memLoad_memStore_same, memLoad_memStore_of_rangeApart])
    all_goals
      intro i hi
      have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
      rcases cases with rfl|rfl|rfl|rfl|rfl <;>
        simp only [wordAddr, Nat.reduceMul, Nat.reduceDiv, BitVec.ofNat_eq_ofNat, Lift.reduceAddOffset] <;>
        segment_words [] <;> rfl

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 8192 in
private theorem secondModularCall {a : Registers} {m : Ram} {x u v : Word} {k : Nat}
    (lo : 24 ≤ x.toNat) (win : Writable Extracted.programImage m (x - 24) 376)
    (rsp : a[4] = ⟨64, x - 16⟩) (second : a[12] = ⟨64, x + 56⟩)
    (shift : a[15] = ⟨64, BitVec.ofNat 64 k⟩) (small : k ≤ 62)
    (uMem : memLoad m (x + 8) 64 = u) (vMem : memLoad m (x + 104) 64 = v)
    (ptr : a[3] = ⟨64, 0x2021e0⟩) (inverse : a[14] = ⟨64, 0x27c7f6e22ddacacf⟩) :
    ∃ c q, program.runBlock (dialect Extracted.programImage) ⟨.l109107, a, m⟩ =
        .call ⟨.l108980, c, q⟩ (callFrame .l10914e 0x10914e) ∧
      ModularCall c q x 56 0x10914e u v k ∧
      c[5] = a[5] ∧ c[12] = a[12] ∧ c[15] = ⟨64, BitVec.ofNat 64 k⟩ ∧
      c[14] = ⟨64, x + 16⟩ ∧ Controls a c ∧ RamWriteFrame m q (pushWrites x) := by
  have hi := win.readable.low
  have stack : a[4].get 64 = x - 16 := congrArg (Value.get 64) rsp
  have sec : a[12].get 64 = x + 56 := congrArg (Value.get 64) second
  refine ⟨?_, ?_, ?run, ?post⟩
  case run =>
    arithmetic_segment using code_l109107 [stack, sec, rsp, second, shift, ptr, inverse,
      uMem, vMem, show x - 16 + 16 = x by bv_omega]
  case post =>
    refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩, rfl, second.symm, rfl, rfl,
      by shift_controls, by push_frame⟩
    · change (((BitVec.ofNat 64 k).setWidth 32).setWidth 64).setWidth 32 = _
      rw [shiftWord small, BitVec.setWidth_ofNat_of_le (by decide)]
    all_goals try (solve | simp (disch := store_disch) only [memLoad_memStore_same, memLoad_memStore_of_rangeApart])

open SafeGcd.Batch (Words)

variable {a b : Registers} {m p : Ram} {sp : Word} {z : Fin modulus} {w : Vector Word 4}

private theorem runModularCall {c : Registers} {q : Ram} {ret dst u v : Word} {k : Nat} {d e : Int}
    (h : Entry a m sp z w) (full : RamWriteFrame m q [⟨(sp - 736).toNat,736⟩])
    (call : ModularCall c q (base sp) dst ret u v k) (df : c[22] = ⟨1,0⟩)
    (slot : dst.toNat ≤ 56) (retLow : ret.toNat < 2^32)
    (sd : signedAt q (base sp + 208) d) (se : signedAt q (base sp + 248) e)
    (pos : 0 < k) (small : k ≤ 62) (bound : (d*u.toInt + e*v.toInt).natAbs < 2^k * modulus) :
    ∃ out r, CalleeExec .l108980 c q out ∧
      CalleeResult c q (base sp - 24) (base sp + dst) ret 304 33 out ∧
      signedAt out.store (base sp + dst) r ∧ r.natAbs < modulus ∧
      ((2:Int)^k * r) % modulus = (d*u.toInt + e*v.toInt) % modulus := by
  have lo := h.low
  have hi := h.high
  have win := h.stack.of_frame full
  have fr := shiftFrame (depth := 304) h full (Or.inr rfl) (by decide) (by omega)
    call.rsp call.dstReg df call.returned retLow
  refine Core.modularShift fr ⟨?_, ?_, call.uReg, call.vReg⟩ call.shift pos small
    (win.readable.sub ?_ ?_) ?_ (Or.inr ?_) ?_ ?_ bound
  · rw [call.left]
    exact shiftSource win lo hi (by decide) (by decide) (by change dst.toNat + 33 ≤ 208; omega) sd
  · rw [call.right]
    exact shiftSource win lo hi (by decide) (by decide) (by change dst.toNat + 33 ≤ 248; omega) se
  all_goals first | (rw [show base sp - 24 + 8 = base sp - 16 by bv_omega]; exact call.ptr)
                  | (rw [show base sp - 24 + 16 = base sp - 8 by bv_omega]; exact call.inverse)
                  | (unfold base; bv_omega)

local macro "slot_out" : tactic => `(tactic|
  (simp only [Outside, linearWrites, modularWrites, copyWrites, pushWrites, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    base, Nat.reduceDiv]
   bv_omega))

local macro "slot_within" : tactic => `(tactic|
  (intro r hr
   simp only [linearWrites, modularWrites, copyWrites, pushWrites, List.cons_append,
     List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
   repeat' (rcases hr with (rfl | hr))
   all_goals try subst r
   all_goals
     simp only [modularWrites, List.mem_cons, List.not_mem_nil, or_false, exists_eq_left,
       exists_eq_or_imp, base]
     bv_omega))

theorem modularRows (h : Entry a m sp z w) {j : Nat} (hj : j < 10) {d e : Int}
    (state : LoopState a m sp z (roundsBefore j) b p d e) {c : Registers} {q : Ram} {s : Words}
    (rows : LinearRows b p sp z j s c q)
    (bound : (SafeGcd.Batch.matrix s).Bounded (2^count j)) :
    ∃ c' q' d' e', Reaches .l109036 c q .l10914e c' q' ∧ ModularRows b p sp z j s c' q' d' e' ∧
      d'.natAbs < modulus ∧ e'.natAbs < modulus ∧
      ((2:Int)^count j * d') % modulus = (d*s.u.toInt + e*s.v.toInt) % modulus ∧
      ((2:Int)^count j * e') % modulus = (d*s.q.toInt + e*s.r.toInt) % modulus := by
  have lo := h.low
  have hi := h.high
  obtain ⟨pos, small, _⟩ := count_spec hj
  have full0 := state.frame.trans rows.frame (by slot_within)
  have win := h.stack.of_frame full0
  obtain ⟨c₁,m₁,step₁,args₁,bp₁,second₁,shift₁,ptr₁,inv₁,ctrl₁,writes₁,copyF,copyG⟩ :=
    firstModularCall (by unfold base; bv_omega) (win.sub (by unfold base; bv_omega) (by unfold base; bv_omega))
      rows.rsp rows.second rows.shift small rows.u rows.v
      ((rows.frame.memLoad_eq (by slot_out)).trans state.modulusPtr)
      ((rows.frame.memLoad_eq (by slot_out)).trans state.modulusInverse)
  have full₁ := full0.trans writes₁ (by slot_within)
  have d₀ := signedAt_of_frame state.dValue rows.frame (by slot_out)
  have e₀ := signedAt_of_frame state.eValue rows.frame (by slot_out)
  have d₁ := signedAt_of_frame d₀ writes₁ (by slot_out)
  have e₁ := signedAt_of_frame e₀ writes₁ (by slot_out)
  have df := ((rows.controls 22 (by decide)).trans (state.kept 22 (by decide))).trans h.df
  obtain ⟨out₁,r₁,run₁,res₁,value₁,bound₁,congr₁⟩ :=
    runModularCall h full₁ args₁ ((ctrl₁ 22 (by decide)).trans df) (by decide) (by decide)
      d₁ e₁ pos small (rowBound state.dBound state.eBound bound.1)
  have reach₁ := Sample.reachesAfterSampleCall step₁ run₁ res₁.returned []
  have fullMid := full₁.trans res₁.frame (by slot_within)
  have rspMid : out₁.values[4] = ⟨64, base sp - 16⟩ := by rw [res₁.rsp]; congr 1 <;> bv_omega
  have secMid := second₁.trans rows.second
  have bpMid := bp₁.trans rows.delta
  have preserved (i : Fin Reg.count) (mem : i.val ∈ [3,5,12,13,14,15]) {v : Word}
      (vEq : c₁[i] = ⟨64,v⟩) := (res₁.kept i mem (by rw [vEq])).trans vEq
  have winMid := h.stack.of_frame fullMid
  obtain ⟨c₂,m₂,step₂,args₂,bp₂,second₂,shift₂,scratch₂,ctrl₂,writes₂⟩ :=
    secondModularCall (by unfold base; bv_omega)
      (winMid.sub (by unfold base; bv_omega) (by unfold base; bv_omega)) rspMid
      (preserved 12 (by decide) secMid) (preserved 15 (by decide) shift₁) small
      ((res₁.frame.memLoad_eq (by slot_out)).trans ((writes₁.memLoad_eq (by slot_out)).trans rows.qWord))
      ((res₁.frame.memLoad_eq (by slot_out)).trans ((writes₁.memLoad_eq (by slot_out)).trans rows.rWord))
      (preserved 3 (by decide) ptr₁) (preserved 14 (by decide) inv₁)
  have full₂ := fullMid.trans writes₂ (by slot_within)
  have controlsMid : Controls b c₂ := fun i hi => (ctrl₂ i hi).trans ((res₁.controls i hi).trans
    ((ctrl₁ i hi).trans (rows.controls i hi)))
  obtain ⟨out₂,r₂,run₂,res₂,value₂,bound₂,congr₂⟩ := runModularCall h full₂ args₂
    (((controlsMid 22 (by decide)).trans (state.kept 22 (by decide))).trans h.df)
    (by decide) (by decide)
    (signedAt_of_frame (signedAt_of_frame d₁ res₁.frame (by slot_out)) writes₂ (by slot_out))
    (signedAt_of_frame (signedAt_of_frame e₁ res₁.frame (by slot_out)) writes₂ (by slot_out))
    pos small (rowBound state.dBound state.eBound bound.2)
  have reach₂ := Sample.reachesAfterSampleCall step₂ run₂ res₂.returned []
  have keep₂ (i : Fin Reg.count) (mem : i.val ∈ [3,5,12,13,14,15]) {v : Word}
      (vEq : c₂[i] = ⟨64,v⟩) := (res₂.kept i mem (by rw [vEq])).trans vEq
  refine ⟨_,_,_,_,reach₁.trans reach₂, ?_, bound₁,bound₂,congr₁,congr₂⟩
  refine ⟨?_,keep₂ 5 (by decide) (bp₂.trans (preserved 5 (by decide) bpMid)),
    keep₂ 12 (by decide) (second₂.trans (preserved 12 (by decide) secMid)),
    keep₂ 14 (by decide) scratch₂, keep₂ 15 (by decide) shift₂, ?_, ?_, ?_, ?_, value₂,
    fun i hi => (res₂.controls i hi).trans (controlsMid i hi), ?_⟩
  · rw [res₂.rsp]; congr 1 <;> bv_omega
  · exact (res₂.frame.memLoad_eq (by slot_out)).trans ((writes₂.memLoad_eq (by slot_out)).trans
      ((res₁.frame.memLoad_eq (by slot_out)).trans ((writes₁.memLoad_eq (by slot_out)).trans rows.remaining)))
  · exact signedAt_of_frame (signedAt_of_frame (signedAt_of_frame
      (signedAt_of_copy rows.firstResult copyF) res₁.frame (by slot_out)) writes₂ (by slot_out)) res₂.frame (by slot_out)
  · exact signedAt_of_frame (signedAt_of_frame (signedAt_of_frame
      (signedAt_of_copy rows.secondResult copyG) res₁.frame (by slot_out)) writes₂ (by slot_out)) res₂.frame (by slot_out)
  · exact signedAt_of_frame (signedAt_of_frame value₁ writes₂ (by slot_out)) res₂.frame (by slot_out)
  · exact (((((RamWriteFrame.refl p (modularWrites sp)).trans rows.frame (by slot_within)).trans
      writes₁ (by slot_within)).trans res₁.frame (by slot_within)).trans writes₂ (by slot_within)).trans
      res₂.frame (by slot_within)

end K256.Proofs.Generate.Generator.Affine.Invert.Core.Batch
