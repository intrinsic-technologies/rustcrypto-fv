import K256.Proofs.Generate.Generator.Multiply.Prepare.Tables.NegativeRecord

namespace K256.Proofs.Generate.Generator.Multiply.Prepare.Table

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Tactic K256.Proofs.Generate.LIR
  K256.Proofs.Common.Field

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1800000 in
theorem dispatchNegative {a : Registers} {m : Ram} {q : Word} {flag : BitVec 8} {x y z : Limbs}
    (win : Writable Extracted.programImage m (q-544) 3800) (room : 544 ≤ q.toNat) (high : q.toNat + 3256 < 2^32)
    (rsp : a[4].get 64 = q) (df : a[22].get 1 = 0)
    (mask4 : a[3].get 64 = 0x3ffffffffffffc) (mask52 : a[12].get 64 = 0xfffffffffffff)
    (mask48 : a[14].get 64 = 0xffffffffffff) (base : a[5].get 64 = q+808)
    (work : a[15].get 64 = q+464) (tmp : a[13].get 64 = q+1048)
    (zero : memLoad (finishCopy true q m) (q+8) 64 = 0)
    (sign : memLoad (finishCopy true q m) (q+72) 8 = flag)
    (px : WordsAt (finishCopy true q m) (q+688) 64 x)
    (py : WordsAt (finishCopy true q m) (q+728) 64 y)
    (pz : WordsAt (finishCopy true q m) (q+768) 64 z) :
    ∃ b : Registers, program.runBlock (dialect Extracted.programImage) ⟨.l11d157,a,m⟩ =
      .call ⟨.l10fcc0,b,memStore (negativeRecord (finishCopy true q m) q x y z) (q-8) (0x11d2e1 : Word)⟩
        (callFrame .l11d2e1 0x11d2e1) ∧ b[4] = ⟨64,q-8⟩ ∧ b[6] = ⟨64,q+688⟩ ∧
      b[2] = ⟨64,q+808⟩ ∧ b[7] = ⟨64,q+3088⟩ ∧ (b[1].get 64).setWidth 8 = flag ∧
      b[3] = ⟨64,q+3088⟩ ∧ b[12] = ⟨64,q+296⟩ ∧ b[14] = ⟨64,0⟩ ∧ b[15] = a[15] ∧
      ∀ j : Fin Reg.count, j.val ∈ [22,39,50,51] → b[j] = a[j] := by
  have win0 : Writable Extracted.programImage m q 3256 := by
    apply win.sub
    all_goals rw [BitVec.toNat_sub_of_le (by exact room)]; simp only [BitVec.reduceToNat]; omega
  let cp := memCopy (memCopy m (q+1048) (q+464) 120) (q+2968) (q+1048) 120
  change memLoad cp (q+8) 64 = 0 at zero
  change memLoad cp (q+72) 8 = flag at sign
  change WordsAt cp (q+688) 64 x at px
  change WordsAt cp (q+728) 64 y at py
  change WordsAt cp (q+768) 64 z at pz
  have x0 : memLoad cp (q+688) 64 = x[0] := by
    simpa only [wordAddr,Nat.reduceDiv,Nat.reduceMul,BitVec.ofNat_eq_ofNat,Lift.reduceAddOffset,BitVec.reduceAdd,BitVec.add_zero] using px 0 (by decide)
  have x1 : memLoad cp (q+696) 64 = x[1] := by
    simpa only [wordAddr,Nat.reduceDiv,Nat.reduceMul,BitVec.ofNat_eq_ofNat,Lift.reduceAddOffset,BitVec.reduceAdd,BitVec.add_zero] using px 1 (by decide)
  have x2 : memLoad cp (q+704) 64 = x[2] := by
    simpa only [wordAddr,Nat.reduceDiv,Nat.reduceMul,BitVec.ofNat_eq_ofNat,Lift.reduceAddOffset,BitVec.reduceAdd,BitVec.add_zero] using px 2 (by decide)
  have x3 : memLoad cp (q+712) 64 = x[3] := by
    simpa only [wordAddr,Nat.reduceDiv,Nat.reduceMul,BitVec.ofNat_eq_ofNat,Lift.reduceAddOffset,BitVec.reduceAdd,BitVec.add_zero] using px 3 (by decide)
  have x4 : memLoad cp (q+720) 64 = x[4] := by
    simpa only [wordAddr,Nat.reduceDiv,Nat.reduceMul,BitVec.ofNat_eq_ofNat,Lift.reduceAddOffset,BitVec.reduceAdd,BitVec.add_zero] using px 4 (by decide)
  have y0 : memLoad cp (q+728) 64 = y[0] := by
    simpa only [wordAddr,Nat.reduceDiv,Nat.reduceMul,BitVec.ofNat_eq_ofNat,Lift.reduceAddOffset,BitVec.reduceAdd,BitVec.add_zero] using py 0 (by decide)
  have y1 : memLoad cp (q+736) 64 = y[1] := by
    simpa only [wordAddr,Nat.reduceDiv,Nat.reduceMul,BitVec.ofNat_eq_ofNat,Lift.reduceAddOffset,BitVec.reduceAdd,BitVec.add_zero] using py 1 (by decide)
  have y2 : memLoad cp (q+744) 64 = y[2] := by
    simpa only [wordAddr,Nat.reduceDiv,Nat.reduceMul,BitVec.ofNat_eq_ofNat,Lift.reduceAddOffset,BitVec.reduceAdd,BitVec.add_zero] using py 2 (by decide)
  have y3 : memLoad cp (q+752) 64 = y[3] := by
    simpa only [wordAddr,Nat.reduceDiv,Nat.reduceMul,BitVec.ofNat_eq_ofNat,Lift.reduceAddOffset,BitVec.reduceAdd,BitVec.add_zero] using py 3 (by decide)
  have y4 : memLoad cp (q+760) 64 = y[4] := by
    simpa only [wordAddr,Nat.reduceDiv,Nat.reduceMul,BitVec.ofNat_eq_ofNat,Lift.reduceAddOffset,BitVec.reduceAdd,BitVec.add_zero] using py 4 (by decide)
  have z0 : memLoad cp (q+768) 64 = z[0] := by
    simpa only [wordAddr,Nat.reduceDiv,Nat.reduceMul,BitVec.ofNat_eq_ofNat,Lift.reduceAddOffset,BitVec.reduceAdd,BitVec.add_zero] using pz 0 (by decide)
  have z1 : memLoad cp (q+776) 64 = z[1] := by
    simpa only [wordAddr,Nat.reduceDiv,Nat.reduceMul,BitVec.ofNat_eq_ofNat,Lift.reduceAddOffset,BitVec.reduceAdd,BitVec.add_zero] using pz 1 (by decide)
  have z2 : memLoad cp (q+784) 64 = z[2] := by
    simpa only [wordAddr,Nat.reduceDiv,Nat.reduceMul,BitVec.ofNat_eq_ofNat,Lift.reduceAddOffset,BitVec.reduceAdd,BitVec.add_zero] using pz 2 (by decide)
  have z3 : memLoad cp (q+792) 64 = z[3] := by
    simpa only [wordAddr,Nat.reduceDiv,Nat.reduceMul,BitVec.ofNat_eq_ofNat,Lift.reduceAddOffset,BitVec.reduceAdd,BitVec.add_zero] using pz 3 (by decide)
  have z4 : memLoad cp (q+800) 64 = z[4] := by
    simpa only [wordAddr,Nat.reduceDiv,Nat.reduceMul,BitVec.ofNat_eq_ofNat,Lift.reduceAddOffset,BitVec.reduceAdd,BitVec.add_zero] using pz 4 (by decide)
  dsimp only [cp] at zero sign x0 x1 x2 x3 x4 y0 y1 y2 y3 y4 z0 z1 z2 z3 z4
  refine ⟨?_,?run,?rest⟩
  case run =>
    arithmetic_segment using code_l11d157 [rsp,df,base,work,tmp,mask4,mask52,mask48,zero,sign,
      negativeRecord,x0,x1,x2,x3,x4,y0,y1,y2,y3,y4,z0,z1,z2,z3,z4]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; first | rep_copy_guard using code_l11d157 | (dsimp only [memCopy]; slot_guard using code_l11d157))
    rfl
  case rest =>
    refine ⟨rfl,rfl,rfl,rfl,?_,rfl,rfl,rfl,rfl,?_⟩
    · simp [Value.get]
    · rintro ⟨j,hj⟩ hm
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
      rcases hm with rfl|rfl|rfl|rfl <;> rfl

end K256.Proofs.Generate.Generator.Multiply.Prepare.Table
