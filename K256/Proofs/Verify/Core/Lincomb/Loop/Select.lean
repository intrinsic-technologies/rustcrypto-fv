import K256.Proofs.Verify.Core.Lincomb.Loop.Index
import K256.Proofs.Verify.Core.Lincomb.Loop.Negative
import K256.Proofs.Generate.Generator.Multiply.Lookup.Memory
import K256.Proofs.Sec1.Wrapper.Copy.Execution

namespace K256.Proofs.Verify.Core.Lincomb.Loop

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
open Generate.Generator.Multiply (Projective)

private theorem reachJump {l r : Label} {a b : Registers} {m n : Ram}
    (step : program.runBlock (dialect Extracted.programImage) ⟨l,a,m⟩ = .jump ⟨r,b,n⟩) :
    Reaches l a m r b n := by
  apply Semantics.Reaches.single
  change (program.runBlock _ _).next _ [] = _
  rw [step]
  rfl

private theorem positivePack {a : Registers} {m : Ram} {sp table : BitVec 64} {k : Fin 8} {q : Projective}
    (rsp : a[4].get 64 = sp) (src : a[6].get 64 = table) (index : a[7].get 64 = BitVec.ofNat 64 k.val)
    (df : a[22].get 1 = 0) (widths : ∀ i : Fin Reg.count, i.val ∈ [1,2,8,9] → a[i].width = 64)
    (write : Writable Extracted.programImage m sp 0x1a8)
    (read : Readable m (table + BitVec.ofNat 64 (120*k.val)) 120)
    (apart : Outside (digitWrites sp) (table + BitVec.ofNat 64 (120*k.val)) 120)
    (point : q.Stored m (table + BitVec.ofNat 64 (120*k.val))) :
    ∃ b n, Reaches .l1103d1 a m .l110300 b n ∧ Packed sp q a b m n := by
  let ptr := table + BitVec.ofNat 64 (120*k.val)
  let temp := sp + 0x58
  have dst : Writable Extracted.programImage m temp 120 :=
    write.of_offsets (x := sp) (c := 0x58) (d := 0) rfl (BitVec.add_zero _).symm (by decide)
  obtain ⟨_,disj⟩ := apart
  have sep := disj (⟨temp.toNat,120⟩ : MemoryRegion) (.head _)
  have ok : RepMovsOk Extracted.programImage m 0 ptr temp 15 8 0x1103e5 3 :=
    Generate.Generator.Multiply.Lookup.copyGuard read (by slot_guard using code_l1103d1) sep
  have scale : BitVec.ofNat 64 k.val * 120 = BitVec.ofNat 64 (120*k.val) := by
    rw [Nat.mul_comm, BitVec.ofNat_mul]
    rfl
  let n := memCopy m temp ptr 120
  have frame : RamWriteFrame m n (digitWrites sp) := by
    apply Sec1.Wrapper.Copy.memCopy_frame (RamWriteFrame.refl _ _)
    exact ⟨_,.head _,Nat.le_refl _,Nat.le_refl _,by have := dst.readable.low; omega⟩
  refine ⟨?_,n,reachJump ?run,?post⟩
  case run =>
    cfg_eval [rsp,src,index,df,scale]
    rw [ite_eq_left (Or.inr ok)]
  case post =>
    refine ⟨?_,rfl,rfl,?_,Generate.Generator.Multiply.Lookup.copyStored point,frame⟩
    · rintro ⟨i,hi⟩ h
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
    · rintro ⟨i,hi⟩ h
      simp only [Activation.argumentNumbers,List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl|rfl|rfl|rfl|rfl|rfl
      · rfl
      · rfl
      · exact widths 2 (by decide)
      · exact widths 1 (by decide)
      · exact widths 8 (by decide)
      · exact widths 9 (by decide)

theorem packDigit {a : Registers} {m : Ram} {sp table : BitVec 64} {q : Projective}
    {d : Int} (hd : Naf.ValidDigit d) (nz : d ≠ 0) (index : d.natAbs / 2 < 8)
    (byte : a[7] = ⟨64, (BitVec.ofInt 8 d).setWidth 64⟩)
    (rsp : a[4].get 64 = sp) (src : a[6].get 64 = table)
    (df : a[22].get 1 = 0) (widths : ∀ i : Fin Reg.count, i.val ∈ [1,2,8,9] → a[i].width = 64)
    (write : Writable Extracted.programImage m sp 0x1a8)
    (read : Readable m (table + BitVec.ofNat 64 (120*(d.natAbs/2))) 120)
    (apart : Outside (digitWrites sp) (table + BitVec.ofNat 64 (120*(d.natAbs/2))) 120)
    (point : q.Stored m (table + BitVec.ofNat 64 (120*(d.natAbs/2)))) :
    ∃ b n, Reaches .l1103c0 a m .l110300 b n ∧ Packed sp (if d < 0 then q.neg else q) a b m n := by
  obtain ⟨s,step,di,ax,keep⟩ := digitSign d hd nz byte
  let k : Fin 8 := ⟨_,index⟩
  by_cases h : d < 0
  · rw [ite_eq_left h] at step ⊢
    obtain ⟨t,run,idx,kept⟩ := negativeIndex d hd h (di.trans byte) (ax.trans di.symm)
    have same (i : Fin Reg.count) (hi : i.val ∈ [1,2,3,4,5,6,8,9,12,13,14,15,22,39,50,51]) :=
      (kept i hi).trans (keep i hi)
    obtain ⟨b,n,path,packed⟩ := negativePack (k := k)
      ((congrArg (Value.get 64) (same 4 (by decide))).trans rsp)
      ((congrArg (Value.get 64) (same 6 (by decide))).trans src) idx write read apart point
    refine ⟨b,n,(reachJump step).trans ((reachJump run).trans path),{packed with keep := ?_}⟩
    intro i hi
    exact (packed.keep i hi).trans (same i ((by decide :
      ∀ i : Fin Reg.count, i.val ∈ [3,4,5,12,13,14,15,22,39,50,51] →
        i.val ∈ [1,2,3,4,5,6,8,9,12,13,14,15,22,39,50,51]) i hi))
  · rw [ite_eq_right h] at step ⊢
    obtain ⟨t,run,idx,kept⟩ := positiveIndex d hd (by omega) (di.trans byte) (ax.trans di.symm)
    have same (i : Fin Reg.count) (hi : i.val ∈ [1,2,3,4,5,6,8,9,12,13,14,15,22,39,50,51]) :=
      (kept i hi).trans (keep i hi)
    obtain ⟨b,n,path,packed⟩ := positivePack (k := k)
      ((congrArg (Value.get 64) (same 4 (by decide))).trans rsp)
      ((congrArg (Value.get 64) (same 6 (by decide))).trans src) idx
      ((congrArg (Value.get 1) (same 22 (by decide))).trans df)
      (fun i hi => (congrArg Value.width (same i ((by decide :
        ∀ i : Fin Reg.count, i.val ∈ [1,2,8,9] → i.val ∈ [1,2,3,4,5,6,8,9,12,13,14,15,22,39,50,51]) i hi))).trans
        (widths i hi)) write read apart point
    refine ⟨b,n,(reachJump step).trans ((reachJump run).trans path),{packed with keep := ?_}⟩
    intro i hi
    exact (packed.keep i hi).trans (same i ((by decide :
      ∀ i : Fin Reg.count, i.val ∈ [3,4,5,12,13,14,15,22,39,50,51] →
        i.val ∈ [1,2,3,4,5,6,8,9,12,13,14,15,22,39,50,51]) i hi))

end K256.Proofs.Verify.Core.Lincomb.Loop
