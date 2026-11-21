import K256.Proofs.Generate.Generator.Multiply.Prepare.Tables.NegativeBlock
import K256.Proofs.Generate.Generator.Multiply.Prepare.Tables.Transport
import K256.Proofs.Generate.Generator.Multiply.Prepare.Accumulator.Frame
import K256.Proofs.Generate.Generator.Multiply.Lookup.SelectCall

namespace K256.Proofs.Generate.Generator.Multiply.Prepare.Table

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
  Standards.SECG.DomainParameters.Secp256k1

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1200000 in
theorem selectSecondBase {fr : Activation} {initial a : Registers} {m : Ram} {d : Nat} {p t : Projective}
    (e : CoreEntry fr initial d) (s : State .l11d157 fr a m) (tab : Partial true 7 (sp fr) m t)
    (stored : p.Stored m (sp fr+688))
    (mask4 : a[3].get 64 = 0x3ffffffffffffc) (mask52 : a[12].get 64 = 0xfffffffffffff)
    (mask48 : a[14].get 64 = 0xffffffffffff) (base : a[5].get 64 = sp fr+808)
    (work : a[15].get 64 = sp fr+464) (tmp : a[13].get 64 = sp fr+1048)
    (zero : memLoad m (sp fr+8) 64 = 0)
    (sign : memLoad m (sp fr+72) 8 = if secondComponent d < 0 then 1 else 0) :
    ∃ b n, Reaches .l11d157 a m .l11d2e1 b n ∧ State .l11d2e1 fr b n ∧
      TableAt n (sp fr+2128) t.value ∧ (if secondComponent d < 0 then p.neg else p).Stored n (sp fr+3088) ∧
      b[3] = ⟨64,sp fr+3088⟩ ∧ b[12] = ⟨64,sp fr+296⟩ ∧ b[14] = ⟨64,0⟩ ∧
      b[15] = ⟨64,sp fr+464⟩ ∧ RamWriteFrame m n (Bases.writes fr scratchSpans) := by
  obtain ⟨top,df,stack⟩ := Accumulator.currentStack s rfl
  have high : (sp fr).toNat + 3256 < 2^32 := by acc_bounds using e
  have room : 544 ≤ (sp fr).toNat := by acc_bounds using e
  obtain ⟨table,ff⟩ := finished true (Nat.le_of_lt high) tab
  let mc := finishCopy true (sp fr) m
  have delta : RamWriteFrame m mc (Bases.writes fr scratchSpans) :=
    (RamWriteFrame.refl m _).trans ff (finishWithin true fr)
  have pos := stored.of_frame delta (Bases.outside e scratchSpans (i := 688) (by decide) (by decide))
  obtain ⟨x,y,z,wx,wy,wz,rx,ry,rz⟩ := pos.coordinates
  obtain ⟨b,call,rsp,rsi,rdx,rdi,flag,b3,b12,b14,b15,ctrl⟩ :=
    dispatchNegative (q := sp fr) (by simpa only [sp,Lift.reduceSubOffset,BitVec.reduceAdd] using stack)
      room high (congrArg (Value.get 64) top) (congrArg (Value.get 1) df) mask4 mask52 mask48 base work tmp
      ((delta.memLoad_eq (Bases.outside e scratchSpans (i := 8) (by decide) (by decide))).trans zero)
      ((delta.memLoad_eq (Bases.outside e scratchSpans (i := 72) (by decide) (by decide))).trans sign)
      wx (by simpa only [Lift.reduceAddOffset,BitVec.reduceAdd] using wy)
      (by simpa only [Lift.reduceAddOffset,BitVec.reduceAdd] using wz)
  have nf := negativeRecord_frame e mc x y z
  have stk := (stack.of_frame delta).of_frame nf
  let choose := decide (secondComponent d < 0)
  obtain ⟨c,n,path,back,save,keep,widths,point,cf⟩ :=
    Lookup.resumeSelect (sp := sp fr) (dst := sp fr+3088) (left := sp fr+688) (right := sp fr+808) choose call (congrArg (Value.get 64) rsp) (congrArg (Value.get 64) rsi)
      (congrArg (Value.get 64) rdx) (congrArg (Value.get 64) rdi) (congrArg Value.width rdi)
      (by simpa only [choose,decide_eq_true_eq] using flag) (stk.sub (by acc_bounds using e) (by acc_bounds using e))
      (by omega) (by decide) (stk.readable.sub (by acc_bounds using e) (by acc_bounds using e))
      (stk.readable.sub (by acc_bounds using e) (by acc_bounds using e))
      (stk.sub (by acc_bounds using e) (by acc_bounds using e)) (by acc_bounds using e)
      (by acc_bounds using e) (by acc_bounds using e)
      (pos.of_frame nf (Bases.outside e [(808,120)] (i := 688) (by decide) (by decide)))
      (negativeRecord_stored rx ry rz)
  let xs : Bases.Spans := [(808,120),(3088,120)]
  have narrow : RamWriteFrame mc n (Bases.writes fr xs) := by
    apply ((RamWriteFrame.refl mc (Bases.writes fr xs)).trans nf (spansWithin fr (by decide))).trans cf
    intro r hr
    rcases List.mem_cons.mp hr with rfl|hr
    · exact ⟨_,.head _,by dsimp [Bases.writes]; acc_bounds using e,by dsimp [Bases.writes]; acc_bounds using e⟩
    · obtain rfl := List.mem_singleton.mp hr
      exact ⟨_,.tail _ (.tail _ (.head _)),by dsimp [Bases.writes,xs]; acc_bounds using e,
        by dsimp [Bases.writes,xs]; acc_bounds using e⟩
  have full := delta.trans narrow (spansWithin fr (by decide))
  have equal (i : Fin Reg.count) (h : i.val ∈ [4,22,39,50,51]) : c[i] = a[i] := by
    rcases List.mem_cons.mp h with eq|h
    · obtain rfl : i = 4 := Fin.ext eq
      exact back.trans top.symm
    · exact (keep i h).trans (ctrl i h)
  refine ⟨c,n,path,scratchState e s rfl rfl full widths (fun j h => congrArg Value.width (save j h)) equal,
    table.of_frame narrow (Bases.outside e xs (i := 2128) (by decide) (by decide)),?_,?_,?_,?_,?_,full⟩
  · simpa only [choose,decide_eq_true_eq] using point
  · exact (save 3 (by decide)).trans (congrArg (fun v : Value => Value.mk 64 (v.get 64)) b3)
  · exact (save 12 (by decide)).trans (congrArg (fun v : Value => Value.mk 64 (v.get 64)) b12)
  · exact (save 14 (by decide)).trans (congrArg (fun v : Value => Value.mk 64 (v.get 64)) b14)
  · exact (save 15 (by decide)).trans (congrArg (Value.mk 64) ((congrArg (Value.get 64) b15).trans work))

end K256.Proofs.Generate.Generator.Multiply.Prepare.Table
