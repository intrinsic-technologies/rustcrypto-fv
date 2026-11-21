import K256.Proofs.Verify.Core.Scalars.Digest.Reduce.Barrier
import K256.Proofs.Verify.LIR.Generated.Values
import K256.Proofs.Common.Tactic
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4

namespace K256.Proofs.Verify.Core.Reduce

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.DomainParameters.Secp256k1 Generate.Generator.Multiply ParseSignature

private abbrev keptRegs := [1,2,3,5,6,8,9,12,13,14,15,22,39,50,51]

private theorem invertBlock {a : Registers} {m : Ram} {base : BitVec 64} (choose : Bool)
    (rsp : a[4].get 64 = base) (rax : a[0].get 64 = if choose then 0 else 1)
    (win : Writable Extracted.programImage m (base-9) 9) :
    ∃ b : Registers, program.runBlock (dialect Extracted.programImage) ⟨.l10a053,a,m⟩ =
      .call ⟨.l127d50,b,memStore m (base-8) (0x10a05f : BitVec 64)⟩ (resume .l10a05f 0x10a05f) ∧
      b[4].get 64 = base-8 ∧ b[7] = ⟨64,if choose then 1 else 0⟩ ∧
      ∀ i : Fin Reg.count, i.val ∈ keptRegs → b[i] = a[i] := by
  refine ⟨?b,?step,?post⟩
  case step =>
    cfg_eval [rsp,rax]
    refine Eq.trans (ite_eq_left ?_) ?_
    · slot_guard using code_l10a053
    · rfl
  case post =>
    refine ⟨rfl,by cases choose <;> rfl,?_⟩
    intro ⟨i,_⟩ hi
    simp only [keptRegs,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem invertChoice {fr : Activation} {w : Vector (BitVec 64) 4} {a : Registers} {m : Ram}
    (h : Live fr w a m) (choose : Bool) (flag : a[0] = ⟨64,if choose then 0 else 1⟩) :
    ∃ b n, Core.Reaches .l10a053 a m .l10a05f b n ∧ Live fr w b n ∧
      b[0] = ⟨64,if choose then 1 else 0⟩ := by
  obtain ⟨rsp,df,mx,ft,fc,di,bx,r12,r13,r14,r15,bp,slot,ret,low,stack,room,align,_⟩ := h.atoms
  change fr.low.toNat + 97 ≤ fr.rsp.toNat at room
  have win : Writable Extracted.programImage m (sp fr-9) 9 :=
    stack.of_offsets (show sp fr-9 = fr.rsp + (0-97) by dsimp only [sp]; bv_omega)
      (addr_sub fr.rsp 97) (by decide)
  obtain ⟨b,call,bs,bit,bk⟩ := invertBlock (base := sp fr) choose (congrArg (Value.get 64) rsp)
    (congrArg (Value.get 64) flag) win
  obtain ⟨c,n,reach,cs,cf,writes,ck⟩ := barrier call bs win
    (by dsimp only [sp]; bv_omega) (by decide)
  have kept (i : Fin Reg.count) (hi : i.val ∈ keptRegs) : c[i] = a[i] := by
    exact (ck i (by simp only [keptRegs,List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega)).trans (bk i hi)
  have load (ptr : BitVec 64) (start : (sp fr).toNat ≤ ptr.toNat) (top : ptr.toNat+8 ≤ 2^64) :
      memLoad n ptr 64 = memLoad m ptr 64 := by
    apply writes.memLoad_eq
    refine ⟨top,?_⟩
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    right
    dsimp only [scratch, sp] at *
    bv_omega
  have top := slot.low
  change fr.rsp.toNat + 8 ≤ 2^32 at top
  have hd (ptr : BitVec 64) (lo : (sp fr).toNat ≤ ptr.toNat) (hi : ptr.toNat+8 ≤ 2^64)
      {v} (hv : memLoad m ptr 64 = v) : memLoad n ptr 64 = v := (load ptr lo hi).trans hv
  have inside : RegionsWithin [scratch (sp fr)] [fr.region] := by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨_,List.mem_cons_self,?_,?_⟩ <;> dsimp only [scratch,sp,Activation.region] <;> bv_omega
  refine ⟨c,n,reach,?_,?_⟩
  · refine ⟨?_,h.frame.trans writes inside,?_,(kept 14 (by decide)).trans h.r14,
      (kept 12 (by decide)).trans h.r12,(kept 5 (by decide)).trans h.rbp,
      (kept 15 (by decide)).trans h.r15,?_,(kept 13 (by decide)).trans h.r13,?_,
      (kept 3 (by decide)).trans h.rbx⟩
    · refine ⟨cs,(kept 22 (by decide)).trans df,(kept 39 (by decide)).trans mx,
        (kept 50 (by decide)).trans ft,(kept 51 (by decide)).trans fc,?_,?_,?_,?_,?_,?_,?_,
        slot.of_frame writes,?_,low,stack.of_frame writes,room,align,trivial⟩
      all_goals apply hd _ _ _ (by assumption) <;> (try dsimp only [sp]) <;> bv_omega
    · intro ⟨i,hi⟩ hj
      simp only [Activation.argumentNumbers,List.mem_cons,List.not_mem_nil,or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
      · exact congrArg Value.width ((ck 7 (by decide)).trans bit)
      · exact (congrArg Value.width (kept 6 (by decide))).trans (h.widths 6 (by decide))
      · exact (congrArg Value.width (kept 2 (by decide))).trans (h.widths 2 (by decide))
      · exact (congrArg Value.width (kept 1 (by decide))).trans (h.widths 1 (by decide))
      · exact (congrArg Value.width (kept 8 (by decide))).trans (h.widths 8 (by decide))
      · exact (congrArg Value.width (kept 9 (by decide))).trans (h.widths 9 (by decide))
    · apply hd _ _ _ h.lowDiff <;> dsimp only [sp] <;> bv_omega
    · apply hd _ _ _ h.highDiff <;> dsimp only [sp] <;> bv_omega
  · rw [cf,bit]
    cases choose <;> rfl

end K256.Proofs.Verify.Core.Reduce
