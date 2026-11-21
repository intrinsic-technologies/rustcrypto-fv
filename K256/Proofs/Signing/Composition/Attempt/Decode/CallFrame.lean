import K256.Proofs.Signing.Composition.Attempt.Call
import K256.Proofs.Generate.LIR.Fn127d50.Frame

namespace K256.Proofs.Signing.Composition.Attempt.Decode

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
open Verify.Core (Registers)

abbrev preservedRegisters := [3,5,12,13,15,22,39,50,51]

theorem fixedRegisters {s : RamState} {a b : Registers} {bx bp p13 p15 : BitVec 64}
    (regs : RegistersAt s a bx bp p13 p15)
    (preserves : ∀ i : Fin Reg.count, i.val ∈ preservedRegisters → b[i] = a[i]) :
    b[22] = ⟨1,0⟩ ∧
    (∀ i : Fin Reg.count, i.val ∈ Activation.calleeSavedNumbers → i.val ≠ 14 → b[i].width = 64) ∧
    b[39].width = 32 ∧ b[50].width = 16 ∧ b[51].width = 16 := by
  refine ⟨(preserves 22 (by decide)).trans regs.df,?_,?_,?_,?_⟩
  · intro i hi h14
    rw [preserves i (by
      simp only [Activation.calleeSavedNumbers,preservedRegisters,List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
      omega)]
    obtain ⟨i,hi'⟩ := i
    simp only [Activation.calleeSavedNumbers,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first
      | exact congrArg Value.width regs.rbx
      | exact congrArg Value.width regs.rbp
      | exact congrArg Value.width regs.r12
      | exact congrArg Value.width regs.r13
      | exact congrArg Value.width regs.r15
      | exact False.elim (h14 rfl)
  · exact (congrArg Value.width (preserves 39 (by decide))).trans regs.fp.1
  · exact (congrArg Value.width (preserves 50 (by decide))).trans regs.fp.2.1
  · exact (congrArg Value.width (preserves 51 (by decide))).trans regs.fp.2.2

theorem afterCall {s : RamState} {a b : Registers} {m : Ram} {bx bp p13 p15 : BitVec 64}
    {depth : Nat} {ret : BitVec 64} {out : Output Value Ram Reg.count}
    (regs : RegistersAt s a bx bp p13 p15)
    (preserves : ∀ i : Fin Reg.count, i.val ∈ preservedRegisters → b[i] = a[i])
    (done_ : Atom.All Extracted.programImage out.values out.store
      (Generate.LIR.Fn127d50.doneAt (activation s m b depth ret)))
    (widths : ParseSignature.ArgumentWidths out.values) :
    RegistersAt s out.values bx bp p13 p15 := by
  simp only [Generate.LIR.Fn127d50.doneAt,Atom.All,Atom.Holds] at done_
  obtain ⟨rsp,df,o3,o5,o12,o13,o14,o15,o39,o50,o51,_⟩ := done_
  refine ⟨rsp.trans (congrArg (Value.mk 64) (show sp s-8+8 = sp s by bv_omega)),df,?_,?_,?_,?_,?_,?_,
    widths,congrArg Value.width o39,congrArg Value.width o50,congrArg Value.width o51⟩
  · exact o3.trans (congrArg (fun v => Value.mk 64 (v.get 64)) ((preserves 3 (by decide)).trans regs.rbx))
  · exact o5.trans (congrArg (fun v => Value.mk 64 (v.get 64)) ((preserves 5 (by decide)).trans regs.rbp))
  · exact o12.trans (congrArg (fun v => Value.mk 64 (v.get 64)) ((preserves 12 (by decide)).trans regs.r12))
  · exact o13.trans (congrArg (fun v => Value.mk 64 (v.get 64)) ((preserves 13 (by decide)).trans regs.r13))
  · exact congrArg Value.width o14
  · exact o15.trans (congrArg (fun v => Value.mk 64 (v.get 64)) ((preserves 15 (by decide)).trans regs.r15))

theorem localSlot {s : RamState} {secret msg : ByteArray}
    (call : ValidCall signingKeyTrySign s [secret,msg])
    {off n : Nat} (finish : off+n ≤ 344) :
    InRegions (workRegions s) (sp s+BitVec.ofNat 64 off) n := by
  obtain ⟨room,high,base⟩ := stackBounds call
  have low : (sp s-9904).toNat = (sp s).toNat-9904 := belowNat call (by decide)
  have atOff := offsetNat call (offset := off) (by omega)
  refine ⟨⟨(sp s-9904).toNat,10248⟩,List.mem_cons_self,?_⟩
  change (sp s-9904).toNat ≤ (sp s+BitVec.ofNat 64 off).toNat ∧
    (sp s+BitVec.ofNat 64 off).toNat+n ≤ (sp s-9904).toNat+10248 ∧ _
  rw [low,atOff]
  omega

theorem returnSlot {s : RamState} {secret msg : ByteArray}
    (call : ValidCall signingKeyTrySign s [secret,msg]) :
    InRegions (workRegions s) (sp s-8) 8 := by
  obtain ⟨room,high,base⟩ := stackBounds call
  have low : (sp s-9904).toNat = (sp s).toNat-9904 := belowNat call (by decide)
  have atSlot : (sp s-8).toNat = (sp s).toNat-8 := belowNat call (by decide)
  refine ⟨⟨(sp s-9904).toNat,10248⟩,List.mem_cons_self,?_⟩
  change (sp s-9904).toNat ≤ (sp s-8).toNat ∧ (sp s-8).toNat+8 ≤ (sp s-9904).toNat+10248 ∧ _
  rw [low,atSlot]
  omega

theorem childWithin {s : RamState} {secret msg : ByteArray} {a : Registers} {m : Ram}
    {depth : Nat} {ret : BitVec 64} {regions : List MemoryRegion}
    (call : ValidCall signingKeyTrySign s [secret,msg]) (small : depth ≤ 9896)
    (localRegions : ∀ r ∈ regions, (sp s-9904).toNat ≤ r.start ∧ r.start+r.size ≤ (sp s).toNat+344) :
    RegionsWithin ((activation s m a depth ret).region :: regions) (workRegions s) := by
  obtain ⟨room,_,base⟩ := stackBounds call
  have low : (sp s-9904).toNat = (sp s).toNat-9904 := belowNat call (by decide)
  have top : (sp s-8).toNat = (sp s).toNat-8 := belowNat call (by decide)
  have bottom : (sp s-8-BitVec.ofNat 64 depth).toNat = (sp s).toNat-(8+depth) := by
    rw [BitVec.sub_sub]
    change (sp s - (BitVec.ofNat 64 8 + BitVec.ofNat 64 depth)).toNat = _
    rw [← BitVec.ofNat_add]
    exact belowNat call (by omega)
  intro r member
  refine ⟨⟨(sp s-9904).toNat,10248⟩,List.mem_cons_self,?_⟩
  rcases List.mem_cons.mp member with rfl|h
  · change (sp s-9904).toNat ≤ (sp s-8-BitVec.ofNat 64 depth).toNat ∧
      (sp s-8-BitVec.ofNat 64 depth).toNat + ((sp s-8).toNat-(sp s-8-BitVec.ofNat 64 depth).toNat) ≤
      (sp s-9904).toNat+10248
    rw [low,top,bottom]
    omega
  · obtain ⟨hlo,hhi⟩ := localRegions r h
    constructor
    · exact hlo
    · change r.start+r.size ≤ (sp s-9904).toNat+10248
      rw [low]
      omega

theorem occursAboveCall {s : RamState} {secret msg : ByteArray} {a : Registers} {m : Ram}
    {depth off size : Nat} {ret : BitVec 64}
    (call : ValidCall signingKeyTrySign s [secret,msg]) (small : depth ≤ 9896) (fits : off+size ≤ 1296) :
    Outside [ParseSignature.callStack (activation s m a depth ret)] (sp s+BitVec.ofNat 64 off) size := by
  obtain ⟨room,high,base⟩ := stackBounds call
  have addr := offsetNat call (offset := off) (by omega)
  have top : (sp s-8).toNat = (sp s).toNat-8 := belowNat call (by decide)
  have bottom : (sp s-8-BitVec.ofNat 64 depth).toNat = (sp s).toNat-(8+depth) := by
    rw [BitVec.sub_sub]
    change (sp s - (BitVec.ofNat 64 8 + BitVec.ofNat 64 depth)).toNat = _
    rw [← BitVec.ofNat_add]
    exact belowNat call (by omega)
  refine ⟨by rw [addr]; omega,?_⟩
  intro r member
  obtain rfl := List.mem_singleton.mp member
  right
  change (sp s-8-BitVec.ofNat 64 depth).toNat +
    ((sp s-8).toNat+8-(sp s-8-BitVec.ofNat 64 depth).toNat) ≤ _
  rw [top,bottom,addr]
  omega

end K256.Proofs.Signing.Composition.Attempt.Decode
