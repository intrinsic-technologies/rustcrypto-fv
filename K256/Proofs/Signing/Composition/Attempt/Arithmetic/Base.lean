import K256.Proofs.Signing.Composition.Attempt.Call
import K256.Proofs.Signing.Composition.Attempt.Arithmetic.Blocks
import K256.Proofs.Signing.Transfer.Verify
import K256.Proofs.Signing.Scalar.Add
import K256.Proofs.Signing.Scalar.Multiply
import K256.Proofs.Verify.Core.Affine.Fill
import K256.Proofs.Verify.Core.Scalars.Digest.Reduce

namespace K256.Proofs.Signing.Composition.Attempt.Arithmetic

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
open Verify.Core (Registers)
open Generate.Generator.Sample (sampleChildReturn preservedValue)

theorem getWord {v : Value} {w : BitVec 64} (eq : v = ⟨64,w⟩) :
    v.get 64 = w := by
  rw [eq]
  exact BitVec.setWidth_eq w

theorem negativeWindow {s : RamState} {secret msg : ByteArray} {m : Ram} {n : Nat} {off : BitVec 64}
    (call : ValidCall signingKeyTrySign s [secret,msg]) (memory : Memory s m)
    (fit : (9904-off).toNat+n ≤ 11200) :
    Writable Extracted.programImage m (sp s-off) n := by
  rw [addr_sub]
  apply stackWindow call memory
  rwa [show 0-off+9904 = 9904-off by bv_omega]

theorem extendFrame {s : RamState} {m n : Ram} {regions : List MemoryRegion}
    (frame : RamWriteFrame m n regions) (within : RegionsWithin regions (workRegions s)) :
    RamWriteFrame m n (workRegions s) :=
  (RamWriteFrame.refl m _).trans frame within

theorem pushFrame {p ret : BitVec 64} {m : Ram} (depth : 8 ≤ p.toNat) :
    RamWriteFrame m (memStore m (p-8) ret) [⟨(p-8).toNat,8⟩] := by
  apply RamWriteFrame.memStore (RamWriteFrame.refl _ _) ret
  exact ⟨_,List.mem_cons_self,by
    simp only [InRegion]
    have sub : (p-8).toNat = p.toNat-8 := BitVec.toNat_sub_of_le depth
    have := p.isLt
    rw [sub]
    exact ⟨Nat.le_refl _,Nat.le_refl _,by omega⟩⟩

theorem savedGP {a b : Registers} (keep : SavedRegs b a)
    (gp : ∀ i : Fin Reg.count, i.val ∈ Activation.calleeSavedNumbers → a[i].width = 64) :
    ∀ i : Fin Reg.count, i.val ∈ Activation.calleeSavedNumbers → b[i].width = 64 := by
  intro i hi
  rw [keep i (by
    simp only [Activation.calleeSavedNumbers, List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
    omega)]
  exact gp i hi

theorem savedFP {a b : Registers} (keep : SavedRegs b a)
    (fp : a[39].width = 32 ∧ a[50].width = 16 ∧ a[51].width = 16) :
    b[39].width = 32 ∧ b[50].width = 16 ∧ b[51].width = 16 := by
  exact ⟨(congrArg Value.width (keep 39 (by decide))).trans fp.1,
    (congrArg Value.width (keep 50 (by decide))).trans fp.2.1,
    (congrArg Value.width (keep 51 (by decide))).trans fp.2.2⟩

theorem regsGP {s : RamState} {a : Registers} {bx bp p13 p15 : BitVec 64}
    (atRegs : RegistersAt s a bx bp p13 p15) :
    ∀ i : Fin Reg.count, i.val ∈ Activation.calleeSavedNumbers → a[i].width = 64 := by
  intro ⟨i,hi⟩ h
  simp only [Activation.calleeSavedNumbers,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl
  · exact congrArg Value.width atRegs.rbx
  · exact congrArg Value.width atRegs.rbp
  · exact congrArg Value.width atRegs.r12
  · exact congrArg Value.width atRegs.r13
  · exact atRegs.r14
  · exact congrArg Value.width atRegs.r15

theorem keepRegisters {s : RamState} {a b : Registers} {bx bp p13 p15 : BitVec 64}
    (atRegs : RegistersAt s a bx bp p13 p15) (keep : SavedRegs b a)
    (rsp : b[4] = ⟨64,sp s⟩) (widths : ParseSignature.ArgumentWidths b) :
    RegistersAt s b bx bp p13 p15 :=
  ⟨rsp,(keep 22 (by decide)).trans atRegs.df,(keep 3 (by decide)).trans atRegs.rbx,
    (keep 5 (by decide)).trans atRegs.rbp,(keep 12 (by decide)).trans atRegs.r12,
    (keep 13 (by decide)).trans atRegs.r13,(congrArg Value.width (keep 14 (by decide))).trans atRegs.r14,
    (keep 15 (by decide)).trans atRegs.r15,widths,savedFP keep atRegs.fp⟩

theorem savedReturn {s : RamState} {m : Ram} {a : Registers} {out : Output Value Ram Reg.count}
    {dep : Nat} {ret : BitVec 64}
    (df : a[22] = ⟨1,0⟩)
    (gp : ∀ i : Fin Reg.count, i.val ∈ Activation.calleeSavedNumbers → a[i].width = 64)
    (fp : a[39].width = 32 ∧ a[50].width = 16 ∧ a[51].width = 16)
    (post : Atom.All Extracted.programImage out.values out.store
      (Generate.LIR.Fn127d50.doneAt (Generate.Generator.Sample.compareChild
        (activation s m a dep ret) a m ret))) :
    out.values[4] = ⟨64,sp s⟩ ∧ SavedRegs out.values a := by
  obtain ⟨rsp, saved⟩ := sampleChildReturn post
  refine ⟨by simpa only [Generate.Generator.Sample.compareChild, ParseSignature.withArguments,
    activation,BitVec.sub_add_cancel] using rsp, ?_⟩
  intro ⟨i,hi⟩ h
  have eq := saved ⟨i,hi⟩ h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals
    refine eq.trans ?_
    first
    | exact df.symm
    | exact (value_eq (gp 3 (by decide))).symm
    | exact (value_eq (gp 5 (by decide))).symm
    | exact (value_eq (gp 12 (by decide))).symm
    | exact (value_eq (gp 13 (by decide))).symm
    | exact (value_eq (gp 14 (by decide))).symm
    | exact (value_eq (gp 15 (by decide))).symm
    | exact (value_eq fp.1).symm
    | exact (value_eq fp.2.1).symm
    | exact (value_eq fp.2.2).symm

end K256.Proofs.Signing.Composition.Attempt.Arithmetic
