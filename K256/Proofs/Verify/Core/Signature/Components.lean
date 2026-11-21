import K256.Proofs.Verify.Core.Signature.Components.Compare
import K256.Proofs.Verify.Core.Signature.Components.Prepare
import K256.Proofs.Verify.Core.Memory

namespace K256.Proofs.Verify.Core

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Generate.Generator.Multiply

structure NonzeroComponents (fr : Activation) (a : Registers) (m : Ram) (r : Nat) : Prop
    extends Phase fr a m where
  atoms : Atom.All Extracted.programImage a m (Fn104f20.frameAt .l105069 fr)
  r9Width : a[9].width = 64
  rAt : WordsAt m (localSp fr + 256) 64 (scalarWords r)

open Components
set_option maxRecDepth 4096 in
theorem checkComponents {fr : Activation} {a : Registers} {p : Curve.Point}
    {d : ByteArray} {r s : Nat} (e : Entry fr a p d r s) :
    ∃ b m, Reaches .l104f20 a fr.original .l105069 b m ∧ NonzeroComponents fr b m r := by
  let sp := localSp fr
  have room := e.stackRoom
  have low := e.low
  have bottom := e.low_toNat
  have spNat : sp.toNat = fr.rsp.toNat-488 :=
    BitVec.toNat_sub_of_le (by change 488 ≤ fr.rsp.toNat; omega)
  have workNat : (sp-24).toNat = fr.rsp.toNat-512 := by
    change (fr.rsp-488-24).toNat = _
    rw [BitVec.sub_sub]
    exact BitVec.toNat_sub_of_le (by change 512 ≤ fr.rsp.toNat; omega)
  have workLow : (sp-24).toNat+512 ≤ 2^32 := by omega
  have base : fr.r8=sp+848 := by rw [e.sig]; change fr.rsp+360=fr.rsp-488+848; bv_omega
  have sb : fr.r8+32=sp+880 := by rw [base,BitVec.add_assoc]; rfl
  have window : Writable Extracted.programImage fr.original (sp-24) 512 :=
    e.stack.sub (by omega) (by omega)
  have sig : Readable fr.original (sp+848) 64 := e.upper.readable.of_offsets
    (show sp+848=fr.rsp+360 by rw [←base,e.sig]) rfl (by decide)
  have lr := wordsToLoads (off := 848) (base ▸ e.rAt)
  obtain ⟨b,firstCall,args⟩ := first e sp rfl window sig lr
  have atoms := e.atoms
  simp only [Fn104f20.frameAt,Fn104f20.frameAtG6,Atom.All,Atom.Holds] at atoms
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,rr,ret,retLow,fullStack,fullRoom,align,
    gr1,g1,gr2,g2,gr3,g3,gotSep,_⟩ := atoms
  have aligned : sp.toNat%16 = 0 := by omega
  have fits : 24 ≤ sp.toNat := by omega
  have bounds := e.bounds
  have order : Standards.SECG.DomainParameters.Secp256k1.domain.n < 2^256 := by decide +kernel
  have saved := saveRegsFrame fr sp workLow
  have win' := window.of_frame saved
  obtain ⟨c,t,firstRun,fixed,rs,dx,r8,r9,firstFrame⟩ :=
    check .r args bounds.1 (by omega) fits aligned (win'.of_offsets (addr_sub sp 24) (addr_sub sp 24) (by decide)) firstCall
  have narrow := saved.trans firstFrame (areaWithin _ (by decide))
  have inside : RegionsWithin (area sp 512) [fr.region] := by
    intro q hq
    obtain rfl := List.mem_singleton.mp hq
    refine ⟨_,List.mem_cons_self,?_,?_⟩
    · change fr.low.toNat ≤ (sp-24).toNat; omega
    · change (sp-24).toNat+512 ≤ fr.low.toNat+(fr.rsp.toNat-fr.low.toNat); omega
  have whole := (RamWriteFrame.refl fr.original [fr.region]).trans narrow inside
  obtain ⟨rAt,sAt⟩ := e.scalarWords_of_frame whole
  rw [base] at rAt
  rw [sb] at sAt
  obtain ⟨b',secondCall,args'⟩ := second fixed sp rfl (congrArg (Value.get 64) rs)
    base dx r8 r9 (window.of_frame narrow) (sig.of_frame narrow)
    (wordsToLoads (off := 848) rAt) (wordsToLoads (off := 880) sAt)
  have copied := saveRFrame t sp (scalarWords r) (by omega)
  have win'' := (window.of_frame narrow).of_frame copied
  obtain ⟨z,m,secondRun,f,stack,_,_,width,last⟩ := check .s args' bounds.2.2.1 (by omega) fits aligned
    (win''.of_offsets (addr_sub sp 24) (addr_sub sp 24) (by decide)) secondCall
  have writes := (narrow.trans copied (areaWithin _ (by decide))).trans last (areaWithin _ (by decide))
  have frame := (RamWriteFrame.refl fr.original [fr.region]).trans writes inside
  have slots := (((savedSlots fr sp).ofFrame firstFrame workLow (by decide)).ofFrame copied
    workLow (by decide)).ofFrame last workLow (by decide)
  have restored : Saved fr z m := by
    refine ⟨stack,f.bx,f.bp,f.df,f.mx,f.ft,f.fc,?_,?_,?_,?_,?_⟩
    all_goals first
      | exact (show sp+448=fr.rsp-40 by dsimp only [sp,localSp]; bv_omega) ▸ slots.bx
      | exact (show sp+456=fr.rsp-32 by dsimp only [sp,localSp]; bv_omega) ▸ slots.r12
      | exact (show sp+464=fr.rsp-24 by dsimp only [sp,localSp]; bv_omega) ▸ slots.r13
      | exact (show sp+472=fr.rsp-16 by dsimp only [sp,localSp]; bv_omega) ▸ slots.r14
      | exact (show sp+480=fr.rsp-8 by dsimp only [sp,localSp]; bv_omega) ▸ slots.r15
  have finalR := (savedRWords t sp (scalarWords r)).of_frame last (by decide)
    (outsideAbove (off := 256) workLow (by decide) (by decide))
  have got {addr : Word} (lo : 0x203dd0 ≤ addr.toNat) (hi : addr.toNat+8 ≤ 0x203e28) :
      Outside (area sp 512) addr 8 := by
    refine ⟨by omega,fun reg hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    change addr.toNat+8 ≤ (sp-24).toNat ∨ (sp-24).toNat+512 ≤ addr.toNat
    omega
  refine ⟨z,m,firstRun.trans secondRun,⟨⟨restored,frame⟩,?_,width,finalR⟩⟩
  simp only [Fn104f20.frameAt,Fn104f20.frameAtG6,Atom.All,Atom.Holds]
  exact ⟨stack,f.df,f.bx,f.bp,f.r12,f.r13,f.r14,f.r15,f.mx,f.ft,f.fc,
    restored.rbx,restored.r12,restored.r13,restored.r14,restored.r15,rr.of_frame writes,
    (frame.memLoad_eq (by simpa only [BitVec.add_zero] using e.above (off := 0) (len := 8) (by decide))).trans ret,retLow,
    fullStack.of_frame writes,fullRoom,align,gr1.of_frame writes,
    (writes.memLoad_eq (got (addr := 0x203dd0) (by decide) (by decide))).trans g1,gr2.of_frame writes,
    (writes.memLoad_eq (got (addr := 0x203de0) (by decide) (by decide))).trans g2,gr3.of_frame writes,
    (writes.memLoad_eq (got (addr := 0x203e20) (by decide) (by decide))).trans g3,gotSep,trivial⟩

end K256.Proofs.Verify.Core
