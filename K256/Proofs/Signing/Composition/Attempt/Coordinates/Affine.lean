import K256.Proofs.Signing.Composition.Attempt.Coordinates.Multiply
import K256.Proofs.Signing.Affine
import K256.Proofs.Verify.Core.Affine.Transfer

namespace K256.Proofs.Signing.Composition.Attempt

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Verify.Core (Registers)

set_option maxHeartbeats 800000 in
theorem affineCoordinates {s : RamState} {secret msg : ByteArray} {d k : Nat} {st : State}
    {a : Registers} {m : Ram} (call : ValidCall signingKeyTrySign s [secret,msg])
    (regs : CoordinateRegisters s a (sp s+624)) (memory : CoordinateMemory s d msg st k m)
    (projective : Generate.Generator.Affine.ProjectiveAt m (sp s+8) (Generate.Curve.generatorWindow k))
    (hne : Generate.Curve.generatorWindow k ≠ .infinity) :
    ∃ b n, Reach (core .l105b62 a m) (core .l105b75 b n) ∧
      CoordinateRegisters s b (sp s+256) ∧ CoordinateMemory s d msg st k n ∧
      Sec1.Parser.PublicKeyAt n (sp s+256) (Generate.Curve.generatorWindow k) := by
  let p := sp s
  have pEq : p.toNat = (sp s).toNat := rfl
  let g := StackBounds.ofCall call
  let pushed := memStore m (p-8) (0x105b75 : BitVec 64)
  have bottom := g.room
  have high := g.high
  have nat8 : (p-8).toNat = p.toNat-8 := g.below 8 (by decide)
  have nat984 : (p-984).toNat = p.toNat-984 := g.below 984 (by decide)
  have fp := g.pushFrame (m := m) 0x105b75
  have lower {r : MemoryRegion} (hr : r ∈ [⟨(p-8).toNat,8⟩]) : p.toNat-9904 ≤ r.start := by
    obtain rfl := List.mem_singleton.mp hr
    change _ ≤ (p-8).toNat
    omega
  have upper {r : MemoryRegion} (hr : r ∈ [⟨(p-8).toNat,8⟩]) : r.start+r.size ≤ p.toNat+344 := by
    obtain rfl := List.mem_singleton.mp hr
    change (p-8).toNat+8 ≤ _
    omega
  have pm := memory.preserve g call fp (fun _ => lower) (fun _ => upper)
  have slotPush : Writable Extracted.programImage m (p-8) 8 :=
    g.slot call memory.toMemory (by rw [nat8]; omega) (by rw [nat8]; omega)
  have pushOk : StoreOk Extracted.programImage m (p-8) 8 0x105b70 5 :=
    ParseSignature.storeOk_of_codeRange (off := 14) slotPush
      (fun y hy => Common.fnCode_subset_programImage y (LIR.code_l105b62 y hy)) (by decide)
  obtain ⟨b,block,b4,b3,b6,b7,keep⟩ := affineCall
    (congrArg (Value.get 64) regs.rsp) (congrArg (Value.get 64) regs.r12) pushOk
  let fr := coordinateActivation s b pushed 976 0x105b75 (p+256) (p+8) (p+256)
  have image := pm.toMemory.image call
  have got := Generate.LIR.Fn10fe50.callSlots_loaded
    (sections := Extracted.programSections) (by simp [Generate.LIR.rodataSection, Extracted.programSections]) image
  obtain ⟨read1,val1⟩ := got (0x203de0,0x129770) (by decide)
  obtain ⟨read2,val2⟩ := got (0x203e20,0x100a20) (by decide)
  have low : fr.low = p-984 := by change p-8-976 = p-984; bv_omega
  have localStack : Writable Extracted.programImage pushed (fr.rsp-976) 976 :=
    g.slot call pm.toMemory (by rw [show fr.rsp-976 = p-984 from low,nat984]; omega)
      (by rw [show fr.rsp-976 = p-984 from low,nat984]; omega)
  have addr8 : (p+8).toNat = p.toNat+8 := g.above 8 (by decide)
  have addr256 : (p+256).toNat = p.toNat+256 := g.above 256 (by decide)
  have rq : fr.rsp.toNat = p.toNat-8 := nat8
  have apart : (p-8).toNat ≤ 0x203de0 ∨ 0x203e28+9768 ≤ (p-8).toNat := subcallApart call g
  have al := g.alignment
  have atoms : Atom.All Extracted.programImage b pushed (Verify.Core.Affine.atomsAt .l10fe50 fr) := by
    refine ⟨b4,(keep 22 (by decide)).trans regs.df,trivial,trivial,b3,
      (keep 5 (by decide)).trans regs.rbp,b6,b7,trivial,trivial,
      (keep 12 (by decide)).trans regs.r12,(keep 13 (by decide)).trans regs.r13,
      (value_eq ((congrArg Value.width (keep 14 (by decide))).trans regs.r14)),
      (keep 15 (by decide)).trans regs.r15,
      (value_eq ((congrArg Value.width (keep 39 (by decide))).trans regs.fp.1)),
      (value_eq ((congrArg Value.width (keep 50 (by decide))).trans regs.fp.2.1)),
      (value_eq ((congrArg Value.width (keep 51 (by decide))).trans regs.fp.2.2)),
      (slotPush.of_frame fp).readable,memLoad_memStore_same _ _ _ (by decide) (by decide),
      by change (0x105b75 : Nat) < 2^32; decide,localStack,?_,?_,read1,val1,read2,val2,?_,trivial⟩
    · change fr.low.toNat+976 ≤ fr.rsp.toNat
      rw [show fr.low.toNat = p.toNat-984 from congrArg BitVec.toNat low |>.trans nat984,rq]; omega
    · change fr.rsp.toNat % 16 = 8
      rw [rq]; omega
    · change 0x2041f8 ≤ (p-8).toNat ∨ (p-8).toNat ≤ 0x203de0
      omega
  have source : Writable Extracted.programImage pushed (p+8) 120 :=
    g.slot call pm.toMemory (by omega) (by omega)
  have dest : Writable Extracted.programImage pushed (p+256) 88 :=
    g.slot call pm.toMemory (by omega) (by omega)
  have entry : Signing.Affine.CallState .l10fe50 fr b pushed := by
    refine ⟨atoms,image,source.readable,dest,?_,?_,.refl _ _⟩
    · change (p-8).toNat+8 ≤ (p+8).toNat
      omega
    · change (p-8).toNat+8 ≤ (p+256).toNat
      omega
  have point : Generate.Generator.Affine.ProjectiveAt pushed fr.rsi (Generate.Curve.generatorWindow k) := by
    obtain ⟨x,y,z,xl,yl,zl,hx,hy,hz,rx,ry,rz,point⟩ := projective
    have addr48 : p+8+40 = p+48 := by bv_omega
    have addr88 : p+8+80 = p+88 := by bv_omega
    have outside (off : BitVec 64) (fits : off.toNat+40 ≤ 1296) :
        Outside [⟨(p-8).toNat,8⟩] (p+off) 40 :=
      g.outside off 40 fits (by
        intro r hr
        obtain rfl := List.mem_singleton.mp hr
        right
        change (p-8).toNat+8 ≤ p.toNat+off.toNat
        omega)
    exact ⟨x,y,z,xl,yl,zl,hx.of_frame fp (by decide) (outside 8 (by decide)),
      hy.of_frame fp (by decide) (addr48 ▸ outside 48 (by decide)),
      hz.of_frame fp (by decide) (addr88 ▸ outside 88 (by decide)),rx,ry,rz,point⟩
  obtain ⟨out,exec,tag,done,writes,xy⟩ := Signing.Affine.execution entry point hne
  have lo : ∀ r ∈ Generate.Generator.Affine.writes fr, p.toNat-9904 ≤ r.start := by
    intro r hr
    simp only [Generate.Generator.Affine.writes,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · change _ ≤ fr.low.toNat
      rw [low,nat984]; omega
    · change _ ≤ (p+256).toNat
      omega
  have hi : ∀ r ∈ Generate.Generator.Affine.writes fr, r.start+r.size ≤ p.toNat+344 := by
    intro r hr
    simp only [Generate.Generator.Affine.writes,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · change fr.low.toNat+(fr.rsp.toNat-fr.low.toNat) ≤ _
      rw [show fr.low.toNat = p.toNat-984 from congrArg BitVec.toNat low |>.trans nat984,rq]; omega
    · change (p+256).toNat+88 ≤ _
      omega
  exact ⟨out.values,out.store,callReaches block
    (Transfer.verifyExecAt (src := .l10fe50) rfl (Verify.Core.Affine.transfer exec)) tag,
    activationRegisters done,pm.preserve g call writes lo hi,xy⟩

end K256.Proofs.Signing.Composition.Attempt
