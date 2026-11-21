import K256.Proofs.Signing.Composition.Attempt.Coordinates.Affine
import K256.Proofs.Signing.Composition.Attempt.Coordinates.Serialize

namespace K256.Proofs.Signing.Composition.Attempt

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Verify.Core (Registers)

set_option maxHeartbeats 800000 in
private theorem serializeCoordinate {s : RamState} {secret msg : ByteArray} {d k : Nat} {st : State}
    {a : Registers} {m : Ram} (call : ValidCall signingKeyTrySign s [secret,msg])
    (regs : CoordinateRegisters s a (sp s+256)) (memory : CoordinateMemory s d msg st k m)
    (pointAt : Sec1.Parser.PublicKeyAt m (sp s+256) (Generate.Curve.generatorWindow k)) :
    ∃ b n x y, Reach (core .l105b75 a m) (core .l105b88 b n) ∧ CoordinatesReady s d msg st k x y b n := by
  let p := sp s
  have pEq : p.toNat = (sp s).toNat := rfl
  let base := p-112
  let pushed := memStore m (p-8) (0x105b88 : BitVec 64)
  let g := StackBounds.ofCall call
  have room := g.room
  have high := g.high
  have align := g.alignment
  have nat8 : (p-8).toNat = p.toNat-8 := g.below 8 (by decide)
  have baseNat : base.toNat = p.toNat-112 := g.below 112 (by decide)
  have windowNat : (base-121).toNat = p.toNat-233 := by
    rw [show base-121 = p-233 by dsimp [base]; bv_omega]
    exact g.below 233 (by decide)
  have natSrc : (p+256).toNat = p.toNat+256 := g.above 256 (by decide)
  have natDst : (p+160).toNat = p.toNat+160 := g.above 160 (by decide)
  have fp := g.pushFrame (m := m) 0x105b88
  have pm := memory.preserve g call fp (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    change _ ≤ (p-8).toNat
    omega) (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    change (p-8).toNat+8 ≤ _
    omega)
  have slotPush : Writable Extracted.programImage m (p-8) 8 :=
    g.slot call memory.toMemory (by rw [nat8]; omega) (by rw [nat8]; omega)
  have pushOk : StoreOk Extracted.programImage m (p-8) 8 0x105b83 5 :=
    ParseSignature.storeOk_of_codeRange (off := 14) slotPush
      (fun y hy => Common.fnCode_subset_programImage y (LIR.code_l105b75 y hy)) (by decide)
  obtain ⟨b,block,b4,b14,b6,b7,keep⟩ := serializeCall
    (congrArg (Value.get 64) regs.rsp) (congrArg (Value.get 64) regs.rbx) pushOk
  have win : Writable Extracted.programImage pushed (base-121) 433 :=
    g.slot call pm.toMemory (by omega) (by omega)
  have source : Writable Extracted.programImage pushed (p+256) 40 :=
    g.slot call pm.toMemory (by omega) (by omega)
  have dest : Writable Extracted.programImage pushed (p+160) 32 :=
    g.slot call pm.toMemory (by omega) (by omega)
  have pop : base+112 = p := by dsimp [base]; bv_omega
  have slot : base+104 = p-8 := by dsimp [base]; bv_omega
  have slotValue : memLoad pushed (base+104) 64 = 0x105b88 := by
    rw [slot]
    exact memLoad_memStore_same _ _ _ (by decide) (by decide)
  obtain ⟨x,y,point,xl,_,wx,_,_,rx,_⟩ := pointAt
  have xAt : Ecdh.Affine.XAt pushed (p+256) (Generate.Curve.generatorWindow k) := by
    have outside : Outside [⟨(p-8).toNat,8⟩] (p+256) 40 :=
      g.outside 256 40 (by decide) (by
        intro r hr
        obtain rfl := List.mem_singleton.mp hr
        right
        change (p-8).toNat+8 ≤ _
        omega)
    exact ⟨x,xl,wx.of_frame fp (by decide) outside,rx,by rw [point]⟩
  have width (i : Fin Reg.count) (hi : i.val ∈ 3 :: savedRegs.erase 14) (hw : a[i].width = 64) :
      b[i].width = 64 := (congrArg Value.width (keep i hi)).trans hw
  obtain ⟨out,exec,tag,outSp,outBX,df,kept,widths,out14,writes,bytes⟩ := Serializer.serializeX
    (a := b) (base := base) (src := p+256) (dst := p+160) (saved14 := p+160)
    (by rw [slot]; exact congrArg (Value.get 64) b4) (congrArg (Value.get 64) b6)
    (congrArg (Value.get 64) b7) (width 5 (by decide) (congrArg Value.width regs.rbp))
    (width 12 (by decide) (congrArg Value.width regs.r12)) (width 13 (by decide) (congrArg Value.width regs.r13))
    (width 15 (by decide) (congrArg Value.width regs.r15)) ((keep 22 (by decide)).trans regs.df)
    (congrArg (Value.get 64) b14) win source.readable dest (by omega) (by omega) (by omega)
    (by decide) slotValue xAt
  have final := pm.preserve g call writes (by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · change _ ≤ (base-121).toNat
      omega
    · change _ ≤ (p+160).toNat
      omega) (by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · change (base-121).toNat+233 ≤ _
      omega
    · change (p+160).toNat+32 ≤ _
      omega)
  have preserved (i : Fin Reg.count) (hi : i.val ∈ [5,12,13,15,39,50,51]) :
      out.values[i] = a[i] := (kept i hi).trans (keep i (by
    change i.val ∈ [3,5,12,13,15,22,39,50,51]
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
    omega))
  have finalRegs : RegistersAt s out.values (p+256) (p+192) (p+656) (p+456) := by
    refine ⟨by simpa only [pop] using outSp,df,?_,(preserved 5 (by decide)).trans regs.rbp,
      (preserved 12 (by decide)).trans regs.r12,(preserved 13 (by decide)).trans regs.r13,
      congrArg Value.width out14,(preserved 15 (by decide)).trans regs.r15,widths,?_⟩
    · exact outBX.trans (congrArg (fun v : Value => Value.mk 64 (v.get 64))
        ((keep 3 (by decide)).trans regs.rbx))
    · exact ⟨(congrArg Value.width (preserved 39 (by decide))).trans regs.fp.1,
        (congrArg Value.width (preserved 50 (by decide))).trans regs.fp.2.1,
        (congrArg Value.width (preserved 51 (by decide))).trans regs.fp.2.2⟩
  refine ⟨out.values,out.store,x.val,y.val,callReaches block (Transfer.verifyExecAt (src := .l120350) rfl (Serializer.transfer exec)) tag,
    ⟨final.toLoopMemory,finalRegs,out14,point,?_,?_,final.digest,final.inverse⟩⟩
  · exact Nat.lt_trans x.isLt (by decide : Common.Field.modulus < 2^256)
  · simpa only [point,Ecdh.Output.xBytes] using bytes

theorem coordinates {s : RamState} {secret msg : ByteArray} {d : Nat}
    (call : ValidCall signingKeyTrySign s [secret,msg])
    {a : Registers} {m : Ram} {st : State} {k : Nat}
    (scalars : ScalarsReady s d msg st k a m) (pos : 0 < k) (bound : k < domain.n) :
    ∃ b n x y, Reach (core .l105b23 a m) (core .l105b88 b n) ∧ CoordinatesReady s d msg st k x y b n := by
  obtain ⟨b,n,multiplied,registers,memory,point⟩ := multiplyNonce call scalars pos bound
  obtain ⟨c,t,converted,registers,memory,point⟩ :=
    affineCoordinates call registers memory point (Generate.Curve.generatorWindow_ne_infinity k pos bound)
  obtain ⟨e,u,x,y,serialized,ready⟩ := serializeCoordinate call registers memory point
  exact ⟨e,u,x,y,(multiplied.trans converted).trans serialized,ready⟩

end K256.Proofs.Signing.Composition.Attempt
