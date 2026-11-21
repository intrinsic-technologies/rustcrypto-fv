import K256.Proofs.Generate.Generator.Multiply.Prepare.Bases.Finish.Dispatch
import K256.Proofs.Ecdh.Multiply.Bases.SelectBlock
import K256.Proofs.Ecdh.Multiply.Bases.Selection
import K256.Proofs.Ecdh.Multiply.Bases.Start.Memory
import K256.Proofs.Ecdh.Multiply.Bases.Pair

namespace K256.Proofs.Generate.Generator.Multiply.Prepare.Bases

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR K256.Proofs.Common.Field
  Standards.SECG.DomainParameters.Secp256k1 Common.Point.TableWords

private theorem pairOnStack {fr : Activation} {initial : Registers} {d : Nat} {peer : Projective}
    (e : PeerCoreEntry fr initial d peer) : fr.rsi = sp fr + 3456 := by
  rw [e.pairPtr]
  unfold sp
  bv_omega

theorem peerReadable {fr : Activation} {initial : Registers} {m : Ram} {d : Nat} {peer : Projective}
    (e : PeerCoreEntry fr initial d peer) (frame : RamWriteFrame fr.original m [fr.region]) :
    Readable m (sp fr + 3456) 120 := by
  rw [← pairOnStack e]
  exact (e.pairRead.of_frame frame).sub (Nat.le_refl _) (by omega)

private theorem choiceFlag (r : Int) : (if decide (r < 0) then (1 : BitVec 8) else 0) = flag r := by
  simp only [decide_eq_true_eq, flag]

private theorem choiceMagnitude (d : Nat) :
    (if decide (secondComponent d < 0) then negative (Curve.splitSecond d) else v d) =
      scalarWords (secondComponent d).natAbs := by
  have eq := selectMagnitude (x := Curve.splitSecond d) (Nat.mod_lt _ (by decide : 0 < domain.n))
  rw [show flag (Curve.centered (Curve.splitSecond d)) = flag (secondComponent d) from rfl,
    ← choiceFlag] at eq
  cases h : decide (secondComponent d < 0) <;>
    simpa only [h, Bool.false_eq_true, ↓reduceIte, (show (1 : BitVec 8) ≠ 0 by decide)] using eq

structure PeerSelectRegisters (fr : Activation) (a b : Registers) (d : Nat) : Prop where
  rsp : b[4] = ⟨64,sp fr - 8⟩
  dst : b[7] = ⟨64,sp fr + 0x328⟩
  src : b[6] = ⟨64,sp fr + 3456⟩
  neg : b[2] = ⟨64,sp fr + 0x3a0⟩
  firstFlag : (b[1].get 64).setWidth 8 = flag (firstComponent d)
  basePtr : b[5] = ⟨64,sp fr + 0x328⟩
  mask4 : b[3] = ⟨64,0x3ffffffffffffc⟩
  mask52 : b[12] = ⟨64,0xfffffffffffff⟩
  mask48 : b[14] = ⟨64,0xffffffffffff⟩
  workPtr : b[15] = ⟨64,sp fr + 0x1d0⟩
  keep : ∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → b[i] = a[i]
structure PeerSelectEntry (fr : Activation) (a b : Registers) (m q : Ram) (d : Nat) (peer : Projective) : Prop
    extends PeerSelectRegisters fr a b d where
  block : program.runBlock (dialect Extracted.programImage) ⟨.l11ccfd,a,m⟩ =
    .call ⟨.l10fcc0,b,memStore q (sp fr - 8) (0x11cf0d : Word)⟩ (callFrame .l11cf0d 0x11cf0d)
  frame : RamWriteFrame m q (writes fr selectWrites)
  magnitude : WordsAt q (sp fr + 0x290) 64 (scalarWords (secondComponent d).natAbs)
  peerStored : peer.Stored q (sp fr + 3456)
  negativeStored : peer.neg.Stored q (sp fr + 0x3a0)

private theorem selectStoreEq {m : Ram} {t : Word} {x y z : Limbs} (d : Nat) :
    stageSelect m t (if decide (secondComponent d < 0) then 1 else 0)
      (if decide (secondComponent d < 0) then negative (Curve.splitSecond d) else v d) x y z =
    stageSelect m t (flag (secondComponent d)) (scalarWords (secondComponent d).natAbs) x y z := by
  let selected := if decide (secondComponent d < 0) then negative (Curve.splitSecond d) else v d
  exact (congrArg (fun bit => stageSelect m t bit selected x y z) (choiceFlag (secondComponent d))).trans
    (congrArg (fun mag => stageSelect m t (flag (secondComponent d)) mag x y z) (choiceMagnitude d))

private theorem selectStoreCongr {fr : Activation} {a b : Registers} {m q r : Ram}
    (eq : q = r)
    (block : program.runBlock (dialect Extracted.programImage) ⟨.l11ccfd,a,m⟩ =
      .call ⟨.l10fcc0,b,memStore q (sp fr - 8) (0x11cf0d : Word)⟩ (callFrame .l11cf0d 0x11cf0d)) :
    program.runBlock (dialect Extracted.programImage) ⟨.l11ccfd,a,m⟩ =
      .call ⟨.l10fcc0,b,memStore r (sp fr - 8) (0x11cf0d : Word)⟩ (callFrame .l11cf0d 0x11cf0d) :=
  eq ▸ block

private theorem selectRegistersOfDispatch {fr : Activation} {a b : Registers} {m : Ram} {d : Nat} {peer : Projective}
    (s : PeerNegated fr a m d peer)
    (args :
      b[4] = ⟨64,sp fr - 8⟩ ∧ b[7] = ⟨64,sp fr + 0x328⟩ ∧ b[6] = ⟨64,sp fr + 3456⟩ ∧
      b[2] = ⟨64,sp fr + 0x3a0⟩ ∧ (b[1].get 64).setWidth 8 = flag (firstComponent d) ∧
      b[5] = ⟨64,sp fr + 0x328⟩ ∧ b[3] = a[3] ∧ b[12] = ⟨64,0xfffffffffffff⟩ ∧
      b[14] = ⟨64,0xffffffffffff⟩ ∧ b[15] = a[15] ∧
      ∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → b[i] = a[i]) :
    PeerSelectRegisters fr a b d := by
  obtain ⟨rsp,dst,src,neg,sign,ptr,mask4,mask52,mask48,work,keep⟩ := args
  exact ⟨rsp,dst,src,neg,sign,ptr,mask4.trans s.r3,mask52,mask48,work.trans s.r15,keep⟩

private theorem dispatchMagnitude {fr : Activation} {initial a : Registers} {m : Ram} {d : Nat} {peer : Projective}
    (e : PeerCoreEntry fr initial d peer) (s : PeerNegated fr a m d peer)
    {x y z : Limbs} (wx : WordsAt m (sp fr + 3456) 64 x)
    (wy : WordsAt m (sp fr + 3496) 64 y) (wz : WordsAt m (sp fr + 3536) 64 z)
    (src : Readable m (sp fr + 3456) 120) :
    let q := stageSelect m (sp fr) (flag (secondComponent d)) (scalarWords (secondComponent d).natAbs) x y z
    ∃ b, program.runBlock (dialect Extracted.programImage) ⟨.l11ccfd,a,m⟩ =
      .call ⟨.l10fcc0,b,memStore q (sp fr - 8) (0x11cf0d : Word)⟩ (callFrame .l11cf0d 0x11cf0d) ∧
      PeerSelectRegisters fr a b d := by
  have rsp : a[4] = ⟨64,sp fr⟩ := s.atoms.1
  have pair := pairOnStack e
  have zero := s.locals (8,0) (by simp [localValues])
  have pair₁ := (s.locals (0x38,fr.rsi) (by simp [localValues])).trans pair
  have pair₂ := (s.locals (0xb0,fr.rsi) (by simp [localValues])).trans pair
  obtain ⟨b,block,args⟩ :=
    peerDispatchSelect (t := sp fr) (p := v d) (q := negative (Curve.splitSecond d))
      (decide (secondComponent d < 0)) (get64OfEq rsp) (get64OfEq s.r3)
      (get64OfEq s.r12) (get64OfEq s.r13)
      (get64OfEq s.r14) (get64OfEq s.r5)
      zero pair₁ pair₂ s.firstSign (s.secondSign.trans (choiceFlag _).symm) s.negSecond wx wy wz
      (Start.peerCallerWindow e s.frame) src
  exact ⟨b,selectStoreCongr (fr := fr) (selectStoreEq d) block,selectRegistersOfDispatch s args⟩

theorem peerEnterSelect {fr : Activation} {initial a : Registers} {m : Ram} {d : Nat} {peer : Projective}
    (e : PeerCoreEntry fr initial d peer) (s : PeerNegated fr a m d peer) :
    ∃ b q, PeerSelectEntry fr a b m q d peer := by
  have apart := peerOutsidePair e
  have pair := pairOnStack e
  have p := e.stored.of_frame s.frame apart
  rw [pair] at p
  obtain ⟨x,y,z,wx,wy,wz,rx,ry,rz⟩ := p.coordinates
  let bit := flag (secondComponent d)
  let mag := scalarWords (secondComponent d).natAbs
  let q := stageSelect m (sp fr) bit mag x y z
  have wf : RamWriteFrame m q (writes fr selectWrites) := peerSelectFrame e m bit mag x y z
  have whole := s.frame.trans wf (peerWithin e (by decide))
  have stored := e.stored.of_frame whole apart
  rw [pair] at stored
  obtain ⟨mw,pneg⟩ := stagedValues (m := m) (t := sp fr) bit mag x y z rx ry rz
  obtain ⟨b,block,args⟩ :=
    dispatchMagnitude e s wx
      (by simpa only [Lift.reduceAddOffset, BitVec.reduceAdd] using wy)
      (by simpa only [Lift.reduceAddOffset, BitVec.reduceAdd] using wz) (peerReadable e s.frame)
  exact ⟨b,q,args,block,wf,mw,stored,pneg⟩

end K256.Proofs.Generate.Generator.Multiply.Prepare.Bases
