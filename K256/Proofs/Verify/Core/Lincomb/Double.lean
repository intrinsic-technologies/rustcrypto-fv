import K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic
import K256.Proofs.Verify.Core.Lincomb.Double.Memory
import K256.Proofs.Verify.Core.Lincomb.Double.SecondSquare
import K256.Proofs.Verify.Core.Lincomb.Double.StackFrame
import K256.Proofs.Verify.Core.Lincomb.Double.StackSquare
import K256.Proofs.Verify.Core.Affine.Call

namespace K256.Proofs.Verify.Core.Lincomb

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  K256.Proofs.Verify.LIR Common.Point Common.Field
open Generate.Generator.Multiply (Projective PointWordsAt)

set_option maxHeartbeats 1300000 in
theorem doubleWithWidths {a : Registers} {m : Ram} {sp dst src : BitVec 64} {p : Projective}
    (entry : RoutineEntry a m sp 0x298) (di : a[7].get 64 = dst) (si : a[6].get 64 = src)
    (read : Readable m src 120) (write : Writable Extracted.programImage m dst 120)
    (source : Outside [scratch sp 0x298, ⟨dst.toNat, 120⟩] src 120)
    (dest : Outside [scratch sp 0x298, ⟨sp.toNat, 8⟩] dst 120)
    (stored : p.Stored m src) (_valid : p.valid) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l110cd0, a, m⟩, []⟩ out ∧
      RoutineReturn a m sp 0x298 [⟨dst.toNat, 120⟩] out ∧
      ParseSignature.ArgumentWidths out.values ∧ p.double.Stored out.store dst := by
  let q := Double.localStack sp
  let m0 := Double.firstMemory a m sp src dst
  have srcApart : Outside [scratch sp 0x298] src 120 := by
    exact ⟨source.1, fun r hr => source.2 r (by
      rcases List.mem_singleton.mp hr with rfl
      exact .head _)⟩
  obtain ⟨b, callY, bSp, bSrc, bDst, bKeep, beforeY⟩ :=
    Double.firstSquareSetup entry si di read srcApart
  obtain ⟨point, dst0, linkY, saved0⟩ := Double.firstMemoryFacts entry srcApart stored
  obtain ⟨x,y,z,xAt,yAt,zAt,rx,ry,rz⟩ := point.coordinates
  have addr (k : Nat) : q + BitVec.ofNat 64 k = Double.below sp (112 + k) := by
    simp only [q,Double.localStack,Double.below,Double.bottom,BitVec.ofNat_add]
    bv_omega
  have child (k : Nat) : Double.childSp sp + BitVec.ofNat 64 k = Double.below sp (104 + k) := by
    simp only [Double.childSp,Double.below,Double.bottom,BitVec.ofNat_add]
    bv_omega
  have bSp' : b[4] = ⟨64,Double.childSp sp⟩ := by
    exact bSp.trans (congrArg (Value.mk 64) (by dsimp only [q, Double.localStack, Double.childSp]; bv_omega))
  have childRsp : Double.childSp sp + 8 = q := by
    dsimp only [q, Double.localStack, Double.childSp]
    bv_omega
  have srcY : Double.childSp sp + BitVec.ofNat 64 0x158 = (q + 0x128) + 40 := by
    dsimp only [q, Double.localStack, Double.childSp]
    bv_omega
  have shiftY : Double.childSp sp + BitVec.ofNat 64 0x1b0 = q + 0x1a8 := by
    dsimp only [q, Double.localStack, Double.childSp]
    bv_omega
  have bSrc' : b[6] = ⟨64,Double.childSp sp + BitVec.ofNat 64 0x158⟩ := by
    rw [srcY]
    exact bSrc.trans (congrArg (Value.mk 64) (by bv_omega))
  have bDst' : b[7] = ⟨64,Double.childSp sp + BitVec.ofNat 64 0x1b0⟩ := by
    rw [shiftY]
    exact bDst
  have linkY' : memLoad m0 (Double.childSp sp) 64 = 0x110d0e := by
    rw [show Double.childSp sp = q - 8 by dsimp only [q,Double.localStack,Double.childSp]; bv_omega]
    exact linkY
  have yAt' : WordsAt m0 (Double.childSp sp + BitVec.ofNat 64 0x158) 64 y := srcY.symm ▸ yAt
  obtain ⟨cy, runY, tagY, cySp, cyKeep, yWrite, fY, yy⟩ :=
    Double.squareOnStack entry beforeY bKeep bSp' bSrc' bDst' (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) linkY' (by decide) yAt'
  have reachY := Affine.resumeCoreCall callY runY tagY
  have bound : (Double.bottom sp).toNat + 0x298 ≤ 2^32 := entry.stack.readable.low
  have childBase : q - 8 = Double.below sp 104 := by
    dsimp only [q,Double.localStack,Double.below,Double.bottom]
    bv_omega
  have window : Writable Extracted.programImage cy.store (q - 8) 0x1f8 := by
    rw [childBase]
    exact (entry.stack.of_frame fY).of_offsets rfl (addr_self _) (by decide)
  obtain ⟨c, callZ, cSp, cSrc, cDst, cKeep, linkZ, copies, copyWrite⟩ :=
    Double.secondSquareSetup ((congrArg (Value.get 64) cySp).trans childRsp) window (shiftY ▸ yy)
  let m1 := memStore (Double.saveYSquare cy.store q (squareWords y)) (q - 8) (0x110d64 : BitVec 64)
  have gCopy : RamWriteFrame cy.store m1 (Double.windows sp [(104,112)]) := by
    change RamWriteFrame cy.store m1 [⟨(Double.below sp 104).toNat,112⟩]
    rw [← childBase]
    exact copyWrite
  have fCopy : RamWriteFrame m m1 [scratch sp 0x298] :=
    fY.trans gCopy (Double.windowsWithin entry.room bound (by decide))
  have zSrc : (q + 0x128) + 80 = Double.childSp sp + BitVec.ofNat 64 0x180 := by
    dsimp only [q,Double.localStack,Double.childSp]
    bv_omega
  have zDst : q + 0x1d0 = Double.childSp sp + BitVec.ofNat 64 0x1d8 := by
    dsimp only [q,Double.localStack,Double.childSp]
    bv_omega
  have bottomZero : Double.below sp 0 = sp - 0x298 := BitVec.add_zero _
  have dy : RamWriteFrame m0 cy.store (Double.windows sp [(0,104),(536,40)]) := by
    change RamWriteFrame _ _ [⟨(Double.below sp 0).toNat,104⟩,⟨(Double.below sp 536).toNat,40⟩]
    rw [bottomZero, ← child 0x1b0]
    exact yWrite
  have zAt₁ : WordsAt m1 (Double.childSp sp + BitVec.ofNat 64 0x180) 64 z := by
    rw [← zSrc]
    have address : (q + 0x128) + 80 = Double.below sp 488 := by
      calc
        _ = q + BitVec.ofNat 64 0x178 := by bv_omega
        _ = _ := addr _
    apply (zAt.of_frame dy (by decide) ?_).of_frame gCopy (by decide)
    all_goals
      rw [address]
      exact Double.outsideWindows bound (by decide) (by decide) (by decide)
  have cSp' : c[4] = ⟨64,Double.childSp sp⟩ := by
    exact cSp.trans (congrArg (Value.mk 64) (by dsimp only [q,Double.localStack,Double.childSp]; bv_omega))
  have cSrc' : c[6] = ⟨64,Double.childSp sp + BitVec.ofNat 64 0x180⟩ := by
    rw [← zSrc]
    exact cSrc.trans (congrArg (Value.mk 64) (by bv_omega))
  have cDst' : c[7] = ⟨64,Double.childSp sp + BitVec.ofNat 64 0x1d8⟩ := by
    rw [← zDst]
    exact cDst
  have linkZ' : memLoad m1 (Double.childSp sp) 64 = 0x110d64 := by
    rw [show Double.childSp sp = q - 8 by dsimp only [q,Double.localStack,Double.childSp]; bv_omega]
    exact linkZ
  obtain ⟨cz, runZ, tagZ, czSp, czKeep, zWrite, fZ, zz⟩ :=
    Double.squareOnStack entry fCopy (fun i hi => (cKeep i hi).trans (cyKeep i hi)) cSp' cSrc' cDst'
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) linkZ' (by decide) zAt₁
  have reachZ := Affine.resumeCoreCall callZ runZ tagZ
  have dz : RamWriteFrame m1 cz.store (Double.windows sp [(0,104),(576,40)]) := by
    change RamWriteFrame _ _ [⟨(Double.below sp 0).toNat,104⟩,⟨(Double.below sp 576).toNat,40⟩]
    rw [bottomZero, ← child 0x1d8]
    exact zWrite
  have keepLoad {k : Nat} (fit : k + 8 ≤ 0x298)
      (sepY : ∀ r ∈ [(0,104),(536,40)], k+8 ≤ r.1 ∨ r.1+r.2 ≤ k)
      (sepCopy : ∀ r ∈ [(104,112)], k+8 ≤ r.1 ∨ r.1+r.2 ≤ k)
      (sepZ : ∀ r ∈ [(0,104),(576,40)], k+8 ≤ r.1 ∨ r.1+r.2 ≤ k) :
      memLoad cz.store (Double.below sp k) 64 = memLoad m0 (Double.below sp k) 64 :=
    (dz.memLoad_eq (Double.outsideWindows bound fit (by decide) sepZ)).trans
      ((gCopy.memLoad_eq (Double.outsideWindows bound fit (by decide) sepCopy)).trans
        (dy.memLoad_eq (Double.outsideWindows bound fit (by decide) sepY)))
  have keepWords {k : Nat} {v : Limbs} (before : WordsAt m0 (Double.below sp k) 64 v)
      (fit : k+40 ≤ 0x298)
      (sepY : ∀ r ∈ [(0,104),(536,40)], k+40 ≤ r.1 ∨ r.1+r.2 ≤ k)
      (sepCopy : ∀ r ∈ [(104,112)], k+40 ≤ r.1 ∨ r.1+r.2 ≤ k)
      (sepZ : ∀ r ∈ [(0,104),(576,40)], k+40 ≤ r.1 ∨ r.1+r.2 ≤ k) :
      WordsAt cz.store (Double.below sp k) 64 v := by
    have y := before.of_frame dy (by decide) (Double.outsideWindows bound fit (by decide) sepY)
    have c := y.of_frame gCopy (by decide) (Double.outsideWindows bound fit (by decide) sepCopy)
    exact c.of_frame dz (by decide) (Double.outsideWindows bound fit (by decide) sepZ)
  let w : PointWords := ⟨x,y,z⟩
  have xAddr : q + 0x128 = Double.below sp 408 := addr 0x128
  have yAddr : (q + 0x128) + 40 = Double.below sp 448 := by
    calc
      _ = q + BitVec.ofNat 64 0x150 := by bv_omega
      _ = _ := addr _
  have zAddr : (q + 0x128) + 80 = Double.below sp 488 := zSrc.trans (child 0x180)
  have wp : PointWordsAt cz.store (q + 0x128) w :=
    ⟨xAddr.symm ▸ keepWords (xAddr ▸ xAt) (by decide) (by decide) (by decide) (by decide),
     yAddr.symm ▸ keepWords (yAddr ▸ yAt) (by decide) (by decide) (by decide) (by decide),
     zAddr.symm ▸ keepWords (zAddr ▸ zAt) (by decide) (by decide) (by decide) (by decide)⟩
  have dst' : memLoad cz.store (q + 0x1a0) 64 = dst := by
    rw [show q + 0x1a0 = Double.below sp 528 from addr 0x1a0, keepLoad (by decide) (by decide) (by decide) (by decide)]
    exact (addr 0x1a0) ▸ dst0
  have yy' (i : Fin 5) : memLoad cz.store (q + Double.ySquareSlots[i]) 64 = (squareWords w.y)[i] := by
    refine (dz.memLoad_eq ?_).trans (copies i)
    rcases i with ⟨j,hj⟩
    rcases (by omega : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4) with rfl|rfl|rfl|rfl|rfl
    · rw [show Double.ySquareSlots[(⟨0, hj⟩ : Fin 5)] = 0x20 from rfl]
      change Outside _ (q + BitVec.ofNat 64 0x20) 8
      rw [addr 0x20]
      exact Double.outsideWindows bound (by decide) (by decide) (by decide)
    · rw [show Double.ySquareSlots[(⟨1, hj⟩ : Fin 5)] = 0x28 from rfl]
      change Outside _ (q + BitVec.ofNat 64 0x28) 8
      rw [addr 0x28]
      exact Double.outsideWindows bound (by decide) (by decide) (by decide)
    · rw [show Double.ySquareSlots[(⟨2, hj⟩ : Fin 5)] = 0x48 from rfl]
      change Outside _ (q + BitVec.ofNat 64 0x48) 8
      rw [addr 0x48]
      exact Double.outsideWindows bound (by decide) (by decide) (by decide)
    · rw [show Double.ySquareSlots[(⟨3, hj⟩ : Fin 5)] = 0x60 from rfl]
      change Outside _ (q + BitVec.ofNat 64 0x60) 8
      rw [addr 0x60]
      exact Double.outsideWindows bound (by decide) (by decide) (by decide)
    · rw [show Double.ySquareSlots[(⟨4, hj⟩ : Fin 5)] = 0x40 from rfl]
      change Outside _ (q + BitVec.ofNat 64 0x40) 8
      rw [addr 0x40]
      exact Double.outsideWindows bound (by decide) (by decide) (by decide)
  have savedZ (i : Fin 6) :
      (⟨64,memLoad cz.store (sp - BitVec.ofNat 64 (8*(i.val+1))) 64⟩ : Value) =
        a[(#v[5,15,14,13,12,3] : Vector (Fin Reg.count) 6)[i]] := by
    have hi := i.isLt
    have k : 8*(i.val+1) ≤ 0x298 := by omega
    have aSave : sp - BitVec.ofNat 64 (8*(i.val+1)) = Double.below sp (0x298 - 8*(i.val+1)) := by
      simp only [Double.below,Double.bottom]
      rw [← BitVec.ofNat_sub_ofNat_of_le (w := 64) _ _ (by omega) k]
      bv_omega
    have lk : memLoad cz.store (Double.below sp (0x298 - 8*(i.val+1))) 64 =
        memLoad m0 (Double.below sp (0x298 - 8*(i.val+1))) 64 := by
      refine keepLoad (by omega) ?_ ?_ ?_
      · intro r hr
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl|rfl <;> omega
      · intro r hr
        rcases List.mem_singleton.mp hr with rfl
        omega
      · intro r hr
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl|rfl <;> omega
    rw [aSave, lk, ← aSave]
    exact saved0 i
  have rspz : cz.values[4] = ⟨64,q⟩ := czSp.trans (congrArg (Value.mk 64) childRsp)
  have keepz (i : Fin Reg.count) (hi : i.val ∈ [22,39,50,51]) : cz.values[i] = a[i] :=
    czKeep i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega)
  obtain ⟨out, run, ret, widths, result⟩ :=
    Double.arithmeticBody entry rspz keepz fZ savedZ dst' write dest wp ⟨rx,ry,rz⟩ yy' (zDst.symm ▸ zz)
  exact ⟨out, Program.Exec.of_sem ((reachY.trans reachZ).exec run.sem), ret, widths, result⟩

theorem double {a : Registers} {m : Ram} {sp dst src : BitVec 64} {p : Projective}
    (entry : RoutineEntry a m sp 0x298) (di : a[7].get 64 = dst) (si : a[6].get 64 = src)
    (read : Readable m src 120) (write : Writable Extracted.programImage m dst 120)
    (source : Outside [scratch sp 0x298, ⟨dst.toNat, 120⟩] src 120)
    (dest : Outside [scratch sp 0x298, ⟨sp.toNat, 8⟩] dst 120)
    (stored : p.Stored m src) (valid : p.valid) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l110cd0, a, m⟩, []⟩ out ∧
      RoutineReturn a m sp 0x298 [⟨dst.toNat, 120⟩] out ∧ p.double.Stored out.store dst := by
  obtain ⟨out,run,ret,_,result⟩ := doubleWithWidths entry di si read write source dest stored valid
  exact ⟨out,run,ret,result⟩

end K256.Proofs.Verify.Core.Lincomb
