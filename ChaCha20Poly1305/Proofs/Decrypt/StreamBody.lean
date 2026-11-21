import ChaCha20Poly1305.Proofs.Decrypt.StreamBase
import ChaCha20Poly1305.Proofs.Decrypt.TailRun
import ChaCha20Poly1305.Proofs.Decrypt.ControlTestTail

namespace ChaCha20Poly1305.Proofs.Decrypt.Stream.Control
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program
set_option allowUnsafeReducibility true in
attribute [local reducible] ChaCha20Poly1305.Proofs.Decrypt.Lifted.lifted Tail.layout
set_option maxHeartbeats 600000
set_option maxRecDepth 6000
set_option pp.maxSteps 120

def bodyFrame (x : Input) (fr : Activation) : List MemoryRegion :=
  [⟨fr.rsp.toNat,368⟩,⟨fr.rdi.toNat+48,4⟩,⟨fr.rdi.toNat+64,64⟩,⟨x.buf.toNat,x.n.toNat⟩]

theorem body (x : Input) (fr : Activation) (a : lifted.Location) (s : Scope x fr a.store)
    (hl : a.label = .l100ba5) (ready : Atom.All fnCode a.arguments a.store (spillStep x fr false).pre)
    (st : Atom.All fnCode a.arguments a.store (state x fr.rdi)) :
    Ahead lifted fnCode (fun b => b.label = .l1014a8 ∧
      Atom.All fnCode b.arguments b.store (Full.registers fr) ∧ RamWriteFrame a.store b.store (bodyFrame x fr) ∧
      ∀ k, k<x.n.toNat → Xor.readAt b.store x.buf k = streamByte x k ^^^ Xor.readAt a.store x.buf k) a := by
  obtain ⟨b,ab,prev⟩ := fromBase x fr a s hl ready st
  let flag := decide (Tail.rem64 x.n ≠ 0)
  obtain ⟨c,bc,cl,ca,cf⟩ := Micro.run (testTailValid x fr flag (by simp [flag])) prev.label prev.registers
  change RamWriteFrame b.store c.store [] at cf
  have stage := prev.frame.trans cf (by intro r hr; simp at hr)
  have bound : 64*count x ≤ x.n.toNat := by unfold count; omega
  have floor := baseNat x
  have remn := remNat x
  have sLow := s.stack.readable.low
  have cLow := s.ctx.readable.low
  have bLow := s.buf.readable.low
  have sb := s.stackBuf
  have cb := s.ctxBuf
  have cs := s.stackCtx
  have wider : RamWriteFrame a.store c.store (bodyFrame x fr) :=
    (RamWriteFrame.refl a.store _).trans stage (by simp [RegionsWithin,stageFrame,bodyFrame]; omega)
  change c.label = (if flag then Lifted.Label.l1010d5 else Lifted.Label.l1014a8) at cl
  let y := atBlock x (count x)
  have scl := s.after stage
  have regs := ((Atom.all_append _ _).1 ca).1
  by_cases zero : Tail.rem64 x.n = 0
  · rw [ite_eq_right (show ¬flag=true by simp [flag,zero])] at cl
    refine ⟨c,jumpTrans ab bc,cl,regs,wider,?_⟩
    intro k hk
    rw [noChange cf,prev.data]
    rw [zero] at remn
    change 0 = _ at remn
    unfold count; omega
  · rw [ite_eq_left (show flag=true from decide_eq_true zero)] at cl
    have pos : 0 < (Tail.rem64 x.n).toNat := by apply Nat.pos_of_ne_zero; intro h; exact zero (BitVec.eq_of_toNat_eq h)
    have me : b.store = c.store := Std.ExtHashMap.ext_getElem? (fun k => (cf.outside k (by simp [Outside]; have := k.isLt; omega)).symm)
    have saved := prev.saved
    have words := prev.words
    rw [me] at saved words
    have ss := scl.stack
    have cw := scl.ctx
    have code := scl.stackCode
    have code' := scl.ctxCode
    have wr : Writable fnCode c.store fr.rsp 176 := ss.sub (Nat.le_refl _) (by omega)
    have enter : Atom.All fnCode c.arguments c.store ((Tail.layout y).atoms .setup fr ()) := by
      change Atom.All _ _ _ ((Tail.registers fr ++ Tail.common y fr) ++
        ([.gpr 7 fr.rdi,.gpr 11 x.n] ++ state y fr.rdi))
      apply (Atom.all_append _ _).2 ⟨(Atom.all_append _ _).2 ⟨regs,?_⟩, (Atom.all_append _ _).2 ⟨((Atom.all_append _ _).1 ca).2,?_⟩⟩
      · exact ⟨wr,cw,by change fr.rsp.toNat+176 ≤ 0x1010d5 ∨ 0x101420 ≤ fr.rsp.toNat; omega,
          by change fr.rdi.toNat+128 ≤ 0x1010d5 ∨ 0x101420 ≤ fr.rdi.toNat; omega,
          by change fr.rsp.toNat+176 ≤ fr.rdi.toNat ∨ fr.rdi.toNat+128 ≤ fr.rsp.toNat; omega,saved.1,saved.2.2.2.2.2.1,saved.2.2.2.2.2.2.1,trivial⟩
      · change Atom.All fnCode b.arguments c.store (state y fr.rdi) at words
        unfold state at words ⊢
        exact words
    have ptrs : Atom.All fnCode c.arguments c.store (tailSaved y fr) := by
      exact ⟨saved.2.2.1,saved.2.2.2.1,saved.2.2.2.2.1,trivial⟩
    obtain ⟨d,cd,dl,dr,df,dv⟩ := runTail y fr c ⟨scl.stack,scl.ctx,scl.buf,scl.stackCode,scl.ctxCode,scl.bufCode,scl.stackCtx,scl.stackBuf,scl.ctxBuf⟩ pos cl enter ptrs
    change RamWriteFrame c.store d.store (tailFrame x fr) at df
    have tp : (tailPtr x).toNat = x.buf.toNat+64*count x := by unfold tailPtr count; bv_omega
    refine ⟨d,jumpTrans ab (jumpTrans bc cd),dl,dr,wider.trans df ?_,?_⟩
    · simp [RegionsWithin,bodyFrame,tailFrame,tp,count]; omega
    · intro k hk
      have kp : (x.buf+BitVec.ofNat 64 k).toNat = x.buf.toNat+k := Xor.ptrNat (by omega)
      by_cases pre : k < 64*count x
      · have endEq : Xor.readAt d.store x.buf k = Xor.readAt c.store x.buf k := by
          apply df.memLoad_eq
          simp [Outside,tailFrame,tp,kp]; omega
        rw [endEq,noChange cf,prev.data _ pre]
      · let i := k-64*count x
        have hi : i < (Tail.rem64 x.n).toNat := by dsimp [i,count] at *; omega
        have eq : 64*count x+i=k := by dsimp [i]; omega
        have rd (m : Ram) : Xor.readAt m (tailPtr y) i = Xor.readAt m x.buf k := by
          change Xor.readAt m (tailPtr x) i = _
          have base : Tail.base64 x.n = BitVec.ofNat 64 (64*count x) := by
            apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
            unfold count; omega
          simp only [Xor.readAt,tailPtr,base,BitVec.add_assoc,← BitVec.ofNat_add,eq]
        have init : Xor.readAt c.store x.buf k = Xor.readAt a.store x.buf k := by
          apply stage.memLoad_eq
          simp [Outside,stageFrame,kp]; omega
        have out := dv i hi
        rw [rd,rd,init] at out
        simpa only [streamByte,show k/64=count x by unfold count at *; omega,
          show k%64=i by dsimp [i,count] at *; omega,y] using out

end ChaCha20Poly1305.Proofs.Decrypt.Stream.Control
