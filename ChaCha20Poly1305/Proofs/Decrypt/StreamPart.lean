import ChaCha20Poly1305.Proofs.Decrypt.FullRepeat
import ChaCha20Poly1305.Proofs.Decrypt.ControlSpill
import ChaCha20Poly1305.Proofs.Decrypt.ControlPrepare
import ChaCha20Poly1305.Proofs.Decrypt.ControlUpdate

namespace ChaCha20Poly1305.Proofs.Decrypt.Stream.Control
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program
set_option allowUnsafeReducibility true in
attribute [local reducible] ChaCha20Poly1305.Proofs.Decrypt.Lifted.lifted
set_option maxHeartbeats 800000
set_option maxRecDepth 5000
set_option pp.maxSteps 160

def count (x : Input) := x.n.toNat/64

def stageFrame (x : Input) (fr : Activation) : List MemoryRegion :=
  [⟨fr.rsp.toNat,368⟩,⟨x.buf.toNat,64*count x⟩,⟨fr.rdi.toNat+48,4⟩]

structure BeforeTail (x : Input) (fr : Activation) (m : Ram) (c : lifted.Location) : Prop where
  label : c.label = .l1010cc
  registers : Atom.All fnCode c.arguments c.store (Full.registers fr ++
    [.gpr 7 fr.rdi,.gpr 11 x.n,.gpr 15 (Tail.rem64 x.n)])
  saved : Atom.All fnCode c.arguments c.store (fullSaved x fr)
  words : Atom.All fnCode c.arguments c.store (state (atBlock x (count x)) fr.rdi)
  frame : RamWriteFrame m c.store (stageFrame x fr)
  data : ∀ k, k<64*count x → Xor.readAt c.store x.buf k = streamByte x k ^^^ Xor.readAt m x.buf k

theorem beforeFull (x : Input) (fr : Activation) (a : lifted.Location) (s : Scope x fr a.store)
    (pos : 0 < count x) (hl : a.label = .l100bde)
    (atSpill : Atom.All fnCode a.arguments a.store (spillStep x fr true).post)
    (st : Atom.All fnCode a.arguments a.store (state x fr.rdi)) :
    Ahead lifted fnCode (BeforeTail x fr a.store) a := by
  have stack := s.stack
  have ctx := s.ctx
  have stackLow := stack.readable.low
  have ctxLow := ctx.readable.low
  have bufLow := s.buf.readable.low
  have sc := s.stackCode
  have cs := s.stackCtx
  have bs := s.stackBuf
  have cb := s.ctxBuf
  have fbound : 64*count x ≤ x.n.toNat := by unfold count; omega
  have saved := ((Atom.all_append _ _).mp atSpill).2
  change Atom.All _ _ _ (fullSaved x fr) at saved
  obtain ⟨b,ab,bl,ba,bf⟩ := Micro.run (prepareValid x fr) hl (by
    apply (Atom.all_append _ _).2 ⟨?_,st⟩
    unpack_atoms atSpill []
    join_atoms []
    all_goals first | assumption | (apply ctx.readable.sub <;> omega) | omega)
  change RamWriteFrame _ _ (prepareStep x fr).writes at bf
  have br : Atom.All fnCode b.arguments b.store (fullSaved x fr) := by
    apply ChaChaRound.keepFrame _ bf saved
    intro t ht
    simp only [fullSaved,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp [ChaChaRound.pass,Outside,prepareStep] <;> bv_omega
  have pp := fullPrefix x fr b (s.after bf) pos bl (by
    unpack_atoms ba []
    join_atoms []
    all_goals first | assumption | (simp_all only [BitVec.ofNat_eq_ofNat,BitVec.add_zero]))
    (by
      unpack_atoms br []
      unpack_atoms ba []
      join_atoms []
      all_goals assumption) (count x) (Nat.le_refl _)
  obtain ⟨c,bc,hc⟩ := pp
  have cc : c.label = Lifted.Label.l1010b3 := by
    have t := hc.label
    simpa only [count,ite_true] using t
  have cf := hc.frame
  have cr : Atom.All fnCode c.arguments c.store (fullSaved x fr) := by
    apply ChaChaRound.keepFrame _ cf br
    intro t ht
    simp only [fullSaved,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp [ChaChaRound.pass,Outside,prefixFrame,blockScratch] <;> bv_omega
  let y := atBlock x (count x)
  have current := (s.after bf).after cf
  obtain ⟨d,cd,dl,da,df⟩ := Micro.run (updateValid y fr) cc (by
    have cw := current.ctx
    have sw := current.stack
    have read : Readable c.store fr.rsp 176 := sw.readable.sub (Nat.le_refl _) (by omega)
    have write : Writable fnCode c.store fr.rdi 64 := cw.sub (Nat.le_refl _) (by omega)
    have code := current.ctxCode
    have regs := hc.regs
    unpack_atoms regs []
    unpack_atoms cr []
    join_atoms [y,atBlock,Vector.getElem_set,UInt32.toBitVec_add]
    all_goals first | assumption | omega | rfl)
  have ds : Atom.All fnCode d.arguments d.store (fullSaved x fr) := by
    apply ChaChaRound.keepFrame _ df cr
    intro t ht
    simp only [fullSaved,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp [ChaChaRound.pass,Outside,updateStep] <;> bv_omega
  have frame : RamWriteFrame a.store d.store (stageFrame x fr) := by
    apply ((RamWriteFrame.refl a.store _).trans bf _ |>.trans cf _) |>.trans df
    all_goals simp [RegionsWithin,stageFrame,prepareStep,updateStep,prefixFrame,blockScratch] <;> omega
  refine ⟨d,jumpTrans ab (jumpTrans bc cd),dl,?_,ds,?_,frame,?_⟩
  · unpack_atoms da []
    join_atoms [y,atBlock]
    all_goals assumption
  · have word : memLoad d.store (fr.rdi+48) 32 = y.w[12].toBitVec := by
      exact da.2.2.2.2.2.2.2.2.1
    unpack_atoms st []
    simp only [stageFrame] at frame
    clear df cf bf
    join_atoms [atBlock,Vector.getElem_set,y]
    all_goals first | assumption | (simp; done) | (simpa [y,atBlock] using word)
  · intro k hk
    have loc : (x.buf+BitVec.ofNat 64 k).toNat = x.buf.toNat+k := Xor.ptrNat (by omega)
    have endSame : Xor.readAt d.store x.buf k = Xor.readAt c.store x.buf k := by
      apply df.memLoad_eq; simp [Outside,updateStep,loc]; omega
    have begSame : Xor.readAt b.store x.buf k = Xor.readAt a.store x.buf k := by
      apply bf.memLoad_eq; simp [Outside,prepareStep,loc]; omega
    rw [endSame,hc.data k hk,begSame]

end ChaCha20Poly1305.Proofs.Decrypt.Stream.Control
