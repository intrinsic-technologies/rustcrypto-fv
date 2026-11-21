import ChaCha20Poly1305.Proofs.Decrypt.StreamPart

namespace ChaCha20Poly1305.Proofs.Decrypt.Stream.Control
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program
set_option allowUnsafeReducibility true in
attribute [local reducible] ChaCha20Poly1305.Proofs.Decrypt.Lifted.lifted
set_option maxHeartbeats 600000
set_option maxRecDepth 6000

private theorem spillWords {x : Input} {fr a b flag rs rs'} (s : Scope x fr a)
    (f : RamWriteFrame a b (spillStep x fr flag).writes) (h : Atom.All fnCode rs a (state x fr.rdi)) :
    Atom.All fnCode rs' b (state x fr.rdi) := by
  apply ChaChaRound.keepFrame _ f h
  have := s.stack.readable.low
  have := s.ctx.readable.low
  have := s.stackCtx
  intro t ht
  simp only [state,List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp [ChaChaRound.pass,Outside,spillStep] <;> bv_omega

theorem fromBase (x : Input) (fr : Activation) (a : lifted.Location) (s : Scope x fr a.store)
    (hl : a.label = .l100ba5) (ready : Atom.All fnCode a.arguments a.store (spillStep x fr false).pre)
    (st : Atom.All fnCode a.arguments a.store (state x fr.rdi)) :
    Ahead lifted fnCode (BeforeTail x fr a.store) a := by
  let flag := decide (0 < count x)
  have eq : x.n >>> 6 ≠ 0 ↔ flag=true := by
    have z : x.n >>> 6 = 0 ↔ count x = 0 :=
      ⟨fun h => (blocksNat x).symm.trans (congrArg BitVec.toNat h),
       fun h => BitVec.eq_of_toNat_eq ((blocksNat x).trans h)⟩
    simp only [flag,decide_eq_true_eq,Nat.pos_iff_ne_zero,ne_eq,z]
  obtain ⟨b,ab,bl,post,f⟩ := Micro.run (spillValid x fr flag eq) hl ready
  have bs := spillWords (rs' := b.arguments) s f st
  have ff : RamWriteFrame a.store b.store (stageFrame x fr) := by
    apply (RamWriteFrame.refl a.store _).trans f
    simp [RegionsWithin,stageFrame,spillStep]
  change b.label = (if flag then Lifted.Label.l100bde else Lifted.Label.l1010cc) at bl
  by_cases pos : 0<count x
  · rw [ite_eq_left (show flag=true by simp [flag,pos])] at bl
    obtain ⟨c,bc,hc⟩ := beforeFull x fr b (s.after f) pos bl post bs
    refine ⟨c,jumpTrans ab bc,{hc with frame := ff.trans hc.frame (fun r hr => ⟨r,hr,Nat.le_refl _,Nat.le_refl _⟩),data := ?_}⟩
    intro k hk
    rw [hc.data k hk]
    congr 1
    apply f.memLoad_eq
    have low := s.buf.readable.low
    have apart := s.stackBuf
    have le : 64*count x ≤ x.n.toNat := by unfold count; omega
    have p : (x.buf+BitVec.ofNat 64 k).toNat=x.buf.toNat+k := Xor.ptrNat (by omega)
    simp [Outside,spillStep,p]; omega
  · rw [ite_eq_right (show ¬flag=true by simp [flag,pos])] at bl
    have zero : count x=0 := by omega
    refine ⟨b,ab,bl,?_,((Atom.all_append _ _).1 post).2,?_,ff,by intro k hk; omega⟩
    · unpack_atoms post []
      join_atoms []
      all_goals assumption
    · rw [zero,atBlock_zero]; exact bs

end ChaCha20Poly1305.Proofs.Decrypt.Stream.Control
