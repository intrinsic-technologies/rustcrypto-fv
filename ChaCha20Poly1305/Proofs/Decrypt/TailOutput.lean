import ChaCha20Poly1305.Proofs.Decrypt.TailKernelAll
import ChaCha20Poly1305.Proofs.Decrypt.StreamScope

namespace ChaCha20Poly1305.Proofs.Decrypt.Stream.Control
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program
set_option allowUnsafeReducibility true in
attribute [local reducible] ChaCha20Poly1305.Proofs.Decrypt.Lifted.lifted Tail.layout
set_option maxHeartbeats 600000
set_option maxRecDepth 6000

@[refine_layout] def tailSaved (x : Input) (fr : Activation) : List Atom :=
  [.mem (fr.rsp+136) 64 x.buf,.mem (fr.rsp+144) 64 x.buf,.mem (fr.rsp+152) 64 0]

private theorem extractTail {x : Input} {fr : Activation} {a : lifted.Location}
    (h : Atom.All fnCode a.arguments a.store ((Tail.layout x).atoms .four fr ())) :
    WordsAt a.store (fr.rdi+64) 32 (sums x.w) := by
  let hh := ((Atom.all_append _ _).mp (show Atom.All _ _ _ ((Tail.registers fr ++ Tail.common x fr) ++ _) from h)).2
  intro i hi
  simp only [sums,Vector.getElem_ofFn,Fin.getElem_fin]
  rcases (show i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 ∨ i=15 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [show wordAddr (fr.rdi+64) 32 0 = fr.rdi+64 by simp [wordAddr]]
    exact hh.2.2.2.2.2.2.1
  · rw [show wordAddr (fr.rdi+64) 32 1 = fr.rdi+68 by simp [wordAddr,BitVec.add_assoc]]
    exact hh.2.2.2.2.2.2.2.1
  · rw [show wordAddr (fr.rdi+64) 32 2 = fr.rdi+72 by simp [wordAddr,BitVec.add_assoc]]
    exact hh.2.2.2.2.2.2.2.2.1
  · rw [show wordAddr (fr.rdi+64) 32 3 = fr.rdi+76 by simp [wordAddr,BitVec.add_assoc]]
    exact hh.2.2.2.2.2.2.2.2.2.1
  · rw [show wordAddr (fr.rdi+64) 32 4 = fr.rdi+80 by simp [wordAddr,BitVec.add_assoc]]
    exact hh.2.2.2.2.2.2.2.2.2.2.1
  · rw [show wordAddr (fr.rdi+64) 32 5 = fr.rdi+84 by simp [wordAddr,BitVec.add_assoc]]
    exact hh.2.2.2.2.2.2.2.2.2.2.2.1
  · rw [show wordAddr (fr.rdi+64) 32 6 = fr.rdi+88 by simp [wordAddr,BitVec.add_assoc]]
    exact hh.2.2.2.2.2.2.2.2.2.2.2.2.1
  · rw [show wordAddr (fr.rdi+64) 32 7 = fr.rdi+92 by simp [wordAddr,BitVec.add_assoc]]
    exact hh.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · rw [show wordAddr (fr.rdi+64) 32 8 = fr.rdi+96 by simp [wordAddr,BitVec.add_assoc]]
    exact hh.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · rw [show wordAddr (fr.rdi+64) 32 9 = fr.rdi+100 by simp [wordAddr,BitVec.add_assoc]]
    exact hh.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · rw [show wordAddr (fr.rdi+64) 32 10 = fr.rdi+104 by simp [wordAddr,BitVec.add_assoc]]
    exact hh.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · rw [show wordAddr (fr.rdi+64) 32 11 = fr.rdi+108 by simp [wordAddr,BitVec.add_assoc]]
    exact hh.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · rw [show wordAddr (fr.rdi+64) 32 12 = fr.rdi+112 by simp [wordAddr,BitVec.add_assoc]]
    exact hh.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · rw [show wordAddr (fr.rdi+64) 32 13 = fr.rdi+116 by simp [wordAddr,BitVec.add_assoc]]
    exact hh.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · rw [show wordAddr (fr.rdi+64) 32 14 = fr.rdi+120 by simp [wordAddr,BitVec.add_assoc]]
    exact hh.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · rw [show wordAddr (fr.rdi+64) 32 15 = fr.rdi+124 by simp [wordAddr,BitVec.add_assoc]]
    exact hh.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem tailOutput (x : Input) (fr : Activation) (a : lifted.Location) (s : Scope x fr a.store)
    (hl : a.label = .l1010d5)
    (hin : Atom.All fnCode a.arguments a.store ((Tail.layout x).atoms .setup fr ()))
    (save : Atom.All fnCode a.arguments a.store (tailSaved x fr)) :
    Ahead lifted fnCode (fun b =>
      (b.label : Lifted.Label) = (if (Tail.rem64 x.n).toNat<4 then Lifted.Label.l1013bf else Lifted.Label.l1013e3) ∧
      Atom.All fnCode b.arguments b.store (Full.registers fr ++ tailState x fr) ∧
      WordsAt b.store (fr.rdi+64) 32 (sums x.w) ∧ RamWriteFrame a.store b.store ((Tail.layout x).regions fr)) a := by
  let snap := {fr with original := a.store}
  have start : (Tail.layout x).Rel fnCode snap (unitLoc .setup) a :=
    ⟨hl,⟨(),rfl,rfl,hin⟩,.refl _ _⟩
  obtain ⟨b,ab,ready⟩ := Tail.run x start
  let next := if (Tail.rem64 x.n).toNat<4 then Tail.Label.one else Tail.Label.four
  obtain ⟨c,bc,l,⟨_,_,_,out⟩,f⟩ := segment (Tail.layout x) (j := next) (Tail.storeStep x) rfl ready
  change RamWriteFrame a.store c.store ((Tail.layout x).regions fr) at f
  have dst : Atom.All fnCode c.arguments c.store ((Tail.layout x).atoms .four fr ()) := by
    change Atom.All _ _ _ ((Tail.layout x).atoms next fr ()) at out
    by_cases hp : (Tail.rem64 x.n).toNat<4 <;> simp only [next,hp,ite_true,ite_false] at out <;> exact out
  have kept : Atom.All fnCode c.arguments c.store (tailSaved x fr) := by
    apply ChaChaRound.keepFrame _ f save
    have := s.stackCtx
    have := s.stack.readable.low
    have := s.ctx.readable.low
    intro t ht
    simp only [tailSaved,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl|rfl|rfl <;> simp [ChaChaRound.pass,Outside] <;> bv_omega
  refine ⟨c,jumpTrans ab bc,?_,?_,extractTail dst,f⟩
  · change (c.label : Lifted.Label) = (Tail.layout x).start next at l
    split <;> rename_i hc
    · simp only [next,hc,ite_true] at l; exact l
    · simp only [next,hc,ite_false] at l; exact l
  · have read := (s.after f).stack.readable
    unpack_atoms dst []
    unpack_atoms kept []
    join_atoms [rem4]
    all_goals first | assumption | (apply read.sub <;> omega)

end ChaCha20Poly1305.Proofs.Decrypt.Stream.Control
