import ChaCha20Poly1305.Proofs.Decrypt.WrapCall
import ChaCha20Poly1305.Proofs.Decrypt.DetachCorrect
import ChaCha20Poly1305.Proofs.Decrypt.Deliver

namespace ChaCha20Poly1305.Proofs.Decrypt.Wrapper
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program
open Hash Detached
set_option allowUnsafeReducibility true in
attribute [local reducible] ChaCha20Poly1305.Proofs.Decrypt.Lifted.lifted
set_option maxHeartbeats 800000
set_option maxRecDepth 8000
set_option linter.constructorNameAsVariable false
attribute [local irreducible] Packet.good Packet.src Packet.dst Packet.x memLoad memStore

def phaseWrites (sp buf : BitVec 64) (n : Nat) : List MemoryRegion :=
  [⟨sp.toNat-872,872⟩,⟨sp.toNat,8⟩,⟨sp.toNat+24,32⟩,⟨buf.toNat,n⟩]

private theorem splitKeep {p la f m m' rs rs'} (h : Atom.All fnCode rs m (oldData p la f))
    (step : RamWriteFrame m m' (splitTag f).writes) (floor : 872≤f.rsp.toNat) : Atom.All fnCode rs' m' (oldData p la f) := by
  have st := h; unpack_atoms st []
  apply ChaChaRound.keepFrame _ step h
  intro t ht
  simp only [oldData,inputs,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp [ChaChaRound.pass,Outside,splitTag,slot,enterD,push,afterD] <;> bv_omega

def nextWrapper (p : Packet) := if p.good then Lifted.Label.l1015d8 else .l101611

structure Opened (p : Packet) (f : Activation) (m : Ram) (d : lifted.Location) : Prop where
  label : d.label=nextWrapper p
  frame : RamWriteFrame m d.store (phaseWrites f.rsp p.buf p.n.toNat)
  regs : Atom.All fnCode d.arguments d.store (live (afterD f p.n))
  vec0 : memLoad d.store (f.rsp+8) 64=f.r14
  vec1 : memLoad d.store (f.rsp+16) 64=p.buf
  vec2 : memLoad d.store (f.rsp+24) 64=f.r14
  bytes : payload p d.store

theorem openTag (p : Packet) (f : Activation) (la : BitVec 64) (a : lifted.Location)
    (data : Atom.All fnCode a.arguments a.store (oldData p la f)) (reg : Atom.All fnCode a.arguments a.store (live f))
    (area : Writable fnCode a.store (f.rsp-872) 960) (floor : 872≤f.rsp.toNat) (align : f.rsp.toNat%16=0)
    (size : 16≤f.r14.toNat) (n : f.r14-16=p.n) (buf : f.rbp=p.buf) (entry : a.label=.l10158b)
    (vec0 : memLoad a.store (f.rsp+8) 64=f.r14) (vec1 : memLoad a.store (f.rsp+16) 64=p.buf) :
    Forward a (Opened p f a.store) := by
  have facts := data; unpack_atoms facts []
  have low := area.readable.low
  have code : f.rsp.toNat+88≤0x1001f0 ∨ 0x102e00+872≤f.rsp.toNat := by assumption
  have st : Writable fnCode a.store f.rsp 32 := area.sub (by bv_omega) (by bv_omega)
  have cd : f.rsp.toNat+32≤0x10158b ∨ 0x101596≤f.rsp.toNat := by omega
  obtain ⟨b,j,bl,br,bf⟩ := Micro.run (splitValid f) entry ((Atom.all_append _ _).2 ⟨reg,st,size,cd,trivial⟩)
  apply fromJump j
  obtain ⟨rb,count,_⟩ := (Atom.all_append _ _).1 br
  let e := detachedCall p la f.rsp
  let sf := snapAt f 872 b.store
  have space0 : Atom.All fnCode b.arguments b.store (space sf 872) := by
    refine ⟨(area.of_frame bf).sub (Nat.le_refl _) (by change (f.rsp-872).toNat+872≤(f.rsp-872).toNat+960; omega),?_,align,?_ ,trivial⟩
    · change (f.rsp-872).toNat+872≤f.rsp.toNat; bv_omega
    · change f.rsp.toNat≤0x1001f0 ∨ 0x102e00+872≤f.rsp.toNat; omega
  have before : Atom.All fnCode b.arguments b.store (e.before sf) :=
    (Atom.all_append _ _).2 ⟨(Atom.all_append _ _).2 ⟨(Atom.all_append _ _).2 ⟨rb,space0⟩,rfl,buf,n,trivial⟩,
      splitKeep data bf floor⟩
  have ok : e.callee.Correct := Callee.reserveCorrect _ (detachedCorrect p) (fun _ _ => ⟨rfl,rfl,rfl,rfl⟩) _
  apply (Invoke.run e ok (detachedValid _ _ _) sf b bl before rfl).bind
  rintro c ⟨cl,cr,cf⟩
  obtain ⟨rl,output⟩ := (Atom.all_append _ _).1 cr
  obtain ⟨al,rest⟩ := (Atom.all_append _ _).1 output
  let ef := afterD f p.n
  obtain ⟨d,j,dl,dr,df⟩ := Micro.run (branchValid ef p.good) cl ((Atom.all_append _ _).2 ⟨rl,al⟩)
  apply fromJump j
  have eq := noWrites df
  have wf : RamWriteFrame a.store c.store (phaseWrites f.rsp p.buf p.n.toNat) := by
    apply (widen bf _).trans cf
    · cases hg : p.good <;> simp [RegionsWithin,e,detachedCall,extraD,slot,sf,snapAt,Activation.region,phaseWrites,hg] <;> bv_omega
    · simp [RegionsWithin,splitTag,slot,phaseWrites]; bv_omega
  have loc (i : Nat) (hi : i=8 ∨ i=16 ∨ i=24) :
      memLoad c.store (f.rsp+BitVec.ofNat 64 i) 64=memLoad b.store (f.rsp+BitVec.ofNat 64 i) 64 := by
    apply cf.memLoad_eq
    rcases hi with rfl|rfl|rfl <;> cases hg : p.good <;>
      simp [Outside,e,detachedCall,extraD,slot,sf,snapAt,Activation.region,hg] <;> bv_omega
  have old (i : Nat) (hi : i=8 ∨ i=16) :
      memLoad b.store (f.rsp+BitVec.ofNat 64 i) 64=memLoad a.store (f.rsp+BitVec.ofNat 64 i) 64 := by
    apply bf.memLoad_eq
    rcases hi with rfl|rfl <;> simp [Outside,splitTag,slot] <;> bv_omega
  apply Forward.here
  refine ⟨dl,eq ▸ wf,dr,eq ▸ (loc 8 (by decide)).trans ((old 8 (by decide)).trans vec0),
    eq ▸ (loc 16 (by decide)).trans ((old 16 (by decide)).trans vec1),eq ▸ (loc 24 (by decide)).trans count,?_⟩
  intro good
  change Atom.All _ _ _ (if p.good then _ else []) at rest
  rw [ite_eq_left good] at rest
  exact eq ▸ rest.1

end ChaCha20Poly1305.Proofs.Decrypt.Wrapper
