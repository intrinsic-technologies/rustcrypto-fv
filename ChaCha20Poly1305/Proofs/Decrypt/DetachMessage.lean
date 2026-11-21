import ChaCha20Poly1305.Proofs.Decrypt.DetachAuth
import ChaCha20Poly1305.Proofs.Decrypt.DetachReturn

namespace ChaCha20Poly1305.Proofs.Decrypt.Detached
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program
open Hash Poly1305 Standards.RFC.ChaCha20Poly1305
set_option allowUnsafeReducibility true in
attribute [local reducible] ChaCha20Poly1305.Proofs.Decrypt.Lifted.lifted
set_option maxHeartbeats 700000
set_option maxRecDepth 8000
set_option pp.maxSteps 160

def dirty (p : Packet) (fr : Activation) := innerZone fr ++ (detachedFn p).writes fr
def payload (p : Packet) (m : Ram) := p.good=true → memLoad m p.buf (8*p.n.toNat)=p.dst

structure Returning (p : Packet) (fr : Activation) (m : Ram) (a : lifted.Location) : Prop where
  label : a.label=.l1005ea
  frame : RamWriteFrame m a.store (dirty p fr)
  regs : Atom.All fnCode a.arguments a.store (basic (physical fr) ++ [.low 0 8 (if p.good then 0 else 1)])
  data : payload p a.store

private theorem msgStart (p : Packet) (fr e : Activation) (a : lifted.Location)
    (reg : Atom.All fnCode a.arguments a.store (regs5 e)) (sp : e.rsp=fr.rsp-440)
    (ext : Atom.All fnCode a.arguments a.store (extraIn p fr))
    (hd : Atom.All fnCode a.arguments a.store (streamHeader p e.rsp))
    (v : memLoad a.store (e.rsp+16) 64=fr.r8)
    (stack : Writable fnCode a.store (fr.rsp-864) 864) (floor : 864≤fr.rsp.toNat) (align : fr.rsp.toNat%16=8) :
    Atom.All fnCode a.arguments a.store ((msgCall p.stream p.x p.src p.dst e.rsp fr.r8).before (snapAt e 424 a.store)) := by
  have low := stack.readable.low
  have copied := ext
  unpack_atoms copied []
  have rd : Readable a.store (e.rsp+16) 8 := stack.readable.sub (by rw [sp]; bv_omega) (by rw [sp]; bv_omega)
  have st : Writable fnCode a.store (e.rsp-424) 424 := stack.sub (by rw [sp]; bv_omega) (by rw [sp]; bv_omega)
  have ar : Atom.All fnCode a.arguments a.store (space (snapAt e 424 a.store) 424) := by
    refine ⟨st,?_,?_,?_,trivial⟩
    all_goals dsimp [Atom.Holds,snapAt]; rw [sp]; bv_omega
  have wr : Writable fnCode a.store (e.rsp+208) 128 := stack.sub (by rw [sp]; bv_omega) (by rw [sp]; bv_omega)
  have geo : Atom.All fnCode a.arguments a.store (Stream.geometry p.stream (msgFrame (snapAt e 424 a.store) fr.r8)) := by
    simp only [Stream.geometry,Packet.stream,msgFrame,snapAt,push,Atom.All,Atom.Holds]
    refine ⟨wr,by assumption,by assumption,?_,?_,?_,?_,?_,?_,?_,by assumption,by assumption,trivial⟩
    all_goals rw [sp]; bv_omega
  have vv : Atom.All fnCode a.arguments a.store (vec fr.r8 p.buf p.n) := ((Atom.all_append _ _).1 ext).2
  obtain ⟨h,u⟩ := (Atom.all_append _ _).1 hd
  have used : memLoad a.store ((e.rsp+208)+64) 8=64 := by rw [BitVec.add_assoc]; exact u.1
  have obj : Atom.All fnCode a.arguments a.store ([Atom.mem ((e.rsp+208)+64) 8 64] ++ vec fr.r8 p.buf p.n) := (Atom.all_append _ _).2 ⟨⟨used,trivial⟩,vv⟩
  exact (Atom.all_append _ _).2 ⟨(Atom.all_append _ _).2 ⟨(Atom.all_append _ _).2 ⟨reg,ar⟩,rfl,rd,v,trivial⟩,
    (Atom.all_append _ _).2 ⟨geo,(Atom.all_append _ _).2 ⟨(Atom.all_append _ _).2 ⟨h,obj⟩,by assumption,trivial⟩⟩⟩

attribute [local irreducible] Packet.good chacha20Encrypt poly1305Mac poly1305KeyGen memLoad memStore
set_option linter.constructorNameAsVariable false

theorem message (p : Packet) (fr : Activation) (m : Ram) (a : lifted.Location)
    (q : Checked p fr m a) (ext : Atom.All fnCode a.arguments a.store (extraIn p fr))
    (stack : Writable fnCode a.store (fr.rsp-864) 864) (floor : 864≤fr.rsp.toNat) (align : fr.rsp.toNat%16=8) :
    Forward a (Returning p fr m) := by
  have out := q.regs
  have low := stack.readable.low
  cases hg : p.good
  · apply Forward.here
    refine ⟨by simpa [checkedAt,hg] using q.label,by simpa [dirty,detachedFn,hg] using q.frame,
      by simpa [checkedRegs,hg] using out,fun h => Bool.noConfusion (hg.symm.trans h)⟩
  · simp only [checkedRegs,hg,ite_true] at out
    obtain ⟨f,sh,reg⟩ := out
    let e := msgCall p.stream p.x p.src p.dst f.rsp fr.r8
    have sp : f.rsp=fr.rsp-440 := sh.sp
    have ok : e.callee.Correct := viewCorrect (key:=p.key) (nonce:=p.nonce) (ctr:=1) rfl _
      (fun _ _ h => h.1) (Stream.messageCorrect p.stream p.key p.nonce p.ct rfl p.length.symm)
    have start := msgStart p fr f a reg sp ext (sh.sp ▸ q.header) (sh.sp ▸ q.vec) stack floor align
    apply (Invoke.run e ok (msgValid _ _ _ _ _ _) (snapAt f 424 a.store) a (by simpa [checkedAt,hg,e,msgCall] using q.label) start rfl).bind
    rintro b ⟨bl,br,bf⟩
    obtain ⟨base,al,val,_⟩ := (Atom.all_append _ _).1 br
    obtain ⟨c,j,cl,cr,cf⟩ := Micro.run (testMsgValid f) bl ((Atom.all_append _ _).2 ⟨base,al,trivial⟩)
    apply fromJump j
    obtain ⟨d,k,dl,dr,df⟩ := Micro.run (zeroMsgValid f) cl cr
    apply fromJump k
    have eq := (noWrites df).trans (noWrites cf)
    apply Forward.here
    refine ⟨dl,?_,?_,fun _ => eq ▸ val⟩
    · rw [eq]
      apply (widen q.frame (fun z hz => ⟨z,List.mem_append_left _ hz,Nat.le_refl _,Nat.le_refl _⟩)).trans bf
      simp [RegionsWithin,innerZone,detachedFn,hg,e,msgCall,snapAt,Activation.region,sp,Packet.stream]; bv_omega
    · change Atom.All _ _ _ (basic f ++ [.low 0 8 0]) at dr
      simpa only [hg,ite_true,basic,sh.sp,sh.mx,sh.ft,sh.fc,newCtx] using dr

end ChaCha20Poly1305.Proofs.Decrypt.Detached
