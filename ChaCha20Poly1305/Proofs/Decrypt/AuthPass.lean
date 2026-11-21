import ChaCha20Poly1305.Proofs.Decrypt.AuthFinish

namespace ChaCha20Poly1305.Proofs.Decrypt.Hash
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program
open Poly1305 Standards.RFC.ChaCha20Poly1305
set_option allowUnsafeReducibility true in
attribute [local reducible] ChaCha20Poly1305.Proofs.Decrypt.Lifted.lifted
set_option maxHeartbeats 650000
set_option maxRecDepth 6500
set_option pp.maxSteps 145

structure Shape (fr fr' : Activation) : Prop where
  sp : fr'.rsp=fr.rsp
  ctx : fr'.rdi=fr.rdi
  mx : fr'.mxcsr=fr.mxcsr
  ft : fr'.ftw=fr.ftw
  fc : fr'.fcw=fr.fcw

theorem Shape.trans {f g h} (a : Shape f g) (b : Shape g h) : Shape f h :=
  ⟨b.sp.trans a.sp,b.ctx.trans a.ctx,b.mx.trans a.mx,b.ft.trans a.ft,b.fc.trans a.fc⟩

theorem eShape (ct : Bool) (fr : Activation) (src : BitVec 64) (s : ByteArray) (tag : BitVec 64) :
    Shape fr (endFr ct fr src s tag) :=
  let ⟨a,b,_,c,d,e⟩ := endShape ct fr src s tag
  ⟨a,b,c,d,e⟩

theorem workLocal {sp : BitVec 64} {m m'} (f : RamWriteFrame m m' (work sp)) (i w : Nat)
    (low : sp.toNat+456≤2^64) (floor : 96≤sp.toNat) (end_ : i+w/8≤456)
    (e1 : i+w/8≤32 ∨ 88≤i) (e2 : i+w/8≤160 ∨ 176≤i) (e3 : i+w/8≤372 ∨ 392≤i) :
    memLoad m' (sp+BitVec.ofNat 64 i) w = memLoad m (sp+BitVec.ofNat 64 i) w := by
  apply f.memLoad_eq
  simp [Outside,work]; bv_omega

theorem workPads {fr src n m m' key rs rs'} (g : PadScope fr src n m) (f : RamWriteFrame m m' (work fr.rsp))
    (hp : Atom.All fnCode rs m (keyPads key fr.rdi)) : Atom.All fnCode rs' m' (keyPads key fr.rdi) := by
  have lo := g.area.readable.low
  have floor := g.floor
  apply ChaChaRound.keepFrame _ f hp
  intro t ht
  simp only [keyPads,Detached.pads,List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl|rfl <;> simp [ChaChaRound.pass,Outside,work,g.ctxAt] <;> bv_omega

def vTag (key : Vector UInt8 32) (aad ct : ByteArray) := tagBits (poly1305Mac (aeadMacData aad ct) key)

structure Verified (fr : Activation) (a : Ram) (key : Vector UInt8 32) (aad ct : ByteArray) (tag : BitVec 64)
    (d : lifted.Location) : Prop where
  label : d.label=.l100577
  frame : RamWriteFrame a d.store (work fr.rsp)
  mem : Atom.All fnCode d.arguments d.store (tagMem fr.rsp (vTag key aad ct))
  regs : ∃ f, Shape fr f ∧ Atom.All fnCode d.arguments d.store (Hash.regs f ++ [.gpr 5 tag])

theorem ctPass (fr : Activation) (src vec la lc tag : BitVec 64) (key : Vector UInt8 32)
    (aad ct : ByteArray) (a : lifted.Location) (ws : Vector (BitVec 32) 5)
    (hla : la.toNat=aad.size) (hlc : lc.toNat=ct.size) (nc : lc.toNat<2^32)
    (rep : represents ws (foldFrom aad (rKey key) 0 (count aad))) (g : PadScope fr src ct.size a.store)
    (vl : Readable a.store vec 8) (vp : memLoad a.store vec 64=src) (limit : fr.r15=274877906879)
    (atV : memLoad a.store (fr.rsp+16) 64=vec) (atA : memLoad a.store (fr.rsp+192) 64=la)
    (atC : memLoad a.store (fr.rsp+24) 64=lc) (atT : memLoad a.store (fr.rsp+448) 64=tag)
    (tagR : Readable a.store (fr.rsp+448) 8) (raw : memLoad a.store src (8*ct.size)=Bytes.packed ct)
    (label : a.label=.l100479) (reg : Atom.All fnCode a.arguments a.store (regs fr))
    (hp : Atom.All fnCode a.arguments a.store (keyPads key fr.rdi))
    (hr : Atom.All fnCode a.arguments a.store (rData fr.rdi (rWords key)))
    (ha : Atom.All fnCode a.arguments a.store (accData fr.rdi ws)) : Forward a (Verified fr a.store key aad ct tag) := by
  let full := decide (16≤ct.size)
  let f := ctRegs fr lc src
  have ready : Atom.All fnCode a.arguments a.store ((setupC fr lc src vec full).pre) :=
    (Atom.all_append _ _).2 ⟨reg,g.area.readable.sub (Nat.le_refl _) (by omega),atV,vl,vp,atC,limit,trivial⟩
  obtain ⟨b,j,bl,regs',bf⟩ := Micro.run (setupCValid fr lc src vec full (by simp [full,hlc])) label ready
  apply fromJump j
  have eq := noWrites bf
  have g' : PadScope f src ct.size b.store := g.move bf (by simp [setupC,RegionsWithin]) rfl rfl
  have start : Source true f src ct b.store := ⟨(masks hlc nc).2,maskLowEq hlc nc,fun _ => rfl⟩
  apply (absorb true f src ct key _ ws rep b tag g' start (fun _ => eq ▸ ⟨tagR,atT⟩)
    bl regs' (eq ▸ hr) (eq ▸ ha) (eq ▸ raw)).bind
  intro c h
  let e := endFr true f src ct tag
  let dfr := {e with rbp:=tag}
  have q := eShape true f src ct tag
  have sh : Shape fr dfr := ⟨q.sp,q.ctx,q.mx,q.ft,q.fc⟩
  have wf : RamWriteFrame a.store c.store (work fr.rsp) := eq ▸ widen h.frame (padWork g')
  have gg : PadScope dfr src ct.size c.store := g.move wf (workZone g.floor) sh.sp sh.ctx
  obtain ⟨new,rep',acc⟩ := h.acc
  have reg' : Atom.All fnCode c.arguments c.store (regs5 dfr) := h.regs
  have lk := workLocal wf
  have low := g.area.readable.low
  have av : memLoad c.store (dfr.rsp+192) 64=la := sh.sp ▸ (lk 192 64 (by omega) g.floor (by decide) (by decide) (by decide) (by decide)).trans atA
  have cv : memLoad c.store (dfr.rsp+24) 64=lc := sh.sp ▸ (lk 24 64 (by omega) g.floor (by decide) (by decide) (by decide) (by decide)).trans atC
  apply (finishAuth dfr src key aad ct la lc c new hla hlc rep' gg h.label reg' av cv
    (sh.ctx ▸ workPads g wf hp) (sh.ctx ▸ padKeepR g wf hr) (sh.ctx ▸ acc)).bind
  rintro d ⟨dl,drs,tagV,df⟩
  apply Forward.here
  rw [sh.sp] at df tagV
  exact ⟨dl,wf.trans df (fun z hz => ⟨z,hz,Nat.le_refl _,Nat.le_refl _⟩),tagV,dfr,sh,drs⟩

end ChaCha20Poly1305.Proofs.Decrypt.Hash
