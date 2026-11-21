import ChaCha20Poly1305.Proofs.Decrypt.DetachBase
import ChaCha20Poly1305.Proofs.Decrypt.Feed

namespace ChaCha20Poly1305.Proofs.Decrypt.Detached
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program
open Hash Poly1305 Standards.RFC.ChaCha20Poly1305
set_option allowUnsafeReducibility true in
attribute [local reducible] ChaCha20Poly1305.Proofs.Decrypt.Lifted.lifted
set_option maxHeartbeats 800000
set_option maxRecDepth 8000
set_option pp.maxSteps 150

def padAtoms (p : Packet) (ctx : BitVec 64) := pads ctx ((keyBits p.one).extractLsb' 128 64) ((keyBits p.one).extractLsb' 192 64)
def contextAtoms (p : Packet) (ctx : BitVec 64) := padAtoms p ctx ++ rData ctx (rWords p.one) ++ accData ctx zeroAcc
def streamHeader (p : Packet) (sp : BitVec 64) := header p.x 1 (sp+208) ++ [.mem (sp+272) 8 64]

structure Prepared (p : Packet) (fr : Activation) (m : Ram) (a : lifted.Location) : Prop where
  label : a.label=.l1003e3
  frame : RamWriteFrame m a.store (innerZone fr)
  regs : Atom.All fnCode a.arguments a.store (regs5 (newCtx (physical fr)))
  header : Atom.All fnCode a.arguments a.store (streamHeader p (physical fr).rsp)
  len : memLoad a.store ((physical fr).rsp+24) 64=p.n
  ctx : Atom.All fnCode a.arguments a.store (contextAtoms p (newCtx (physical fr)).rdi)

private theorem keyPre (p : Packet) (fr : Activation) (m rs)
    (reg : Atom.All fnCode rs m (live (physical fr))) (w : Atom.All fnCode rs m (beginWords p.x (physical fr).rsp))
    (stack : Writable fnCode m (fr.rsp-864) 864) (floor : 864≤fr.rsp.toNat) (align : fr.rsp.toNat%16=8)
    (code : fr.rsp.toNat≤0x1001f0 ∨ 0x102e00+864≤fr.rsp.toNat) :
    let f := physical fr
    Atom.All fnCode rs m ((keyCall (Stream.words p.key p.nonce 0) p.x (keyBits p.one) f.rsp).before (snapAt f 424 m)) := by
  have slo := stack.readable.low
  have st : Writable fnCode m ((physical fr).rsp-424) 424 := stack.sub (by dsimp [physical]; bv_omega) (by dsimp [physical]; bv_omega)
  have area : Writable fnCode m (physical fr).rsp 392 := stack.sub (by dsimp [physical]; bv_omega) (by dsimp [physical]; bv_omega)
  have dst : Writable fnCode m ((physical fr).rsp+32) 128 := stack.sub (by dsimp [physical]; bv_omega) (by dsimp [physical]; bv_omega)
  have vec : Readable m ((physical fr).rsp+208) 24 := stack.readable.sub (by dsimp [physical]; bv_omega) (by dsimp [physical]; bv_omega)
  have bwr : Writable fnCode m ((physical fr).rsp+160) 32 := stack.sub (by dsimp [physical]; bv_omega) (by dsimp [physical]; bv_omega)
  unpack_atoms reg []
  unpack_atoms w []
  join_atoms [physical]
  all_goals first | assumption | rfl | bv_omega

private theorem initPre (p : Packet) (fr : Activation) (m rs)
    (reg : Atom.All fnCode rs m (live (physical fr))) (otk : memLoad m ((physical fr).rsp+160) 256=keyBits p.one)
    (stack : Writable fnCode m (fr.rsp-864) 864) (floor : 864≤fr.rsp.toNat) (align : fr.rsp.toNat%16=8)
    (code : fr.rsp.toNat≤0x1001f0 ∨ 0x102e00+864≤fr.rsp.toNat) :
    let f := physical fr
    Atom.All fnCode rs m ((initCall (keyBits p.one) (rWords p.one) zeroAcc ((keyBits p.one).extractLsb' 128 64)
      ((keyBits p.one).extractLsb' 192 64) f.rsp).before (snapAt f 8 m)) := by
  have slo := stack.readable.low
  have st : Writable fnCode m ((physical fr).rsp-8) 8 := stack.sub (by dsimp [physical]; bv_omega) (by dsimp [physical]; bv_omega)
  have dest : Writable fnCode m ((physical fr).rsp+336) 56 := stack.sub (by dsimp [physical]; bv_omega) (by dsimp [physical]; bv_omega)
  have src : Readable m ((physical fr).rsp+160) 32 := stack.readable.sub (by dsimp [physical]; bv_omega) (by dsimp [physical]; bv_omega)
  let f := physical fr
  let g := snapAt f 8 m
  have ar : Atom.All fnCode rs m (space g 8) :=
    ⟨st,by change (fr.rsp-440-8).toNat+8≤(fr.rsp-440).toNat; bv_omega,
     by change (fr.rsp-440).toNat%16=0; bv_omega,
     by change (fr.rsp-440).toNat≤_ ∨ _≤(fr.rsp-440).toNat; bv_omega,trivial⟩
  have geo : Atom.All fnCode rs m (initGeo {push g with rdi:=f.rsp+336,rsi:=f.rsp+160}) := by
    refine ⟨src,dest,?_,?_,?_,trivial⟩
    all_goals dsimp [g,f,snapAt,push,physical,Atom.Holds]; bv_omega
  exact (Atom.all_append _ _).2 ⟨(Atom.all_append _ _).2
    ⟨(Atom.all_append _ _).2 ⟨reg,ar⟩,rfl,otk,trivial⟩,geo⟩

theorem prep (p : Packet) (fr : Activation) (a : lifted.Location)
    (label : a.label=.l1002e5) (reg : Atom.All fnCode a.arguments a.store (live (physical fr)))
    (words : Atom.All fnCode a.arguments a.store (beginWords p.x (physical fr).rsp))
    (stack : Writable fnCode a.store (fr.rsp-864) 864) (floor : 864≤fr.rsp.toNat) (align : fr.rsp.toNat%16=8)
    (code : fr.rsp.toNat≤0x1001f0 ∨ 0x102e00+864≤fr.rsp.toNat)
    (ext : Atom.All fnCode a.arguments a.store (extraIn p fr)) :
    Forward a (Prepared p fr a.store) := by
  let f := physical fr
  let z := keyBits p.one
  let w := Stream.words p.key p.nonce 0
  let e := keyCall w p.x z f.rsp
  have correct : e.callee.Correct := Callee.reserveCorrect _ (keyFnCorrect p.key p.nonce (f.rsp+160))
    (fun _ _ => ⟨rfl,rfl,rfl,rfl⟩) _
  apply (Invoke.run e correct (keyCallValid _ _ _ _) (snapAt f 424 a.store) a label (keyPre p fr _ _ reg words stack floor align code) rfl).bind
  rintro b ⟨bl,br,bf⟩
  have bframe : RamWriteFrame a.store b.store (innerZone fr) := by
    apply widen bf
    simp [RegionsWithin,e,keyCall,keyAreas,keyStack,slot,snapAt,Activation.region,f,physical,innerZone]; bv_omega
  obtain ⟨head,header0⟩ := (Atom.all_append _ _).1 br
  obtain ⟨bregs,al,otk,_⟩ := (Atom.all_append _ _).1 head
  obtain ⟨c,j,cl,cr,cf⟩ := Micro.run (keyTestValid f) bl ((Atom.all_append _ _).2 ⟨bregs,al,trivial⟩)
  apply fromJump j
  have eq := noWrites cf
  let k := initCall z (rWords p.one) zeroAcc (z.extractLsb' 128 64) (z.extractLsb' 192 64) f.rsp
  have st := stack.of_frame bframe
  apply (Invoke.run k (initWideCorrect p.one) (initValid _ _ _ _ _ _) (snapAt f 8 c.store) c cl
    (initPre p fr _ _ cr (eq ▸ otk) (eq ▸ st) floor align code) rfl).bind
  rintro d ⟨dl,dr,df⟩
  have dw : RamWriteFrame a.store d.store (innerZone fr) := by
    apply (show RamWriteFrame a.store c.store (innerZone fr) from eq ▸ bframe).trans df
    simp [RegionsWithin,innerZone,k,initCall,slot,snapAt,Activation.region,f,physical]; bv_omega
  have rtag := ext
  unpack_atoms rtag []
  have low : fr.rsp.toNat+16≤2^32 := by bv_omega
  have x := keepExt (rs':=d.arguments) ext dw (innerOuter fr floor) floor low
  have stable : Atom.All fnCode d.arguments d.store (fixed p.x (f.rsp+32)) := by
    apply ChaChaRound.keepFrame _ df (eq ▸ header0)
    intro t ht
    simp only [fixed,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp [ChaChaRound.pass,Outside,k,initCall,snapAt,Activation.region,slot,f,physical] <;> bv_omega
  have area : Writable fnCode d.store f.rsp 392 := (stack.of_frame dw).sub (by dsimp [f,physical]; bv_omega) (by dsimp [f,physical]; bv_omega)
  obtain ⟨reg5,dat⟩ := (Atom.all_append _ _).1 dr
  have ins : Atom.All fnCode d.arguments d.store ((install p.x (newCtx f) p.n).pre) := by
    unpack_atoms reg5 [f]
    unpack_atoms x []
    unpack_atoms stable [f]
    join_atoms [f]
    all_goals first | assumption | rfl | bv_omega
  obtain ⟨b',j,lb,atoms,wf⟩ := Micro.run (installValid p.x (newCtx f) p.n p.small) dl ins
  apply fromJump j
  apply Forward.here
  obtain ⟨pre,used⟩ := (Atom.all_append _ _).1 atoms
  obtain ⟨first,header⟩ := (Atom.all_append _ _).1 pre
  obtain ⟨regs0,bp,ln,_⟩ := (Atom.all_append _ _).1 first
  refine ⟨lb,dw.trans wf ?_,(Atom.all_append _ _).2 ⟨regs0,bp,trivial⟩,(Atom.all_append _ _).2 ⟨header,used⟩,ln,?_⟩
  · simp [RegionsWithin,install,installWrites,updates,slot,innerZone,newCtx,f,physical]; bv_omega
  · have old : Atom.All fnCode d.arguments d.store (contextAtoms p (newCtx f).rdi) := dat
    apply ChaChaRound.keepFrame _ wf old
    intro t ht
    simp only [contextAtoms,padAtoms,pads,rData,accData,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp [ChaChaRound.pass,Outside,install,installWrites,updates,slot,newCtx,f,physical] <;> bv_omega

end ChaCha20Poly1305.Proofs.Decrypt.Detached
