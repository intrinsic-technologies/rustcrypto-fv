import ChaCha20Poly1305.Proofs.Decrypt.AuthScope

namespace ChaCha20Poly1305.Proofs.Decrypt.Hash
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program
open Poly1305 Standards.RFC.ChaCha20Poly1305
set_option allowUnsafeReducibility true in
attribute [local reducible] ChaCha20Poly1305.Proofs.Decrypt.Lifted.lifted
set_option maxHeartbeats 700000
set_option maxRecDepth 6500
set_option pp.maxSteps 140

def keyPads (key : Vector UInt8 32) (p : BitVec 64) :=
  Detached.pads p ((keyBits key).extractLsb' 128 64) ((keyBits key).extractLsb' 192 64)

theorem makeQuads {key : Vector UInt8 32} {p rs m} {r ws : Vector (BitVec 32) 5}
    (hp : Atom.All fnCode rs m (keyPads key p))
    (hr : Atom.All fnCode rs m (rData p r)) (ha : Atom.All fnCode rs m (accData p ws)) :
    Atom.All fnCode rs m (quad7 p (quads r ⟨sWords key,ws⟩)) := by
  obtain ⟨lo,hi,_⟩ := hp
  obtain ⟨r0,r1,r2,r3,r4,_⟩ := hr
  obtain ⟨a0,a1,a2,a3,a4,_⟩ := ha
  refine ⟨?_,?_,pair32.mpr ⟨?_,r0⟩,pair32.mpr ⟨?_,r2⟩,pair32.mpr ⟨?_,r4⟩,
    pair32.mpr ⟨?_,a1⟩,pair32.mpr ⟨?_,a3⟩,trivial⟩
  · apply lo.trans
    exact (BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (len₁:=32) (len₂:=32) (x:=keyBits key) (start₂:=160) (start₁:=128) rfl).symm
  · apply hi.trans
    exact (BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (len₁:=32) (len₂:=32) (x:=keyBits key) (start₂:=224) (start₁:=192) rfl).symm
  all_goals rw [BitVec.add_assoc]; assumption

private theorem mulPre {fr src n m rs r w out a c} (g : PadScope fr src n m)
    (reg : Atom.All fnCode rs m (regs5 fr)) (la : memLoad m (fr.rsp+192) 64=a)
    (lc : memLoad m (fr.rsp+24) 64=c)
    (hr : Atom.All fnCode rs m (rData fr.rdi r)) (ha : Atom.All fnCode rs m (accData fr.rdi w)) :
    Atom.All fnCode rs m ((lengthsCall r w out a c fr.rsp fr.rdi).before (snapAt fr 96 m)) := by
  have lo := g.area.readable.low
  have sp := g.floor
  have code := g.code
  have ctx := g.ctxAt
  have align := g.align
  have below := g.below
  have area := g.area
  have cw := g.ctx
  have rd : Readable m (fr.rsp+32) 16 := area.readable.sub (by bv_omega) (by bv_omega)
  unpack_atoms reg [regs5]
  unpack_atoms hr []
  unpack_atoms ha []
  join_atoms []
  all_goals first | assumption | rfl | bv_omega

private theorem endPre {fr src n m rs q lo hi} (g : PadScope fr src n m)
    (reg : Atom.All fnCode rs m (regs5 fr)) (qv : Atom.All fnCode rs m (quad7 fr.rdi q)) :
    Atom.All fnCode rs m ((finishCall q lo hi fr.rsp).before (snapAt fr 56 m)) := by
  have low := g.area.readable.low
  have sp := g.floor
  have code := g.code
  have ctx := g.ctxAt
  have align := g.align
  have below : Writable fnCode m (fr.rsp-56) 56 := g.below.sub (by bv_omega) (by bv_omega)
  have area := g.area
  have cr := g.ctx.readable
  have rr : Readable m (fr.rsp+32) 56 := area.readable.sub (by bv_omega) (by bv_omega)
  have wr : Writable fnCode m (fr.rsp+160) 16 := area.sub (by bv_omega) (by bv_omega)
  unpack_atoms reg [regs5]
  unpack_atoms qv []
  join_atoms []
  all_goals first | assumption | rfl | bv_omega

def tagMem (p : BitVec 64) (t : BitVec 128) := Detached.pads (p+160) (t.extractLsb' 0 64) (t.extractLsb' 64 64)

theorem tagMemOf {x : Finish.Input} {t : BitVec 128} {p : BitVec 64} {m rs} (eq : tagValue x=t)
    (lo : memLoad m (p+160) 64=tagLo x) (hi : memLoad m (p+168) 64=tagHi x) :
    Atom.All fnCode rs m (tagMem p t) := by
  subst t
  change memLoad m (p+160) 64=(tagHi x ++ tagLo x).extractLsb' 0 64 ∧
    memLoad m (p+160+8) 64=(tagHi x ++ tagLo x).extractLsb' 64 64 ∧ True
  rw [BitVec.extractLsb'_append_eq_left,BitVec.extractLsb'_append_eq_right,BitVec.add_assoc]
  exact ⟨lo,hi,trivial⟩

theorem finishAuth (fr : Activation) (src : BitVec 64) (key : Vector UInt8 32) (aad ct : ByteArray)
    (la lc : BitVec 64) (a : lifted.Location) (ws : Vector (BitVec 32) 5)
    (hla : la.toNat=aad.size) (hlc : lc.toNat=ct.size)
    (rep : represents ws (foldFrom ct (rKey key) (foldFrom aad (rKey key) 0 (count aad)) (count ct)))
    (g : PadScope fr src ct.size a.store) (label : a.label=.l1004fc) (reg : Atom.All fnCode a.arguments a.store (regs5 fr))
    (av : memLoad a.store (fr.rsp+192) 64=la) (cv : memLoad a.store (fr.rsp+24) 64=lc)
    (pad : Atom.All fnCode a.arguments a.store (keyPads key fr.rdi))
    (hr : Atom.All fnCode a.arguments a.store (rData fr.rdi (rWords key)))
    (ha : Atom.All fnCode a.arguments a.store (accData fr.rdi ws)) :
    Forward a (fun d => d.label=.l100577 ∧ Atom.All fnCode d.arguments d.store (regs5 fr) ∧
      Atom.All fnCode d.arguments d.store (tagMem fr.rsp (tagBits (poly1305Mac (aeadMacData aad ct) key))) ∧
      RamWriteFrame a.store d.store (work fr.rsp)) := by
  let r := rWords key
  let out := Mul.output ⟨r,ws,lc++la⟩
  let f := snapAt fr 96 a.store
  let site := lengthsCall r ws out la lc fr.rsp fr.rdi
  have good : site.callee.Correct := Callee.reserveCorrect _ (lastMulCorrect r ws la lc) (fun _ _ => ⟨rfl,rfl,rfl,rfl⟩) _
  apply (Invoke.run site good (lengthsValid _ _ _ _ _ _ _) f a label (mulPre g reg av cv hr ha) rfl).bind
  rintro b ⟨bl,rout,fw⟩
  have low := g.area.readable.low
  have floor := g.floor
  have wf : RamWriteFrame a.store b.store (work fr.rsp) := by
    apply widen fw
    simp [RegionsWithin,f,site,snapAt,Activation.region,lengthsCall,slot,work,g.ctxAt]; bv_omega
  have reg' : Atom.All fnCode b.arguments b.store (regs5 fr) := ((Atom.all_append _ _).1 rout).1
  have acc : Atom.All fnCode b.arguments b.store (accData fr.rdi out) := ((Atom.all_append _ _).1 rout).2
  have pads' : Atom.All fnCode b.arguments b.store (keyPads key fr.rdi) := by
    apply ChaChaRound.keepFrame _ wf pad
    intro t ht
    simp only [keyPads,Detached.pads,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl|rfl <;> simp [ChaChaRound.pass,Outside,work,g.ctxAt] <;> bv_omega
  let x : Finish.Input := ⟨sWords key,out⟩
  let e := finishCall (quads r x) (tagLo x) (tagHi x) fr.rsp
  let f' := snapAt fr 56 b.store
  have gg := g.move (fr':=fr) wf (workZone floor) rfl rfl
  have goodE : e.callee.Correct := Callee.reserveCorrect _ (endCorrect r x) (fun _ _ => ⟨rfl,rfl,rfl,rfl⟩) _
  apply (Invoke.run e goodE (finishValid _ _ _ _) f' b bl (endPre gg reg' (makeQuads pads' (padKeepR g wf hr) acc)) rfl).bind
  rintro d ⟨dl,dr,df⟩
  have eq := nextRep (key:=key) rep (lc++la)
  rw [lengths,hla,hlc] at eq
  have tag : tagValue x = tagBits (poly1305Mac (aeadMacData aad ct) key) := tagEquals eq
  apply Forward.here
  obtain ⟨rr,bp,lo,hi,_⟩ := (Atom.all_append _ _).1 dr
  refine ⟨dl,(Atom.all_append _ _).2 ⟨rr,bp,trivial⟩,tagMemOf tag lo hi,wf.trans df ?_⟩
  simp [RegionsWithin,e,f',snapAt,Activation.region,finishCall,slot,work]; bv_omega

end ChaCha20Poly1305.Proofs.Decrypt.Hash
