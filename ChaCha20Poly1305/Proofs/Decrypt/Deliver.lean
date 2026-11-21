import ChaCha20Poly1305.Proofs.Decrypt.WrapFlow
import ChaCha20Poly1305.Proofs.Decrypt.Feed

namespace ChaCha20Poly1305.Proofs.Decrypt.Wrapper
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program
open Hash Detached
set_option allowUnsafeReducibility true in
attribute [local reducible] ChaCha20Poly1305.Proofs.Decrypt.Lifted.lifted
set_option maxHeartbeats 700000
set_option maxRecDepth 6500

structure Delivery (sp dest src n cap : BitVec 64) (m : Ram) : Prop where
  rd : Readable m (sp+168) 8
  capacity : memLoad m (sp+168) 64=cap
  fits : n.toNat≤cap.toNat
  write : 0<n.toNat → Writable fnCode m dest n.toNat
  code : 0<n.toNat → dest.toNat+n.toNat≤0x100000 ∨ 0x102def≤dest.toNat
  stack : 0<n.toNat → dest.toNat+n.toNat≤sp.toNat-872 ∨ sp.toNat+144≤dest.toNat
  heap : 0<n.toNat → src.toNat+n.toNat≤dest.toNat ∨ dest.toNat+n.toNat≤src.toNat
  slot : src.toNat+n.toNat≤sp.toNat+168 ∨ sp.toNat+176≤src.toNat

theorem Delivery.after {sp dest src n cap m m' r} (h : Delivery sp dest src n cap m) (f : RamWriteFrame m m' r)
    (e : memLoad m' (sp+168) 64=memLoad m (sp+168) 64) : Delivery sp dest src n cap m' :=
  {h with rd:=h.rd.of_frame f,capacity:=e.trans h.capacity,write:=fun pos => (h.write pos).of_frame f}

def deliveryWrites (sp dest : BitVec 64) (n : Nat) : List MemoryRegion :=
  [⟨sp.toNat-8,8⟩,⟨sp.toNat+24,8⟩,⟨dest.toNat,n⟩]

theorem deliver (fr : Activation) (total cap : BitVec 64) (a : lifted.Location) (data : BitVec (8*fr.r13.toNat))
    (sz : fr.r13.toNat≤total.toNat) (low : total.toNat<2^32) (floor : 872≤fr.rsp.toNat)
    (align : fr.rsp.toNat%16=0) (area : Writable fnCode a.store (fr.rsp-872) 960)
    (code : fr.rsp.toNat+88≤0x1001f0 ∨ 0x102e00+872≤fr.rsp.toNat)
    (src : Readable a.store fr.rbp fr.r13.toNat)
    (apart : fr.rbp.toNat+fr.r13.toNat≤fr.rsp.toNat-872 ∨ fr.rsp.toNat+88≤fr.rbp.toNat)
    (got : Readable a.store 0x2013a8 8) (gotV : memLoad a.store 0x2013a8 64=0x102dc0)
    (gs : fr.rsp.toNat+88≤0x2013a8 ∨ 0x2013e8+872≤fr.rsp.toNat)
    (delivery : Delivery fr.rsp fr.rbx fr.rbp fr.r13 cap a.store)
    (c8 : memLoad a.store (fr.rsp+8) 64=total) (ptr : memLoad a.store (fr.rsp+16) 64=fr.rbp)
    (c24 : memLoad a.store (fr.rsp+24) 64=total) (plain : memLoad a.store fr.rbp (8*fr.r13.toNat)=data)
    (label : a.label=.l1015d8) (reg : Atom.All fnCode a.arguments a.store (live fr)) :
    Forward a (fun d => d.label=.l10160d ∧ Atom.All fnCode d.arguments d.store (basic fr) ∧
      memLoad d.store fr.rbx (8*fr.r13.toNat)=data ∧ RamWriteFrame a.store d.store (deliveryWrites fr.rsp fr.rbx fr.r13.toNat)) := by
  have geo := area.readable.low
  have stack : Writable fnCode a.store (fr.rsp-8) 8 := area.sub (by bv_omega) (by bv_omega)
  have here : Writable fnCode a.store fr.rsp 32 := area.sub (by bv_omega) (by bv_omega)
  have s8 (m : Ram) (w : Writable fnCode m (fr.rsp-8) 8) (rs) : Atom.All fnCode rs m (space (snapAt fr 8 m) 8) := by
    refine ⟨w,?_,align,?_,trivial⟩
    all_goals dsimp [Atom.Holds,snapAt]; bv_omega
  let site := cut total fr.rsp
  have cd : fr.rsp.toNat+32≤0x102020 ∨ 0x10202b≤fr.rsp.toNat := by omega
  have pre : Atom.All fnCode a.arguments a.store (site.before (snapAt fr 8 a.store)) :=
    (Atom.all_append _ _).2 ⟨(Atom.all_append _ _).2 ⟨reg,s8 _ stack _⟩,rfl,here,c24,sz,cd,trivial⟩
  apply (Invoke.run site (trimCorrect total) (cutValid _ _) (snapAt fr 8 a.store) a label pre rfl).bind
  rintro b ⟨bl,br,bf⟩
  obtain ⟨regB,count,_⟩ := (Atom.all_append _ _).1 br
  let rs : List MemoryRegion := [⟨fr.rsp.toNat-8,8⟩,⟨fr.rsp.toNat+24,8⟩]
  have fw : RamWriteFrame a.store b.store rs := by
    apply widen bf
    simp [RegionsWithin,rs,site,cut,snapAt,Activation.region,slot]; bv_omega
  have loc (i : Nat) (h : i=8 ∨ i=16 ∨ i=168) : memLoad b.store (fr.rsp+BitVec.ofNat 64 i) 64=memLoad a.store (fr.rsp+BitVec.ofNat 64 i) 64 := by
    apply fw.memLoad_eq
    rcases h with rfl|rfl|rfl <;> simp [Outside,rs] <;> bv_omega
  have dg := delivery.after fw (loc 168 (by decide))
  have area' := here.of_frame fw
  have r8 : Readable b.store (fr.rsp+8) 8 := area'.readable.sub (by bv_omega) (by bv_omega)
  have r16 : Readable b.store (fr.rsp+16) 8 := area'.readable.sub (by bv_omega) (by bv_omega)
  have r24 : Readable b.store (fr.rsp+24) 8 := area'.readable.sub (by bv_omega) (by bv_omega)
  obtain ⟨c,j,cl,cr,cf⟩ := Micro.run (checkCapValid fr total) bl
    ((Atom.all_append _ _).2 ⟨regB,r8,(loc 8 (by decide)).trans c8,low,trivial⟩)
  apply fromJump j
  have eq := noWrites cf
  obtain ⟨d,j,dl,dr,df⟩ := Micro.run (checkLenValid fr fr.r13 cap) cl
    ((Atom.all_append _ _).2 ⟨cr,eq ▸ dg.rd,eq ▸ dg.capacity,eq ▸ r24,eq ▸ count,dg.fits,trivial⟩)
  apply fromJump j
  have dm := (noWrites df).trans eq
  have arr : memLoad d.store fr.rbp (8*fr.r13.toNat)=data := by
    rw [dm]
    apply (fw.memLoad_eq _).trans plain
    have l := src.low
    simp [Outside,rs]; omega
  have gv : memLoad d.store 0x2013a8 64=0x102dc0 := by
    rw [dm]; apply (fw.memLoad_eq _).trans gotV
    simp [Outside,rs]; omega
  let e := copySite fr.r13 fr.rbp fr.rbx data
  let f := snapAt fr 8 d.store
  have wr : Atom.All fnCode d.arguments d.store (if fr.r13.toNat=0 then [] else [Atom.writable fr.rbx fr.r13.toNat]) := by
    split
    · trivial
    · exact ⟨dm ▸ dg.write (by omega),trivial⟩
  have stk (pos : 0<fr.r13.toNat) := dg.stack pos
  have srcG : fr.rbp.toNat+fr.r13.toNat≤fr.rsp.toNat-8 ∨ fr.rsp.toNat≤fr.rbp.toNat := by omega
  have dstG (pos : 0<fr.r13.toNat) : fr.rbx.toNat+fr.r13.toNat≤(fr.rsp-8).toNat ∨ (fr.rsp-8).toNat+8≤fr.rbx.toNat := by
    have h := stk pos; bv_omega
  have codeG (pos : 0<fr.r13.toNat) : fr.rbx.toNat+fr.r13.toNat≤0x102dc0 ∨ 0x102def≤fr.rbx.toNat := by have h := dg.code pos; omega
  have cc : Atom.All fnCode d.arguments d.store (e.before f) := by
    obtain ⟨r,rdx,_⟩ := (Atom.all_append _ _).1 dr
    exact (Atom.all_append _ _).2 ⟨(Atom.all_append _ _).2 ⟨(Atom.all_append _ _).2 ⟨r,s8 _ (dm ▸ stack.of_frame fw) _⟩,
      rdx,rfl,dm ▸ r16,dm ▸ (loc 16 (by decide)).trans ptr,dm ▸ got.of_frame fw,gv,srcG,trivial⟩,
      (Atom.all_append _ _).2 ⟨⟨rfl,arr,dm ▸ src.of_frame fw,dg.heap,codeG,dstG,trivial⟩,wr⟩⟩
  apply (Invoke.run e (copyOutCorrect _ _) (copySiteValid _ _ _ _) f d dl cc rfl).bind
  rintro t ⟨tl,tr,tf⟩
  obtain ⟨base,out,_⟩ := (Atom.all_append _ _).1 tr
  apply Forward.here
  refine ⟨tl,base,out,(widen (show RamWriteFrame a.store d.store rs from dm ▸ fw) ?_).trans tf ?_⟩
  · simp [RegionsWithin,rs,deliveryWrites]; omega
  · simp [RegionsWithin,e,copySite,f,snapAt,Activation.region,deliveryWrites]; bv_omega

end ChaCha20Poly1305.Proofs.Decrypt.Wrapper
