import ChaCha20Poly1305.Proofs.Decrypt.AuthPass

namespace ChaCha20Poly1305.Proofs.Decrypt.Hash
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program
open Poly1305 Standards.RFC.ChaCha20Poly1305
set_option allowUnsafeReducibility true in
attribute [local reducible] ChaCha20Poly1305.Proofs.Decrypt.Lifted.lifted
set_option maxHeartbeats 650000
set_option maxRecDepth 6500

theorem passBoth (fr : Activation) (pa pc vec la lc tag : BitVec 64) (key : Vector UInt8 32)
    (aad ct : ByteArray) (a : lifted.Location) (hla : la.toNat=aad.size) (hlc : lc.toNat=ct.size)
    (nc : lc.toNat<2^32) (ga : PadScope fr pa aad.size a.store) (gc : PadScope fr pc ct.size a.store)
    (vl : Readable a.store vec 8) (vp : memLoad a.store vec 64=pc)
    (vsep : vec.toNat+8≤fr.rsp.toNat-96 ∨ fr.rsp.toNat+392≤vec.toNat)
    (limit : fr.r15=274877906879) (atV : memLoad a.store (fr.rsp+16) 64=vec)
    (atA : memLoad a.store (fr.rsp+192) 64=la) (atC : memLoad a.store (fr.rsp+24) 64=lc)
    (atT : memLoad a.store (fr.rsp+448) 64=tag) (tagR : Readable a.store (fr.rsp+448) 8)
    (rawA : memLoad a.store pa (8*aad.size)=Bytes.packed aad) (rawC : memLoad a.store pc (8*ct.size)=Bytes.packed ct)
    (start : Source false fr pa aad a.store) (label : a.label=enter false (decide (16≤aad.size)))
    (reg : Atom.All fnCode a.arguments a.store (regs fr)) (hp : Atom.All fnCode a.arguments a.store (keyPads key fr.rdi))
    (hr : Atom.All fnCode a.arguments a.store (rData fr.rdi (rWords key)))
    (ha : Atom.All fnCode a.arguments a.store (accData fr.rdi zeroAcc)) : Forward a (Verified fr a.store key aad ct tag) := by
  apply (absorb false fr pa aad key 0 zeroAcc zeroRep a 0 ga start (fun h => nomatch h) label reg hr ha rawA).bind
  intro b h
  let f := endFr false fr pa aad 0
  have sh := eShape false fr pa aad 0
  have floor := gc.floor
  have low := gc.area.readable.low
  have wl := widen h.frame (padWork ga)
  have wz := widen wl (workZone floor)
  have geo : PadScope f pc ct.size b.store := gc.move wl (workZone floor) sh.sp sh.ctx
  have ptr : memLoad b.store vec 64=pc := by
    apply (wz.memLoad_eq _).trans vp
    have lo := vl.low
    simp [Outside,zone]; omega
  have loc (i : Nat) (hi : i=16 ∨ i=192 ∨ i=24 ∨ i=448) :
      memLoad b.store (f.rsp+BitVec.ofNat 64 i) 64 = memLoad a.store (fr.rsp+BitVec.ofNat 64 i) 64 := by
    rw [sh.sp]
    apply workLocal wl
    all_goals rcases hi with rfl|rfl|rfl|rfl <;> omega
  obtain ⟨ws,rep,acc⟩ := h.acc
  have lim : f.r15=274877906879 := (endShape false fr pa aad 0).2.2.1.trans limit
  have sep := gc.apart
  have cl := gc.buf.low
  have craw : memLoad b.store pc (8*ct.size)=Bytes.packed ct := by
    apply (wz.memLoad_eq _).trans rawC
    simp [Outside,zone]; omega
  apply (ctPass f pc vec la lc tag key aad ct b ws hla hlc nc rep geo (vl.of_frame wl) ptr lim
    ((loc 16 (by decide)).trans atV) ((loc 192 (by decide)).trans atA) ((loc 24 (by decide)).trans atC)
    ((loc 448 (by decide)).trans atT) (sh.sp ▸ tagR.of_frame wl) craw h.label
    ((Atom.all_append _ _).1 h.regs).1 (sh.ctx ▸ workPads ga wl hp) (sh.ctx ▸ padKeepR ga wl hr) (sh.ctx ▸ acc)).bind
  intro d result
  obtain ⟨g,sg,registers⟩ := result.regs
  apply Forward.here
  exact ⟨result.label,wl.trans (sh.sp ▸ result.frame) (fun z hz => ⟨z,hz,Nat.le_refl _,Nat.le_refl _⟩),
    sh.sp ▸ result.mem,g,(show Shape fr f from sh).trans sg,registers⟩

def authWrites (sp : BitVec 64) := saved sp ++ work sp

structure Authenticated (fr : Activation) (m : Ram) (key : Vector UInt8 32) (aad ct : ByteArray) (tag : BitVec 64)
    (d : lifted.Location) : Prop where
  label : d.label=.l100577
  frame : RamWriteFrame m d.store (authWrites fr.rsp)
  mem : Atom.All fnCode d.arguments d.store (tagMem fr.rsp (vTag key aad ct))
  lo : memLoad d.store (fr.rsp+200) 64=fr.r14
  vec : memLoad d.store (fr.rsp+16) 64=fr.rbx
  regs : ∃ f, Shape fr f ∧ Atom.All fnCode d.arguments d.store (Hash.regs f ++ [.gpr 5 tag])

theorem authenticate (fr : Activation) (pa pc lc tag : BitVec 64) (key : Vector UInt8 32)
    (aad ct : ByteArray) (a : lifted.Location) (hla : fr.rbp.toNat=aad.size) (hlc : lc.toNat=ct.size)
    (na : fr.rbp.toNat<2^32) (nc : lc.toNat<2^32) (ga : PadScope fr pa aad.size a.store) (gc : PadScope fr pc ct.size a.store)
    (ptrA : 0<aad.size → fr.r13=pa)
    (vl : Readable a.store fr.rbx 8) (vp : memLoad a.store fr.rbx 64=pc)
    (vsep : fr.rbx.toNat+8≤fr.rsp.toNat-96 ∨ fr.rsp.toNat+392≤fr.rbx.toNat)
    (limit : fr.r15=274877906879) (atC : memLoad a.store (fr.rsp+24) 64=lc)
    (atT : memLoad a.store (fr.rsp+448) 64=tag) (tagR : Readable a.store (fr.rsp+448) 8)
    (rawA : memLoad a.store pa (8*aad.size)=Bytes.packed aad) (rawC : memLoad a.store pc (8*ct.size)=Bytes.packed ct)
    (label : a.label=.l1003e3) (reg : Atom.All fnCode a.arguments a.store (regs5 fr))
    (hp : Atom.All fnCode a.arguments a.store (keyPads key fr.rdi))
    (hr : Atom.All fnCode a.arguments a.store (rData fr.rdi (rWords key)))
    (ha : Atom.All fnCode a.arguments a.store (accData fr.rdi zeroAcc)) : Forward a (Authenticated fr a.store key aad ct tag) := by
  let f := aadRegs fr fr.rbp
  let full := decide (16≤aad.size)
  have geo := ga.code
  have cd : fr.rsp.toNat+208≤0x1003e3 ∨ 0x100417≤fr.rsp.toNat := by omega
  have ready : Atom.All fnCode a.arguments a.store ((setupA fr fr.rbp full).pre) := (Atom.all_append _ _).2
    ⟨((Atom.all_append _ _).1 reg).1,((Atom.all_append _ _).1 reg).2.1,ga.area.sub (Nat.le_refl _) (by omega),cd,trivial⟩
  obtain ⟨b,j,bl,out,sf⟩ := Micro.run (setupAValid fr fr.rbp full (by simp [full,hla])) label ready
  apply fromJump j
  change RamWriteFrame a.store b.store (saved fr.rsp) at sf
  have floor := ga.floor
  have lo := ga.area.readable.low
  have gz := savedZone floor
  have ag : PadScope f pa aad.size b.store := ga.move sf gz rfl rfl
  have cg : PadScope f pc ct.size b.store := gc.move sf gz rfl rfl
  obtain ⟨rg,savedSlots⟩ := (Atom.all_append _ _).1 out
  obtain ⟨sA,sV,sL,sT,_⟩ := savedSlots
  have start : Source false f pa aad b.store := ⟨(masks hla na).1,maskLowEq hla na,fun pos => sA.trans (ptrA pos)⟩
  have data {src len} (g : PadScope fr src len a.store) : memLoad b.store src (8*len)=memLoad a.store src (8*len) := by
    have sep := g.apart
    have low := g.buf.low
    apply (widen sf gz).memLoad_eq
    simp [Outside,zone]; omega
  have ptr : memLoad b.store fr.rbx 64=pc := by
    apply ((widen sf gz).memLoad_eq _).trans vp
    have low := vl.low
    simp [Outside,zone]; omega
  have keep (i : Nat) (h : i=24 ∨ i=448) : memLoad b.store (fr.rsp+BitVec.ofNat 64 i) 64=memLoad a.store (fr.rsp+BitVec.ofNat 64 i) 64 := by
    apply sf.memLoad_eq
    rcases h with rfl|rfl <;> simp [Outside,saved] <;> bv_omega
  have ctx := ga.ctxAt
  have across {ts : List Atom} (h : Atom.All fnCode a.arguments a.store ts)
      (all : ∀ t ∈ ts, ChaChaRound.pass (saved fr.rsp) t) := ChaChaRound.keepFrame (regs':=b.arguments) all sf h
  have safeP : ∀ t ∈ keyPads key fr.rdi, ChaChaRound.pass (saved fr.rsp) t := by
    intro t ht
    simp only [keyPads,Detached.pads,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl|rfl <;> simp [ChaChaRound.pass,Outside,saved,ctx] <;> bv_omega
  have safeR : ∀ t ∈ rData fr.rdi (rWords key), ChaChaRound.pass (saved fr.rsp) t := by
    intro t ht
    simp only [rData,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl|rfl|rfl|rfl|rfl <;> simp [ChaChaRound.pass,Outside,saved,ctx] <;> bv_omega
  have safeA : ∀ t ∈ accData fr.rdi zeroAcc, ChaChaRound.pass (saved fr.rsp) t := by
    intro t ht
    simp only [accData,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl|rfl|rfl|rfl|rfl <;> simp [ChaChaRound.pass,Outside,saved,ctx] <;> bv_omega
  apply (passBoth f pa pc fr.rbx fr.rbp lc tag key aad ct b hla hlc nc ag cg (vl.of_frame sf) ptr vsep limit
    sV sL ((keep 24 (by decide)).trans atC) ((keep 448 (by decide)).trans atT) (tagR.of_frame sf)
    ((data ga).trans rawA) ((data gc).trans rawC) start bl rg (across hp safeP) (across hr safeR) (across ha safeA)).bind
  intro d h
  have loc := workLocal h.frame
  obtain ⟨e,⟨sh.sp,sh.ctx,sh.mx,sh.ft,sh.fc⟩,reg'⟩ := h.regs
  apply Forward.here
  refine ⟨h.label,(widen sf (fun r h => ⟨r,List.mem_append_left _ h,Nat.le_refl _,Nat.le_refl _⟩)).trans h.frame
        (fun r h => ⟨r,List.mem_append_right _ h,Nat.le_refl _,Nat.le_refl _⟩),h.mem,
      (loc 200 64 (by change fr.rsp.toNat+456≤2^64; omega) floor (by decide) (by decide) (by decide) (by decide)).trans sT,
      (loc 16 64 (by change fr.rsp.toNat+456≤2^64; omega) floor (by decide) (by decide) (by decide) (by decide)).trans sV,e,⟨sh.sp,sh.ctx,sh.mx,sh.ft,sh.fc⟩,reg'⟩

end ChaCha20Poly1305.Proofs.Decrypt.Hash
