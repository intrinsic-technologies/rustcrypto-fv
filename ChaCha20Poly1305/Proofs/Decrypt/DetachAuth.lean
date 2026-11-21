import ChaCha20Poly1305.Proofs.Decrypt.DetachPrep
import ChaCha20Poly1305.Proofs.Decrypt.AuthRun
import ChaCha20Poly1305.Proofs.Decrypt.DetachTag

namespace ChaCha20Poly1305.Proofs.Decrypt.Detached
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program
open Hash Poly1305 Standards.RFC.ChaCha20Poly1305
set_option allowUnsafeReducibility true in
attribute [local reducible] ChaCha20Poly1305.Proofs.Decrypt.Lifted.lifted
set_option linter.constructorNameAsVariable false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
set_option pp.maxSteps 160

@[refine_layout] def gotInfo (fr : Activation) : List Atom :=
  [.readable 0x2013a8 8,.mem 0x2013a8 64 0x102dc0,.readable 0x2013e0 8,.mem 0x2013e0 64 0x102d70,
   .fact (0x201748≤fr.rsp.toNat ∨ fr.rsp.toNat≤0x2013a8)]

theorem keepGot {fr m m' rs rs' regs} (h : Atom.All fnCode rs m (gotInfo fr)) (f : RamWriteFrame m m' regs)
    (le : RegionsWithin regs [⟨fr.rsp.toNat-864,864⟩]) (sp : 864≤fr.rsp.toNat) : Atom.All fnCode rs' m' (gotInfo fr) := by
  have sep := h.2.2.2.2.1
  change 0x201748≤fr.rsp.toNat ∨ fr.rsp.toNat≤0x2013a8 at sep
  apply ChaChaRound.keepFrame _ (widen f le) h
  intro t ht
  simp only [gotInfo,List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl|rfl|rfl|rfl|rfl <;> simp [ChaChaRound.pass,Outside] <;> omega

private theorem padGeo {fr : Activation} {src : BitVec 64} {n m rs}
    (read : Readable m src n) (sep : src.toNat+n≤fr.rsp.toNat-864 ∨ fr.rsp.toNat+8≤src.toNat)
    (code : fr.rsp.toNat≤0x1001f0 ∨ 0x102e00+864≤fr.rsp.toNat)
    (stack : Writable fnCode m (fr.rsp-864) 864) (floor : 864≤fr.rsp.toNat) (align : fr.rsp.toNat%16=8)
    (got : Atom.All fnCode rs m (gotInfo fr)) : PadScope (newCtx (physical fr)) src n m := by
  have low := stack.readable.low
  have v := read.low
  unpack_atoms got []
  constructor
  · constructor
    all_goals try dsimp only [newCtx,physical]
    all_goals first | assumption | (apply stack.sub <;> bv_omega) | bv_omega
  all_goals try dsimp only [newCtx,physical]
  all_goals first | assumption | rfl | (apply stack.sub <;> bv_omega) | bv_omega

def checkedAt (p : Packet) := if p.good then Lifted.Label.l1005d2 else .l1005ea
def checkedRegs (p : Packet) (fr : Activation) (a : lifted.Location) : Prop :=
  if p.good then ∃ f, Shape (newCtx (physical fr)) f ∧ Atom.All fnCode a.arguments a.store (regs5 f)
  else Atom.All fnCode a.arguments a.store (basic (physical fr) ++ [.low 0 8 1])

structure Checked (p : Packet) (fr : Activation) (m : Ram) (a : lifted.Location) : Prop where
  label : a.label=checkedAt p
  frame : RamWriteFrame m a.store (innerZone fr)
  regs : checkedRegs p fr a
  header : Atom.All fnCode a.arguments a.store (streamHeader p (physical fr).rsp)
  vec : memLoad a.store ((physical fr).rsp+16) 64=fr.r8

private theorem authHeader {p : Packet} {fr rs rs' m m'} (h : Atom.All fnCode rs m (streamHeader p (physical fr).rsp))
    (w : RamWriteFrame m m' (authWrites (physical fr).rsp)) (floor : 864≤fr.rsp.toNat) (low : fr.rsp.toNat<2^32) :
    Atom.All fnCode rs' m' (streamHeader p (physical fr).rsp) := by
  apply ChaChaRound.keepFrame _ w h
  intro t ht
  simp only [streamHeader,header,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp [ChaChaRound.pass,Outside,authWrites,work,saved,physical] <;> bv_omega

private theorem checkResult (p : Packet) {fr f : Activation} {a : lifted.Location}
    (sh : Shape (newCtx (physical fr)) f)
    (out : Atom.All fnCode a.arguments a.store (if p.good then regs f ++ [.gpr 5 (p.tag.extractLsb' 64 64)] else basic f ++ [.low 0 8 1])) :
    checkedRegs p fr a := by
  cases hg : p.good
  · simp only [hg,Bool.false_eq_true,ite_false] at out
    simp only [checkedRegs,hg,Bool.false_eq_true,ite_false]
    simpa only [basic,sh.sp,sh.mx,sh.ft,sh.fc,newCtx] using out
  · simp only [hg,ite_true] at out
    simp only [checkedRegs,hg,ite_true]
    exact ⟨{f with rbp:=p.tag.extractLsb' 64 64},⟨sh.sp,sh.ctx,sh.mx,sh.ft,sh.fc⟩,out⟩

attribute [local irreducible] memLoad memStore poly1305Mac poly1305KeyGen

theorem checkPrepared (p : Packet) (fr : Activation) (m : Ram) (a : lifted.Location)
    (pr : Prepared p fr m a) (ext : Atom.All fnCode a.arguments a.store (extraIn p fr))
    (stack : Writable fnCode a.store (fr.rsp-864) 864)
    (floor : 864≤fr.rsp.toNat) (align : fr.rsp.toNat%16=8) (got : Atom.All fnCode a.arguments a.store (gotInfo fr)) :
    Forward a (Checked p fr m) := by
  let f := newCtx (physical fr)
  have data := ext
  unpack_atoms data []
  have lo := stack.readable.low
  have ga : PadScope f p.pa p.aad.size a.store := padGeo (by assumption) (by assumption) (by assumption) stack floor align got
  have gc : PadScope f p.buf p.ct.size a.store := by rw [←p.length]; exact padGeo (show Writable fnCode a.store p.buf p.n.toNat by assumption).readable (by assumption) (by assumption) stack floor align got
  have ctRaw : memLoad a.store p.buf (8*p.ct.size)=Bytes.packed p.ct := by
    have eq : memLoad a.store p.buf (8*p.n.toNat)=p.src := by assumption
    unfold Packet.src Stream.encode at eq
    rw [p.length,BitVec.setWidth_eq] at eq
    exact eq
  obtain ⟨pd,ac⟩ := (Atom.all_append _ _).1 pr.ctx
  obtain ⟨pads0,r⟩ := (Atom.all_append _ _).1 pd
  have rd : Readable a.store fr.r8 8 := (show Readable a.store fr.r8 24 by assumption).sub (Nat.le_refl _) (by omega)
  have tagRead : Readable a.store (f.rsp+448) 8 := by
    rw [show f.rsp+448=fr.rsp+8 by dsimp [f,newCtx,physical]; bv_omega]; assumption
  have tagV : memLoad a.store (f.rsp+448) 64=p.tag.extractLsb' 64 64 := by
    rw [show f.rsp+448=fr.rsp+8 by dsimp [f,newCtx,physical]; bv_omega]; assumption
  apply (authenticate f p.pa p.buf p.n _ p.one p.aad p.ct a (by assumption) p.length (by assumption) p.small ga gc
    (by assumption) rd (by assumption) (by dsimp [f,newCtx,physical]; bv_omega) rfl pr.len tagV tagRead
    (by assumption) ctRaw pr.label pr.regs pads0 r ac).bind
  intro b q
  obtain ⟨e,sh,reg⟩ := q.regs
  let x : TagCompare.Input := ⟨p.computed.extractLsb' 0 64,p.computed.extractLsb' 64 64,
    p.tag.extractLsb' 0 64,p.tag.extractLsb' 64 64⟩
  have accept : TagCompare.ok x ↔ p.good=true := by
    rw [Packet.good,decide_eq_true_eq]
    exact halves
  have gg := ga.area.of_frame q.frame
  have pre : Atom.All fnCode b.arguments b.store ((checkTag e x p.good).pre) := by
    obtain ⟨rs,bp,_⟩ := (Atom.all_append _ _).1 reg
    obtain ⟨l,h,_⟩ := q.mem
    have val : memLoad b.store (f.rsp+200) 64=x.suppliedLo := q.lo.trans (show fr.r9=p.tag.extractLsb' 0 64 by assumption)
    have cw := ga.code
    have ck : e.rsp.toNat+208≤0x100577 ∨ 0x1005d2≤e.rsp.toNat := by rw [sh.sp]; omega
    refine (Atom.all_append _ _).2 ⟨rs,bp,sh.sp ▸ l,?_,sh.sp ▸ val,sh.sp ▸ gg.sub (Nat.le_refl _) (by omega),ck,trivial⟩
    rw [sh.sp]; change memLoad b.store (f.rsp+160+8) 64=_ at h
    rw [BitVec.add_assoc] at h; exact h
  obtain ⟨d,j,dl,dr,df⟩ := Micro.run (checkValid e x p.good accept) q.label pre
  apply fromJump j
  have fw : RamWriteFrame b.store d.store [slot f.rsp 6 1] := sh.sp ▸ df
  have hz := authHeader (p:=p) (fr:=fr) (rs':=b.arguments) pr.header q.frame floor (by bv_omega)
  apply Forward.here
  refine ⟨dl,(pr.frame.trans q.frame ?_).trans fw ?_,checkResult p sh dr,?_,?_⟩
  · simp [RegionsWithin,authWrites,saved,work,innerZone,f,newCtx,physical]; bv_omega
  · simp [RegionsWithin,innerZone,slot,f,newCtx,physical]; bv_omega
  · apply ChaChaRound.keepFrame _ fw hz
    intro t ht
    simp only [streamHeader,header,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp [ChaChaRound.pass,Outside,slot,f,newCtx,physical] <;> bv_omega
  · apply (fw.memLoad_eq _).trans q.vec
    simp [Outside,slot,f,newCtx,physical]; bv_omega

end ChaCha20Poly1305.Proofs.Decrypt.Detached
