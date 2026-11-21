import ChaCha20Poly1305.Proofs.Decrypt.Feed

namespace ChaCha20Poly1305.Proofs.Decrypt.Hash
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program
open Poly1305
set_option allowUnsafeReducibility true in
attribute [local reducible] ChaCha20Poly1305.Proofs.Decrypt.Lifted.lifted
set_option maxHeartbeats 650000
set_option maxRecDepth 6000
set_option pp.maxSteps 140

def testFr (fr : Activation) (s : ByteArray) (tag : BitVec 64) := {afterBlocks fr s with rbp := tag}
def endFr (ct : Bool) (fr : Activation) (src : BitVec 64) (s : ByteArray) (tag : BitVec 64) :=
  if s.size%16=0 then testFr fr s tag else lastFr ct (testFr fr s tag) src

structure Source (ct : Bool) (fr : Activation) (src : BitVec 64) (s : ByteArray) (m : Ram) : Prop where
  floor : basePtr ct fr=offset s
  rem : fr.r14=amount s
  pointer : 0<s.size → (match ct with | true => fr.r13=src | false => memLoad m (fr.rsp+8) 64=src)

structure End (ct : Bool) (fr : Activation) (src : BitVec 64) (s : ByteArray) (tag : BitVec 64)
    (key : Vector UInt8 32) (v : Nat) (m : Ram) (b : lifted.Location) : Prop where
  label : b.label=padEnd ct
  regs : Atom.All fnCode b.arguments b.store (Hash.regs (endFr ct fr src s tag) ++ bpAtoms ct tag)
  frame : RamWriteFrame m b.store (padRegions fr)
  acc : ∃ ws, represents ws (foldFrom s (rKey key) v (count s)) ∧ Atom.All fnCode b.arguments b.store (accData fr.rdi ws)

theorem absorb (ct : Bool) (fr : Activation) (src : BitVec 64) (s : ByteArray) (key : Vector UInt8 32) (v : Nat)
    (ws : Vector (BitVec 32) 5) (rep : represents ws v) (a : lifted.Location) (tag : BitVec 64)
    (g : PadScope fr src s.size a.store) (init : Source ct fr src s a.store)
    (tagAt : ct=true → Readable a.store (fr.rsp+448) 8 ∧ memLoad a.store (fr.rsp+448) 64=tag)
    (entry : a.label=enter ct (decide (16≤s.size))) (ready : Atom.All fnCode a.arguments a.store (regs fr))
    (hr : Atom.All fnCode a.arguments a.store (rData fr.rdi (rWords key)))
    (ha : Atom.All fnCode a.arguments a.store (accData fr.rdi ws))
    (raw : memLoad a.store src (8*s.size)=Bytes.packed s) :
    Forward a (End ct fr src s tag key v a.store) := by
  have area := g.area
  have low := area.readable.low
  have sp := g.floor
  have setup (many : 16≤s.size) : Atom.All fnCode a.arguments a.store (beginStep ct fr src).pre := by
    have p := init.pointer (by omega)
    cases ct <;> unpack_atoms ready [] <;> join_atoms []
    all_goals first | assumption | (apply Readable.sub area.readable <;> bv_omega)
  apply (beforeTest ct fr src s key v ws rep a (fun _ => g) init.floor entry ready setup hr ha raw).bind
  intro b h
  let tf := testFr fr s tag
  let pad := decide (s.size%16≠0)
  have rem : tf.r14.toNat=s.size%16 := init.rem ▸ amountNat s
  have cond : tf.r14≠0 ↔ pad=true := by dsimp [pad]; rw [decide_eq_true_eq,← BitVec.toNat_inj]; change (tf.r14.toNat≠0) ↔ _; rw [rem]
  have saved (i : Nat) (hi : i=8 ∨ i=448) :
      memLoad b.store (fr.rsp+BitVec.ofNat 64 i) 64 = memLoad a.store (fr.rsp+BitVec.ofNat 64 i) 64 := by
    apply h.frame.memLoad_eq
    rcases hi with rfl|rfl <;> simp [Outside,regions,g.ctxAt] <;> bv_omega
  have state := h.regs
  have test : Atom.All fnCode b.arguments b.store (testStep ct pad tf tag).pre := by
    cases ct
    · exact state
    · obtain ⟨rd,val⟩ := tagAt rfl
      exact (Atom.all_append _ _).2 ⟨state,rd.of_frame h.frame,(saved 448 (Or.inr rfl)).trans val,trivial⟩
  obtain ⟨c,bc,cl,rr,cf⟩ := Micro.run (testValid ct pad tf tag cond) h.label test
  apply fromJump bc
  have me := noWrites cf
  have frame : RamWriteFrame a.store c.store (padRegions fr) := me ▸ widen h.frame
    (fun z hz => ⟨z,.tail _ hz,Nat.le_refl _,Nat.le_refl _⟩)
  obtain ⟨ww,repW,acc⟩ := h.acc
  have ha' : Atom.All fnCode c.arguments c.store (accData fr.rdi ww) := by rw [me]; exact acc
  by_cases aligned : s.size%16=0
  · apply Forward.here
    refine ⟨?_,?_,frame,ww,?_,ha'⟩
    · cases ct <;> simpa [testStep,nextLabel,pad,aligned,padEnd] using cl
    · change Atom.All _ _ _ (regs tf ++ bpAtoms ct tag) at rr
      simpa only [endFr,ite_eq_left aligned] using rr
    · have n : count s=s.size/16 := by unfold count; omega
      simpa only [n] using repW
  · have pos : 0<s.size := by omega
    have p := init.pointer pos
    have floor := init.floor
    have args : TailArgs ct tf src s := by
      refine ⟨init.rem,?_⟩
      cases ct <;> dsimp [basePtr] at floor
      · change src+fr.r13=addr src (s.size/16); rw [floor]; rfl
      · change fr.r13+fr.r15=addr src (s.size/16); rw [p,floor]; rfl
    have partialRegs : Atom.All fnCode c.arguments c.store (partEntry ct tf src) := by
      cases ct
      · exact (Atom.all_append _ _).2 ⟨((Atom.all_append _ _).1 rr).1,me ▸ (saved 8 (Or.inl rfl)).trans p,trivial⟩
      · exact rr
    have gg := g.after frame
    have geo : PadScope tf src s.size c.store :=
      ⟨⟨gg.below,gg.ctx,gg.buf,gg.floor,gg.align,gg.stackCode,gg.ctxCode,gg.stackCtx,gg.stackBuf,gg.ctxBuf⟩,
        gg.area,gg.ctxAt,gg.apart,gg.code,gg.got,gg.copyRead,gg.copyAddr,gg.fillRead,gg.fillAddr⟩
    have start : c.label = padStart ct := by cases ct <;> simpa [testStep,nextLabel,pad,aligned,padStart] using cl
    have keyData : Atom.All fnCode c.arguments c.store (rData tf.rdi (rWords key)) := by
      rw [me]; exact unchangedR (fr := fr) g.toScope h.frame hr
    apply (padBlock ct tf src s key _ ww repW c geo args partialRegs ((g.data frame).trans raw) start
      ((Atom.all_append _ _).2 ⟨keyData,ha'⟩)).bind
    rintro d ⟨dl,drs,df,new,repNew,accNew⟩
    apply Forward.here
    refine ⟨dl,?_,frame.trans df (fun z hz => ⟨z,hz,Nat.le_refl _,Nat.le_refl _⟩),new,?_,accNew⟩
    · simp only [endFr,ite_eq_right aligned]
      cases ct
      · exact ((Atom.all_append _ _).1 drs).1
      · exact drs
    · have n : count s=s.size/16+1 := by unfold count; omega
      rw [n,foldFrom]; exact repNew

end ChaCha20Poly1305.Proofs.Decrypt.Hash
