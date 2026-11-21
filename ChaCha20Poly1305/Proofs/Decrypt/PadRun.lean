import ChaCha20Poly1305.Proofs.Decrypt.PadScope

namespace ChaCha20Poly1305.Proofs.Decrypt.Hash
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program
open Poly1305
set_option allowUnsafeReducibility true in
attribute [local reducible] ChaCha20Poly1305.Proofs.Decrypt.Lifted.lifted
set_option maxHeartbeats 650000
set_option maxRecDepth 6000
set_option pp.maxSteps 140

@[refine_layout] def partEntry (ct : Bool) (fr : Activation) (src : BitVec 64) : List Atom :=
  regs fr ++ match ct with
  | true => [.gpr 5 fr.rbp]
  | false => [.mem (fr.rsp+8) 64 src]

def baseFr (fr : Activation) (src : BitVec 64) := {fr with rsi := src}
def moved (ct : Bool) (fr : Activation) (src : BitVec 64) := afterFill ct (baseFr fr src)
def lastFr (ct : Bool) (fr : Activation) (src : BitVec 64) := {moved ct fr src with rbx := fr.rsp+32}

def regs5 (fr : Activation) := regs fr ++ [.gpr 5 fr.rbp]

structure TailArgs (ct : Bool) (fr : Activation) (src : BitVec 64) (s : ByteArray) : Prop where
  rem : fr.r14 = amount s
  ptr : copySource ct (moved ct fr src) = addr src (s.size/16)

private theorem fillStart (ct : Bool) (fr : Activation) (src : BitVec 64) (s : ByteArray) (a : lifted.Location)
    (g : PadScope fr src s.size a.store) (args : TailArgs ct fr src s)
    (rs : Atom.All fnCode a.arguments a.store (partEntry ct fr src)) :
    Atom.All fnCode a.arguments a.store ((fill ct (fr.rsp+fr.r14+32) (16-fr.r14)).before
       (snapAt (baseFr fr src) 8 a.store)) := by
  have stack := g.below
  have area := g.area
  have bound := g.area.readable.low
  have floor := g.floor
  have align := g.align
  have code := g.code
  have got := g.fillRead
  have addr := g.fillAddr
  have rem := args.rem ▸ amountNat s
  have rest : ((16:BitVec 64)-fr.r14).toNat=16-s.size%16 := args.rem ▸ restNat s
  cases ct <;> unpack_atoms rs [] <;> join_atoms [baseFr]
  all_goals first | assumption | rfl | (apply Writable.sub stack <;> bv_omega) |
    (apply Writable.sub area <;> bv_omega) | (apply Readable.sub area.readable <;> bv_omega) | bv_omega

private theorem copyStart (ct : Bool) (fr : Activation) (src : BitVec 64) (s : ByteArray) (a : lifted.Location)
    (g : PadScope fr src s.size a.store) (args : TailArgs ct fr src s)
    (rs : Atom.All fnCode a.arguments a.store (regs5 (moved ct fr src)))
    (data : memLoad a.store src (8*s.size) = Bytes.packed s) :
    Atom.All fnCode a.arguments a.store ((copy ct (fr.rsp+32) fr.r14
      ((tailBits s).setWidth (8*fr.r14.toNat))).before (snapAt (moved ct fr src) 8 a.store)) := by
  have stack := g.below
  have area := g.area
  have bound := g.area.readable.low
  have floor := g.floor
  have align := g.align
  have code := g.code
  have got := g.copyRead
  have gv := g.copyAddr
  have buf := g.buf
  have low := buf.low
  have apart := g.apart
  have rem := args.rem ▸ amountNat s
  have hp := addrNat (i := s.size/16) low (by omega)
  have ptr := args.ptr
  have htake := loadPart (m := a.store) (p := src) (w := 8*s.size) (16*(s.size/16)) (s.size%16) (by omega)
  rw [data] at htake
  have useData : memLoad a.store (copySource ct (moved ct fr src)) (8*fr.r14.toNat) =
      (tailBits s).setWidth (8*fr.r14.toNat) := by
    rw [rem,ptr,BitVec.setWidth_eq]; exact htake.symm
  cases ct <;> simp only [copySource,moved,afterFill,baseFr] at ptr useData rs ⊢
  all_goals unpack_atoms rs [regs5,moved,baseFr] <;> join_atoms [moved,baseFr]
  all_goals first | assumption | rfl | (apply Writable.sub stack <;> bv_omega) |
    (apply Writable.sub area <;> bv_omega) | (apply Readable.sub buf <;> bv_omega) | bv_omega

structure Copied (ct : Bool) (fr : Activation) (src : BitVec 64) (s : ByteArray) (m : Ram) (b : lifted.Location) : Prop where
  label : b.label = (match ct with | true => Lifted.Label.l1004f1 | false => Lifted.Label.l10046e)
  regs : Atom.All fnCode b.arguments b.store (regs5 (lastFr ct fr src))
  data : memLoad b.store (fr.rsp+32) 128 = word s (s.size/16)
  writes : RamWriteFrame m b.store (tempAreas fr)

theorem copyPartial (ct : Bool) (fr : Activation) (src : BitVec 64) (s : ByteArray) (a : lifted.Location)
    (g : PadScope fr src s.size a.store) (args : TailArgs ct fr src s)
    (rs : Atom.All fnCode a.arguments a.store (partEntry ct fr src)) (data : memLoad a.store src (8*s.size)=Bytes.packed s)
    (entry : a.label = (match ct with | true => Lifted.Label.l1004c2 | false => Lifted.Label.l10043a)) :
    Forward a (Copied ct fr src s a.store) := by
  let dest := fr.rsp+fr.r14+32
  let num := (16:BitVec 64)-fr.r14
  let low := fr.rsp+32
  let bits := (tailBits s).setWidth (8*fr.r14.toNat)
  let f := snapAt (baseFr fr src) 8 a.store
  have leap := Invoke.run (fill ct dest num) fillFnCorrect (fillValid ct dest num) f a (by cases ct <;> exact entry)
    (fillStart ct fr src s a g args rs) rfl
  have sp := g.floor
  have slim := g.area.readable.low
  have rem : fr.r14.toNat=s.size%16 := args.rem ▸ amountNat s
  have rest : num.toNat=16-s.size%16 := by dsimp only [num]; rw [args.rem,restNat]
  have dst : dest.toNat = fr.rsp.toNat+32+s.size%16 := by dsimp [dest]; bv_omega
  have lw : low.toNat=fr.rsp.toNat+32 := by dsimp [low]; bv_omega
  apply leap.bind
  rintro b ⟨lb,rr,ff⟩
  change RamWriteFrame a.store b.store ((snapAt fr 8 a.store).region :: [⟨dest.toNat,num.toNat⟩]) at ff
  have wr : RamWriteFrame a.store b.store (tempAreas fr) :=
    widen ff (tempToFrame g (by omega : fr.rsp.toNat+32≤dest.toNat) (by omega : dest.toNat+num.toNat≤fr.rsp.toNat+48))
  have wp := widen wr (tempToPad g)
  have rb : Atom.All fnCode b.arguments b.store (regs5 (moved ct fr src)) ∧ memLoad b.store dest (8*num.toNat)=0 := by
    cases ct <;> unpack_atoms rr [f,baseFr] <;> constructor
    all_goals first | assumption | (join_atoms [regs5,moved,baseFr] <;> assumption)
  let cf := snapAt (moved ct fr src) 8 b.store
  apply (Invoke.run (copy ct low fr.r14 bits) copyFnCorrect (copyValid ct low fr.r14 bits) cf b (by cases ct <;> exact lb)
    (copyStart ct fr src s b (g.after wp) args rb.1 ((g.data wp).trans data)) rfl).bind
  rintro c ⟨cl,atC,wf⟩
  have fc : RamWriteFrame b.store c.store ((snapAt fr 8 b.store).region :: [⟨low.toNat,fr.r14.toNat⟩]) := by
    cases ct <;> exact wf
  have fin := wr.trans fc (tempToFrame (g.after wp) (by omega : fr.rsp.toNat+32≤low.toNat)
    (by omega : low.toNat+fr.r14.toNat≤fr.rsp.toNat+48))
  have kept : memLoad c.store dest (8*num.toNat) = 0 := by
    rw [fc.memLoad_eq,rb.2]; simp [Outside,snapAt,Activation.region,dst,lw]; bv_omega
  have rr : Atom.All fnCode c.arguments c.store (regs5 (lastFr ct fr src)) ∧ memLoad c.store low (8*fr.r14.toNat)=bits := by
    cases ct <;> unpack_atoms atC [cf,moved,baseFr] <;> constructor
    all_goals first | assumption | (join_atoms [regs5,lastFr,moved,baseFr] <;> assumption)
  apply Forward.here
  refine ⟨by cases ct <;> exact cl,rr.1,paddedLoad s low ?_ ?_,fin⟩
  · apply BitVec.eq_of_toNat_eq
    have e := congrArg BitVec.toNat rr.2
    change (memLoad c.store low (8*fr.r14.toNat)).toNat = ((tailBits s).setWidth (8*fr.r14.toNat)).toNat at e
    rw [rem,BitVec.setWidth_eq] at e
    exact e
  · have ptr : low+BitVec.ofNat 64 (s.size%16)=dest := by
      dsimp [low,dest]; rw [←rem,BitVec.ofNat_toNat,BitVec.setWidth_eq]; ac_rfl
    rw [ptr,←rest]; exact kept

end ChaCha20Poly1305.Proofs.Decrypt.Hash
