import ChaCha20Poly1305.Proofs.Decrypt.PadRun

namespace ChaCha20Poly1305.Proofs.Decrypt.Hash
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program
open Poly1305
set_option maxHeartbeats 500000
set_option maxRecDepth 6000
set_option pp.maxSteps 130
set_option allowUnsafeReducibility true in
attribute [local reducible] ChaCha20Poly1305.Proofs.Decrypt.Lifted.lifted

def padEnd : Bool → Lifted.Label | false => .l100479 | true => .l1004fc
def padStart : Bool → Lifted.Label | false => .l10043a | true => .l1004c2

private theorem mulStart (ct : Bool) (fr : Activation) (src : BitVec 64) (s : ByteArray) (a b : lifted.Location)
    (r ws out : Vector (BitVec 32) 5) (g : PadScope fr src s.size a.store) (h : Copied ct fr src s a.store b)
    (hw : Atom.All fnCode a.arguments a.store (rData fr.rdi r ++ accData fr.rdi ws)) :
    Atom.All fnCode b.arguments b.store ((padMul ct ⟨r,ws,word s (s.size/16)⟩ out fr.rdi).before
      (snapAt (lastFr ct fr src) 96 b.store)) := by
  have inputs := g.keepAcc (rs' := b.arguments) h.writes hw
  have hi := split128 (rs := b.arguments) h.data
  have g := g.after (widen h.writes (tempToPad g))
  have st := g.below
  have sp := g.floor
  have ctx := g.ctx
  have cw := g.area
  have low := cw.readable.low
  have align := g.align
  have code := g.code
  have ptr := g.ctxAt
  have regs := h.regs
  unpack_atoms hi []
  unpack_atoms inputs []
  cases ct <;> unpack_atoms regs [regs5,lastFr,moved,baseFr] <;> join_atoms [lastFr,moved,baseFr]
  all_goals first | assumption | rfl | (apply Readable.sub cw.readable <;> bv_omega) | bv_omega

theorem padBlock (ct : Bool) (fr : Activation) (src : BitVec 64) (s : ByteArray) (key : Vector UInt8 32)
    (val : Nat) (ws : Vector (BitVec 32) 5) (rep : represents ws val) (a : lifted.Location)
    (g : PadScope fr src s.size a.store) (args : TailArgs ct fr src s)
    (rs : Atom.All fnCode a.arguments a.store (partEntry ct fr src))
    (data : memLoad a.store src (8*s.size)=Bytes.packed s) (entry : a.label=padStart ct)
    (hw : Atom.All fnCode a.arguments a.store (rData fr.rdi (rWords key) ++ accData fr.rdi ws)) :
    Forward a (fun b => b.label = padEnd ct ∧ Atom.All fnCode b.arguments b.store (regs5 (lastFr ct fr src)) ∧
      RamWriteFrame a.store b.store (padRegions fr) ∧ ∃ out,
      represents out (stepAcc (rKey key) val (blockNumber s (s.size/16))) ∧
      Atom.All fnCode b.arguments b.store (accData fr.rdi out)) := by
  apply (copyPartial ct fr src s a g args rs data (by cases ct <;> exact entry)).bind
  intro b copied
  let y : Mul.Input := ⟨rWords key,ws,word s (s.size/16)⟩
  let out := Mul.output y
  let f := snapAt (lastFr ct fr src) 96 b.store
  apply (Invoke.run (padMul ct y out fr.rdi) (multiplyCorrect y) (padMulValid ct y out fr.rdi) f b
    (by cases ct <;> exact copied.label) (mulStart ct fr src s a b _ _ out g copied hw) rfl).bind
  rintro c ⟨lc,rr,wf⟩
  have eq : f.region :: (padMul ct y out fr.rdi).footprint = regions fr := by
    have floor := g.floor
    cases ct <;> simp [f,snapAt,lastFr,moved,baseFr,afterFill,Activation.region,padMul,regions] <;> bv_omega
  rw [eq] at wf
  have wr := (widen copied.writes (tempToPad g)).trans wf
    (show RegionsWithin (regions fr) (padRegions fr) from fun z hz => ⟨z,.tail _ hz, Nat.le_refl _,Nat.le_refl _⟩)
  apply Forward.here
  refine ⟨by cases ct <;> exact lc,?_,wr,out,?_,?_⟩
  · cases ct <;> exact ((Atom.all_append _ _).1 rr).1
  · rw [← lastNat s]; exact nextRep rep _
  · cases ct <;> exact ((Atom.all_append _ _).1 rr).2

end ChaCha20Poly1305.Proofs.Decrypt.Hash
