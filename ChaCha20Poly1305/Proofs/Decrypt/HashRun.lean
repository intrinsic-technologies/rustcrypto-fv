import ChaCha20Poly1305.Proofs.Decrypt.HashLoop

namespace ChaCha20Poly1305.Proofs.Decrypt.Hash
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program
open Poly1305
set_option allowUnsafeReducibility true in
attribute [local reducible] ChaCha20Poly1305.Proofs.Decrypt.Lifted.lifted
set_option maxHeartbeats 600000
set_option maxRecDepth 6000
set_option pp.maxSteps 150

theorem addrNat {src i n} (h : (src : BitVec 64).toNat+n ≤ 2^32) (hi : 16*i≤n) :
    (addr src i).toNat = src.toNat+16*i := by
  unfold addr; bv_omega

def loopRegs (fr : Activation) (src : BitVec 64) (s : ByteArray) (i : Nat) : List Atom :=
  regs {fr with rbx := remain s i} ++ [.gpr 6 (addr src i)]

def doneLabel (ct : Bool) (s : ByteArray) (i : Nat) :=
  if i=s.size/16 then finish ct else site ct

structure Result (ct : Bool) (fr : Activation) (src : BitVec 64) (s : ByteArray) (key : Vector UInt8 32)
    (init i : Nat) (m : Ram) (b : lifted.Location) : Prop where
  label : b.label = doneLabel ct s i
  regs : Atom.All fnCode b.arguments b.store (loopRegs fr src s i)
  frame : RamWriteFrame m b.store (regions fr)
  acc : ∃ ws, represents ws (foldFrom s (rKey key) init i) ∧ Atom.All fnCode b.arguments b.store (accData fr.rdi ws)

theorem readWord {src : BitVec 64} {s : ByteArray} {m : Ram} (h : memLoad m src (8*s.size)=Bytes.packed s)
    {i : Nat} (hi : i < s.size/16) : memLoad m (addr src i) 128 = word s i := by
  rw [word,←h,extractLsb'_memLoad _ _ _ _ (by omega) (by decide) (by omega)]
  simp [addr]

private theorem beforeCall (fr : Activation) (src : BitVec 64) (s : ByteArray) (ct : Bool) (i : Nat)
    (ws r out : Vector (BitVec 32) 5) (a : lifted.Location) (hi : i<s.size/16)
    (g : Scope fr src s.size a.store)
    (reg : Atom.All fnCode a.arguments a.store (loopRegs fr src s i))
    (hr : Atom.All fnCode a.arguments a.store (rData fr.rdi r))
    (ha : Atom.All fnCode a.arguments a.store (accData fr.rdi ws))
    (hd : memLoad a.store src (8*s.size)=Bytes.packed s) :
    Atom.All fnCode a.arguments a.store
      ((call ct ⟨r,ws,word s i⟩ out fr.rdi).before (iter fr src s i a.store)) := by
  have block := split128 (rs := a.arguments) (readWord hd hi)
  obtain ⟨stack,ctx,buf,sp,align,sc,cc,xc,xb,cb⟩ := g
  have low := buf.low
  have ap := addrNat (i := i) low (by omega)
  have sr : Readable a.store (addr src i) 16 := buf.sub (by omega) (by omega)
  unpack_atoms reg [loopRegs]
  unpack_atoms hr []
  unpack_atoms ha []
  unpack_atoms block []
  join_atoms [iter]
  all_goals first | assumption | rfl | bv_omega

theorem unchangedR {fr src n m b rs r rs'} (g : Scope fr src n m) (f : RamWriteFrame m b (regions fr))
    (hr : Atom.All fnCode rs m (rData fr.rdi r)) : Atom.All fnCode rs' b (rData fr.rdi r) := by
  have ctx := g.ctx.readable.low
  have sp := g.floor
  have stack := g.stackCtx
  apply ChaChaRound.keepFrame _ f hr
  intro t ht
  simp only [rData,List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl|rfl|rfl|rfl|rfl
  all_goals simp [ChaChaRound.pass,Outside,regions] <;> bv_omega

theorem unchangedData {fr src n m b} (g : Scope fr src n m) (f : RamWriteFrame m b (regions fr)) :
    memLoad b src (8*n) = memLoad m src (8*n) := by
  have lo := g.buf.low
  have st := g.stackBuf
  have cd := g.ctxBuf
  have sp := g.floor
  apply f.memLoad_eq
  simp [Outside,regions]
  omega

theorem full (ct : Bool) (fr : Activation) (src : BitVec 64) (s : ByteArray) (key : Vector UInt8 32)
    (init : Nat) (ws : Vector (BitVec 32) 5) (rep : represents ws init) (a : lifted.Location)
    (g : Scope fr src s.size a.store) (pos : 0<s.size/16) (entry : a.label = site ct)
    (start : Atom.All fnCode a.arguments a.store (loopRegs fr src s 0))
    (hr : Atom.All fnCode a.arguments a.store (rData fr.rdi (rWords key)))
    (ha : Atom.All fnCode a.arguments a.store (accData fr.rdi ws))
    (data : memLoad a.store src (8*s.size)=Bytes.packed s) (i : Nat) (hi : i≤s.size/16) :
    Forward a (Result ct fr src s key init i a.store) := by
  induction i with
  | zero =>
    exact Forward.here ⟨by simpa [doneLabel,Nat.ne_of_lt pos] using entry,start,.refl _ _,ws,rep,ha⟩
  | succ i ih =>
    have hi' : i<s.size/16 := by omega
    apply (ih (by omega)).bind
    intro b old
    obtain ⟨reg,rep,acc⟩ := old.acc
    let y : Mul.Input := ⟨rWords key,reg,word s i⟩
    let out := Mul.output y
    let f := iter fr src s i b.store
    let edge := call ct y out fr.rdi
    have eqSite : edge.site = site ct := by cases ct <;> rfl
    have eqResume : edge.resume = resume ct := by cases ct <;> rfl
    have curr : b.label = edge.site := by rw [eqSite]; simpa [doneLabel,Nat.ne_of_lt hi'] using old.label
    have ok := Invoke.run edge (multiplyCorrect y) (callValid ct y out fr.rdi) f b curr
      (beforeCall fr src s ct i reg _ out b hi' (g.after old.frame) old.regs (unchangedR g old.frame hr)
        acc ((unchangedData g old.frame).trans data)) rfl
    apply ok.bind
    rintro c ⟨lbl,atoms,writes⟩
    let more := decide (i+1≠s.size/16)
    have low := g.buf.low
    have rem : f.rbx.toNat = 16*(s.size/16-i) := by
      change (BitVec.ofNat 64 _).toNat = _
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    have cond : f.rbx ≠ 16 ↔ more=true := by
      dsimp [more]; rw [decide_eq_true_eq,←BitVec.toNat_inj]; change (f.rbx.toNat≠16) ↔ _; omega
    change Atom.All fnCode _ _ ((regs f ++ [.gpr 5 (f.rsi+16)]) ++ accData f.rdi out) at atoms
    obtain ⟨r,aout⟩ := (Atom.all_append _ _).1 atoms
    apply (Forward.ofAhead (Micro.run (againValid ct more f cond) (lbl.trans eqResume) r)).bind
    rintro d ⟨dl,drs,df⟩
    change RamWriteFrame c.store d.store [] at df
    have wf : RamWriteFrame b.store c.store (regions fr) := iterRegion g.floor ▸ writes
    have res : represents out (foldFrom s (rKey key) init (i+1)) := by
      change represents out (stepAcc _ _ _)
      rw [←wordNat s i hi']
      exact nextRep rep (word s i)
    apply Forward.here
    refine ⟨?_,?_,(old.frame.trans wf (fun z hz => ⟨z,hz,Nat.le_refl _,Nat.le_refl _⟩)).trans df (by simp [RegionsWithin]),out,res,?_⟩
    · by_cases e : i+1=s.size/16 <;> simpa [doneLabel,again,more,e] using dl
    · have norm : f.rbx-16 = remain s (i+1) := by
        apply BitVec.eq_of_toNat_eq
        unfold remain
        bv_omega
      have ad : f.rsi+16 = addr src (i+1) := by
        change (src+BitVec.ofNat 64 (16*i))+16=src+BitVec.ofNat 64 (16*(i+1))
        rw [BitVec.add_assoc,show (16:BitVec 64)=BitVec.ofNat 64 16 from rfl,←BitVec.ofNat_add]
        congr 2 <;> omega
      unpack_atoms drs []
      join_atoms [loopRegs]
      all_goals first | assumption | (simp only [f,iter]; done) | simpa only [f,iter] using ‹_› | (rw [←norm] <;> assumption) | (rw [←ad] <;> assumption)
    · apply ChaChaRound.keepFrame _ df aout
      intro t ht
      simp only [accData,List.mem_cons,List.not_mem_nil,or_false] at ht
      rcases ht with rfl|rfl|rfl|rfl|rfl
      all_goals have hh := g.ctx.readable.low; simp [ChaChaRound.pass,Outside,f,iter] <;> bv_omega

end ChaCha20Poly1305.Proofs.Decrypt.Hash
