import ChaCha20Poly1305.Proofs.Decrypt.XorTail1
import ChaCha20Poly1305.Proofs.Decrypt.XorTail4
import ChaCha20Poly1305.Proofs.Decrypt.XorFull
import ChaCha20Poly1305.Proofs.Decrypt.Segment

namespace ChaCha20Poly1305.Proofs.Decrypt.Stream.Xor
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 600000

def src (k : Kind) (x : Input) : BitVec 64 :=
  match k with | .full => x.sp+x.off+301 | _ => x.buf+x.off
def key (k : Kind) (x : Input) : BitVec 64 :=
  match k with | .full => x.sp+x.off+237 | _ => x.keyBase+64+x.off

def attrs (k : Kind) (x : Input) := match k with
  | .full => geoFull x | .tail4 | .tail1 => geoTail k x

def saved (k : Kind) (x : Input) := match k with
  | .full => fullRegs x | .tail4 => tail4Regs x | .tail1 => tail1Regs x

def regsAt (k : Kind) (l : Label) (last : Bool) (x : Input) := match k with
  | .full => fullPointers l last x | .tail4 => tail4Pointers l last x | .tail1 => tail1Pointers l last x

def dataAt (k : Kind) (l : Label) (x : Input) := match k with
  | .full => fullData l x | .tail4 => tail4Data l x | .tail1 => tail1Data l x

private theorem spec (k : Kind) (x : Input) (stop : Bool) (l : Label) (m : Ram) (args) {orig p} :
    Atom.All fnCode args m ((layout k x stop).atoms l orig p) ↔
      Atom.All fnCode args m (attrs k x) ∧ Atom.All fnCode args m (saved k x) ∧
      Atom.All fnCode args m (regsAt k l stop x) ∧ Atom.All fnCode args m (dataAt k l x) := by
  cases k <;> simp only [layout,Atom.all_append,attrs,saved,regsAt,dataAt,and_assoc]

def readAt (m : Ram) (base : BitVec 64) (i : Nat) := memLoad m (base + BitVec.ofNat 64 i) 8
def readFour (m : Ram) (base : BitVec 64) : Vector (BitVec 8) 4 := Vector.ofFn fun i => readAt m base i.val

def loaded (k : Kind) (x : Input) (m : Ram) : Input :=
  {x with keyBytes := readFour m (key k x), srcBytes := readFour m (src k x)}

private theorem inputs (k : Kind) (x : Input) (m : Ram) {args} :
    Atom.All fnCode args m (dataAt k .start (loaded k x m)) := by
  cases k <;> simp (config := {decide := true}) only [dataAt,fullData,tail4Data,tail1Data,Atom.All,Atom.Holds,
    loaded,readFour,readAt,src,key,Vector.getElem_ofFn,BitVec.add_assoc,BitVec.reduceAdd,
    BitVec.reduceOfNat,BitVec.add_zero, and_true,true_and]
  all_goals repeat' constructor
  all_goals rfl

def Chunk (k : Kind) (x : Input) (m m' : Ram) := ∀ i, i < bytes k →
  readAt m' (dst k x) i = readAt m (key k x) i ^^^ readAt m (src k x) i

private theorem fourCases (P : Nat → Prop) (p0 : P 0) (p1 : P 1) (p2 : P 2) (p3 : P 3)
    (i : Nat) (hi : i<4) : P i := by
  rcases (show i=0 ∨ i=1 ∨ i=2 ∨ i=3 by omega) with rfl | rfl | rfl | rfl <;> assumption

private theorem outputs (k : Kind) (x : Input) (m m' : Ram) {args}
    (h : Atom.All fnCode args m' (dataAt k .next (loaded k x m))) : Chunk k x m m' := by
  cases k
  case tail1 =>
    intro i hi; change i < 1 at hi
    have eq : i=0 := by omega
    subst i
    exact h.1
  all_goals
    apply fourCases
    · exact h.1
    · exact h.2.1
    · exact h.2.2.1
    · exact h.2.2.2.1

structure ReadyAt (k : Kind) (x : Input) (l : Label) (stop : Bool) (a : lifted.Location) : Prop where
  label : a.label = (layout k x stop).start l
  attrs : Atom.All fnCode a.arguments a.store (attrs k x)
  saved : Atom.All fnCode a.arguments a.store (saved k x)
  regs : Atom.All fnCode a.arguments a.store (regsAt k l stop x)

theorem iteration (k : Kind) (x : Input) (stop : Bool) (eq : done k x ↔ stop = true)
    {a : lifted.Location} (h : ReadyAt k x .start stop a) :
    Ahead lifted fnCode (fun b => ReadyAt k x .next stop b ∧ Chunk k x a.store b.store ∧
      RamWriteFrame a.store b.store [⟨(dst k x).toNat, bytes k⟩]) a := by
  let y := loaded k x a.store
  have r : (layout k y stop).Rel fnCode a.store (unitLoc .start) a :=
    ⟨h.label,⟨(),rfl,rfl,(spec ..).2 ⟨h.attrs,h.saved,h.regs,inputs ..⟩⟩,.refl _ _⟩
  have step : (layout k y stop).BlockSimulation fnCode .start := by
    cases k with
    | full => exact fullStep _ _ eq
    | tail4 => exact tail4Step _ _ eq
    | tail1 => exact tail1Step _ _ eq
  obtain ⟨b,run,hb⟩ := segment (layout k y stop) (j := .next) step rfl r
  obtain ⟨lbl,⟨p,_,_,atoms⟩,frame⟩ := hb
  obtain ⟨ha,hs,hp,hd⟩ := (spec k y stop .next _ _).1 atoms
  exact ⟨b,run,⟨lbl,ha,hs,hp⟩,outputs _ _ _ _ hd,frame⟩

end ChaCha20Poly1305.Proofs.Decrypt.Stream.Xor
