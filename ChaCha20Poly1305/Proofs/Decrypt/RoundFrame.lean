import ChaCha20Poly1305.Proofs.Decrypt.ChaChaLoop
import ChaCha20Poly1305.Proofs.Decrypt.FullRoundsAll
import ChaCha20Poly1305.Proofs.Decrypt.TailRoundsAll

namespace ChaCha20Poly1305.Proofs.Decrypt.ChaChaRound
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Refine ChaCha20Poly1305.Proofs.Lift
open Standards.RFC.ChaCha20Poly1305

def pass (regions : List MemoryRegion) : Atom → Prop
  | .fact _ | .readable .. | .writable .. => True
  | .mem a w _ => Outside regions a (w/8)
  | .reg .. | .low .. | .words .. => False

theorem keepFrame {regions : List MemoryRegion} {code : CodeMap} {m m' : Ram} {regs regs'}
    {as : List Atom} (safe : ∀ a ∈ as, pass regions a) (h : RamWriteFrame m m' regions)
    (ha : Atom.All code regs m as) : Atom.All code regs' m' as := by
  induction as with
  | nil => trivial
  | cons a as ih =>
    obtain ⟨head,tail⟩ := ha
    refine ⟨?_, ih (fun b hb => safe b (.tail _ hb)) tail⟩
    have p := safe a (.head _)
    cases a with
    | reg | low | words => exact False.elim p
    | fact => exact head
    | readable => exact Readable.of_frame head h
    | writable => exact Writable.of_frame head h
    | mem => exact (h.memLoad_eq p).trans head

theorem runFramed (lay : Layout program dialect Lifted.lifted Activation)
    (hs : ∀ l, l ≠ .finish → lay.BlockSimulation Lifted.fnCode l)
    (hx : ∀ (fr : Activation) (m : Ram), lay.original {fr with original := m} = m)
    (ha : ∀ (fr : Activation) (m : Ram) l p, lay.atoms l {fr with original := m} p = lay.atoms l fr p)
    (hr : ∀ (fr : Activation) (m : Ram), lay.regions {fr with original := m} = lay.regions fr)
    (params : ∀ l, Data → lay.Params l)
    (hargs : ∀ l p, lay.args l (params l p) = #v[p])
    {w : Vector UInt32 16} {fr : Activation} {a : Lifted.lifted.Location}
    {as : List Atom} {big : List MemoryRegion}
    (safe : ∀ t ∈ as, pass (lay.regions fr) t) (within : RegionsWithin (lay.regions fr) big)
    (label : a.label = lay.start .q0)
    (atoms : Atom.All Lifted.fnCode a.arguments a.store
      (lay.atoms .q0 fr (params .q0 ⟨w,10⟩) ++ as))
    (frame : RamWriteFrame fr.original a.store big)
    (inj : ∀ l p q, lay.args l p = lay.args l q → p = q) :
    Ahead Lifted.lifted Lifted.fnCode (fun b => b.label = lay.start .finish ∧
      Atom.All Lifted.fnCode b.arguments b.store (lay.atoms .finish fr (params .finish ⟨rounds 10 w,0⟩) ++ as) ∧
      RamWriteFrame fr.original b.store big) a := by
  rw [Atom.all_append] at atoms
  let snap := {fr with original := a.store}
  have enter : lay.Rel Lifted.fnCode snap (loc .q0 ⟨w,10⟩) a :=
    ⟨label, ⟨_,(hargs _ _).symm,Subsingleton.elim _ _, (ha ..) ▸ atoms.1⟩,
      (hx ..) ▸ RamWriteFrame.refl _ _⟩
  obtain ⟨b,steps,hb⟩ := loop lay hs (n := 10) (by decide) (by decide) enter
  obtain ⟨lbl,⟨p,hp,_,pat⟩,hf⟩ := hb
  have eq : p = params .finish ⟨rounds 10 w,0⟩ := inj _ _ _ (hp.symm.trans (hargs ..).symm)
  subst p
  change Atom.All _ _ _ (lay.atoms .finish snap _) at pat
  rw [show snap = {fr with original := a.store} from rfl, ha] at pat
  rw [show snap = {fr with original := a.store} from rfl, hx,hr] at hf
  exact ⟨b,steps,lbl,(Atom.all_append _ _).2 ⟨pat,keepFrame safe hf atoms.2⟩,frame.trans hf within⟩

end ChaCha20Poly1305.Proofs.Decrypt.ChaChaRound
