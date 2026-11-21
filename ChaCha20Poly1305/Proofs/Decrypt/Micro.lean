import ChaCha20Poly1305.Proofs.Decrypt.Segment
import ChaCha20Poly1305.Proofs.Decrypt.Refine
import ChaCha20Poly1305.Proofs.Decrypt.RoundFrame

namespace ChaCha20Poly1305.Proofs.Decrypt.Micro
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program

inductive Point | before | after

def program : Program (fun _ => _root_.Empty) Point (fun _ => 0) 0 := ⟨fun
  | .before => .terminate (.br ⟨.after,#v[]⟩)
  | .after => .terminate (.ret #v[])⟩

structure Step where
  entry : Lifted.Label
  exit : Lifted.Label
  pre : List Atom
  post : List Atom
  writes : List MemoryRegion

def layout (s : Step) : Layout program Empty.semantics lifted Ram where
  start | .before => s.entry | .after => s.exit
  Params := fun _ => Unit
  args := fun _ _ => #v[]
  store := fun _ _ => ()
  atoms l _ _ := match l with | .before => s.pre | .after => s.post
  Result := Unit
  output := fun _ => ⟨#v[],none,()⟩
  done := fun _ _ => []
  original := id
  retAddr := fun _ => 0
  regions := fun _ => s.writes

def Valid (s : Step) := (layout s).BlockSimulation fnCode .before

theorem run {s : Step} (ok : Valid s) {a : lifted.Location} (hl : a.label = s.entry)
    (hin : Atom.All fnCode a.arguments a.store s.pre) :
    Ahead lifted fnCode (fun b => b.label = s.exit ∧ Atom.All fnCode b.arguments b.store s.post ∧
      RamWriteFrame a.store b.store s.writes) a := by
  have h := segment (layout s) (j := .after) ok rfl (a := a) (c := a.store)
    ⟨hl,⟨(),rfl,rfl,hin⟩,.refl _ _⟩
  obtain ⟨b,steps,bl,⟨_,_,_,out⟩,f⟩ := h
  exact ⟨b,steps,bl,out,f⟩

end ChaCha20Poly1305.Proofs.Decrypt.Micro
