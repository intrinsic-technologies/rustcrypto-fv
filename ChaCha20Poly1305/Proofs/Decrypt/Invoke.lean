import ChaCha20Poly1305.Proofs.Decrypt.Micro
import ChaCha20Poly1305.Proofs.Decrypt.Compose

namespace ChaCha20Poly1305.Proofs.Decrypt
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program

abbrev Result := Output Value Ram Reg.count
abbrev Runs (a : lifted.Location) (post : Result → Prop) := ∃ o,
  lifted.program.Exec (ChaCha20Poly1305.Proofs.Lift.dialect fnCode) ⟨a,[]⟩ o ∧ post o

def Forward (a : lifted.Location) (spec : lifted.Location → Prop) : Prop :=
  ∀ (P : Result → Prop), (∀ b, spec b → Runs b P) → Runs a P

theorem Forward.ofAhead {a spec} (h : Ahead lifted fnCode spec a) : Forward a spec := by
  intro _ cont
  obtain ⟨b,r,hb⟩ := h
  obtain ⟨o,run,p⟩ := cont b hb
  exact ⟨o,execJump r run,p⟩

theorem Forward.bind {a P Q} (h : Forward a P) (k : ∀ b, P b → Forward b Q) : Forward a Q :=
  fun p cont => h p (fun b hb => k b hb p cont)

theorem Forward.here {a P} (h : P a) : Forward a P := fun _p k => k a h

structure Callee where
  entry : Lifted.Label
  abi : Activation → List Atom
  pre : Activation → List Atom
  post : Activation → List Atom
  writes : Activation → List MemoryRegion

abbrev abiOut := Decrypt.doneAt

def Callee.Correct (k : Callee) := ∀ fr (a : lifted.Location), a.label = k.entry →
  Atom.All fnCode a.arguments a.store (k.abi fr ++ k.pre fr) →
  RamWriteFrame fr.original a.store (fr.region :: k.writes fr) →
  Runs a (fun o => o.tag = some ⟨64,fr.ret⟩ ∧
    Atom.All fnCode o.values o.store (abiOut fr ++ k.post fr) ∧
    RamWriteFrame fr.original o.store (fr.region :: k.writes fr))

theorem provedCallee {L : Type} {p : Program (fun _ => _root_.Empty) L (fun _ => 0) 0}
    (e : L) (abi : Lifted.Label → Activation → List Atom)
    (c : LayoutCore p Empty.semantics lifted Unit)
    (param : c.Params e) (empty : c.args e param = #v[])
    (out : c.Result) (_result : c.output out = ⟨#v[],none,()⟩)
    (unique : ∀ (r : c.Result), r=out)
    (blocks : ∀ l, (Layout.withFrame abi abiOut c).BlockSimulation fnCode l)
    (run : p.Exec Empty.semantics ⟨unitLoc e,[]⟩ ⟨#v[],none,()⟩) :
    Callee.Correct ⟨c.start e,abi (c.start e),fun fr => c.atoms e () fr param,
      fun fr => c.done () fr out,fun fr => c.footprint () fr⟩ := by
  intro fr a hl hat ho
  let lay := Layout.withFrame abi abiOut c
  let ctx := (fr,())
  have start : lay.Rel fnCode ctx (unitLoc e) a :=
    ⟨hl,⟨param,empty.symm,Subsingleton.elim _ _,hat⟩,ho⟩
  obtain ⟨o,er,tag,⟨r,_,done⟩,f⟩ :=
    (lay.simulation fnCode ctx blocks).exec run.sem (show lay.StateRel fnCode ctx ⟨unitLoc e,[]⟩ ⟨a,[]⟩ from
      ⟨ctx,start,rfl⟩)
  cases unique r
  exact ⟨o,Program.Exec.of_sem er,tag,done,f⟩

namespace Invoke
inductive Point | site | child | resume

def program : Program (fun _ => _root_.Empty) Point (fun _ => 0) 0 := ⟨fun
  | .site => .terminate (.call ⟨.child,#v[]⟩ ⟨.resume,#v[],rfl,none⟩)
  | _ => .terminate (.ret #v[])⟩

structure Edge where
  site : Lifted.Label
  resume : Lifted.Label
  callee : Callee
  before : Activation → List Atom
  after : Activation → List Atom
  footprint : List MemoryRegion

@[refine_layout] def core (s : Edge) : LayoutCore program Empty.semantics lifted Unit where
  start | .site => s.site | .child => s.callee.entry | .resume => s.resume
  Params := fun _ => Unit
  args := fun _ _ => #v[]
  store := fun _ _ => ()
  atoms l _ fr _ := match l with
    | .site => s.before fr | .child => s.callee.abi fr ++ (s.callee.pre fr ++ [.fact (s.callee.writes fr = s.footprint)])
    | .resume => s.after fr
  Result := Unit
  output := fun _ => ⟨#v[],none,()⟩
  done := fun _ fr _ => s.callee.post fr
  footprint := fun _ _ => s.footprint

abbrev layout (s : Edge) := Layout.withFrame (fun _ _ => []) abiOut (core s)

theorem invoke (s : Edge) (child : s.callee.Correct)
    (proof : (layout s).BlockSimulation fnCode .site) {fr : Activation} {a : lifted.Location}
    (h : (layout s).Rel fnCode (fr,()) (unitLoc .site) a) :
    Forward a ((layout s).Rel fnCode (fr,()) (unitLoc .resume)) := by
  intro _ cont
  apply composeCall (layout s) (ret := ⟨#v[],none,()⟩) (proof _ _ _ _ h) rfl _ cont
  rintro ⟨f,_⟩ b ⟨hl,⟨_,_,_,hat⟩,hf⟩
  change Atom.All fnCode _ _ (s.callee.abi f ++ (s.callee.pre f ++ [.fact _])) at hat
  simp only [Atom.all_append] at hat
  obtain ⟨aa,bb,eq, _⟩ := hat
  change s.callee.writes f = s.footprint at eq
  change RamWriteFrame f.original b.store (f.region :: s.footprint) at hf
  obtain ⟨o,run,tag,done,frame⟩ := child f b hl ((Atom.all_append _ _).2 ⟨aa,bb⟩) (eq ▸ hf)
  refine ⟨o,run,tag,⟨(),rfl,done⟩,?_⟩
  change RamWriteFrame f.original o.store (f.region :: s.footprint)
  rwa [←eq]
end Invoke
end ChaCha20Poly1305.Proofs.Decrypt
