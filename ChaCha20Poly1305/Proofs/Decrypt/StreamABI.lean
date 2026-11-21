import ChaCha20Poly1305.Proofs.Decrypt.StreamBody
import ChaCha20Poly1305.Proofs.Decrypt.StreamEntry
import ChaCha20Poly1305.Proofs.Decrypt.StreamBounds
import ChaCha20Poly1305.Proofs.Decrypt.StreamUsed
import ChaCha20Poly1305.Proofs.Decrypt.Invoke
import ChaCha20Poly1305.Proofs.Decrypt.Copy

namespace ChaCha20Poly1305.Proofs.Decrypt.Stream
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program
open Control

@[refine_layout] def retCore : LayoutCore Copy.program Empty.semantics lifted Unit where
  start := fun _ => .l1014a8
  Params := fun _ => Unit
  args := fun _ _ => #v[]
  store := fun _ _ => ()
  atoms := fun _ _ _ _ => []
  Result := Unit
  output := fun _ => ⟨#v[],none,()⟩
  done := fun _ _ _ => [.gpr 0 0]
  footprint := fun _ _ => []

theorem finishOK : (Layout.withFrame Fn100a80.active Fn100a80.doneAt retCore).BlockSimulation fnCode () := by
  x86_refine [Copy.program]

abbrev front (x : Input) := Layout.withFrame Fn100a80.active Fn100a80.doneAt (core x)

theorem prologue (x : Input) (small : x.w[12].toBitVec.toNat ≤ 1) {fr a}
    (h : (front x).Rel fnCode (fr,()) (unitLoc .entry) a) :
    Ahead lifted fnCode ((front x).Rel fnCode (fr,()) (unitLoc .base)) a := by
  apply aheadBind (segment (front x) (j := .bounds) (entryBlock x) rfl h); intro _ h
  apply aheadBind (segment (front x) (j := .used) (boundsBlock x small) rfl h); intro _ h
  exact segment (front x) (j := .base) (usedBlock x) rfl h

@[refine_layout] def work (fr : Activation) := {fr with rsp := fr.rsp-416}
@[refine_layout] def snap (fr : Activation) (m : Ram) := {fr with low := fr.rsp-416,original := m}

def Base (x : Input) (fr : Activation) (a : lifted.Location) :=
  Atom.All fnCode a.arguments a.store ((front x).atoms .base (fr,()) ())

set_option maxHeartbeats 400000
set_option maxRecDepth 6000
set_option pp.maxSteps 120
theorem baseInputs (x : Input) (fr : Activation) (a : lifted.Location) (base : Base x fr a) :
    Scope x (work fr) a.store ∧ Atom.All fnCode a.arguments a.store (spillStep x (work fr) false).pre ∧
      Atom.All fnCode a.arguments a.store (state x fr.rdi) := by
  unfold Base at base
  unpack_atoms base []
  have sp : (fr.rsp-416).toNat = fr.rsp.toNat-416 := by bv_omega
  constructor
  · constructor
    all_goals try simp only [work]
    all_goals first | assumption | (apply Writable.sub (h := ‹Writable _ _ (fr.rsp-416) 416›) <;> omega) | omega
  constructor
  · join_atoms []
    all_goals first | assumption | (apply Writable.sub (h := ‹Writable _ _ (fr.rsp-416) 416›) <;> omega) | omega | rfl
  · join_atoms []
    all_goals assumption

theorem baseOut (x : Input) (fr : Activation) (a b : lifted.Location) (base : Base x fr a)
    (regs : Atom.All fnCode b.arguments b.store (Full.registers (work fr)))
    (f : RamWriteFrame a.store b.store (bodyFrame x (work fr))) :
    Atom.All fnCode b.arguments b.store (Fn100a80.active .l1014a8 fr) := by
  unfold Base at base
  unpack_atoms base []
  unpack_atoms regs []
  simp only [bodyFrame,work] at f
  join_atoms []
  all_goals assumption

theorem execEnd (fr : Activation) (b : lifted.Location) (hl : b.label = .l1014a8)
    (hat : Atom.All fnCode b.arguments b.store (Fn100a80.active .l1014a8 fr)) (orig : fr.original=b.store) :
    Runs b (fun o => o.tag = some ⟨64,fr.ret⟩ ∧ Atom.All fnCode o.values o.store (abiOut fr ++ [.gpr 0 0]) ∧
      RamWriteFrame fr.original o.store [fr.region]) := by
  let lay := Layout.withFrame Fn100a80.active Fn100a80.doneAt retCore
  have h : lay.Rel fnCode (fr,()) (unitLoc ()) b := ⟨hl,⟨(),rfl,rfl,by simpa only [lay,Layout.withFrame,retCore,List.append_nil] using hat⟩,by
    exact orig ▸ RamWriteFrame.refl _ _⟩
  obtain ⟨o,run,tag,⟨_,_,done⟩,f⟩ := composeReturn lay (finishOK _ _ _ _ h)
  exact ⟨o,run,tag,done,f⟩

end ChaCha20Poly1305.Proofs.Decrypt.Stream
