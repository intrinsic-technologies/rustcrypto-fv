import ChaCha20Poly1305.Proofs.Decrypt.Invoke

namespace ChaCha20Poly1305.Proofs.Decrypt.Invoke
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program

theorem run (s : Edge) (ok : s.callee.Correct) (proof : (layout s).BlockSimulation fnCode .site)
    (fr : Activation) (a : lifted.Location)
    (entry : a.label = s.site) (pre : Atom.All fnCode a.arguments a.store (s.before fr))
    (orig : fr.original = a.store) :
    Forward a (fun b => b.label = s.resume ∧ Atom.All fnCode b.arguments b.store (s.after fr) ∧
      RamWriteFrame a.store b.store (fr.region :: s.footprint)) := by
  have h : (layout s).Rel fnCode (fr,()) (unitLoc .site) a := by
    refine ⟨entry,⟨(),rfl,rfl,?_⟩,orig ▸ RamWriteFrame.refl _ _⟩
    exact pre
  apply (invoke s ok proof h).bind
  intro b hb
  obtain ⟨bl,⟨_,_,_,out⟩,hf⟩ := hb
  apply Forward.here
  exact ⟨bl,out,orig ▸ hf⟩

end ChaCha20Poly1305.Proofs.Decrypt.Invoke
