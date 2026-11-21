import ChaCha20Poly1305.Proofs.Decrypt.CallRun

namespace ChaCha20Poly1305.Proofs.Decrypt
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program

@[refine_layout] def Callee.reserve (k : Callee) (extra : List MemoryRegion) : Callee :=
  {k with writes := fun fr => k.writes fr ++ extra}

def Callee.Independent (k : Callee) := ∀ (f : Activation) (m : Ram),
  let g := {f with original := m}
  k.abi g = k.abi f ∧ k.pre g = k.pre f ∧ k.post g = k.post f ∧ k.writes g = k.writes f

theorem Callee.reserveCorrect (k : Callee) (ok : k.Correct) (stable : k.Independent) (extra : List MemoryRegion) :
    (k.reserve extra).Correct := by
  intro fr a label hat hf
  let f := {fr with original := a.store}
  obtain ⟨sa,sp,sq,sw⟩ := stable fr a.store
  have pre : Atom.All fnCode a.arguments a.store (k.abi f ++ k.pre f) := by
    change Atom.All _ _ _ (k.abi fr ++ k.pre fr) at hat
    simpa only [f,sa,sp] using hat
  obtain ⟨o,run,ret,post,frame⟩ := ok f a label pre (.refl _ _)
  refine ⟨o,run,ret,?_,?_⟩
  · change Atom.All _ _ _ (abiOut fr ++ k.post fr)
    change Atom.All _ _ _ (abiOut fr ++ k.post f) at post
    rwa [sq] at post
  · change RamWriteFrame a.store o.store (fr.region :: k.writes f) at frame
    rw [sw] at frame
    apply hf.trans frame
    intro z hz
    refine ⟨z,?_,Nat.le_refl _,Nat.le_refl _⟩
    change z ∈ fr.region :: (k.writes fr ++ extra)
    rcases List.mem_cons.mp hz with rfl|h
    · exact .head _
    · exact .tail _ (List.mem_append_left _ h)

end ChaCha20Poly1305.Proofs.Decrypt
