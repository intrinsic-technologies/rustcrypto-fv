import ChaCha20Poly1305.Proofs.Decrypt.Prefix

namespace ChaCha20Poly1305.Proofs.Decrypt.Prefix

open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted
open ChaCha20Poly1305.Proofs.Decrypt.Short hiding core

set_option maxRecDepth 14000
set_option maxHeartbeats 1500000
set_option pp.maxSteps 300

theorem shimBlock (e : Env) (x : Inputs e) (hg : Geometry e (2^32)) :
    (Layout.withFrame frameAt Decrypt.doneAt (core e x)).BlockSimulation fnCode .shim := by
  obtain ⟨n, cap, heap, src, sp⟩ := e
  obtain ⟨key,ct,ss,sa⟩ := x
  dsimp only at ss sa
  rcases hg with ⟨⟨hpos, hlen⟩, hf, hn, hl, hsl, hsep, hc, hro, ha, hhs, hrs, hcs, hgs, hgs'⟩
  dsimp only at hpos hlen hf hn hl hsl hsep hc hro ha hhs hrs hcs hgs hgs'
  x86_refine [Short.program]
  all_goals try subst sp
  all_goals try subst src
  all_goals try subst heap
  all_goals try subst n
  all_goals try assumption
  rw [atom19]
  exact BitVec.eq_of_zero_length rfl


end ChaCha20Poly1305.Proofs.Decrypt.Prefix
