import ChaCha20Poly1305.Proofs.Decrypt.ShortCore

namespace ChaCha20Poly1305.Proofs.Decrypt.Short

open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted

set_option maxRecDepth 14000
set_option maxHeartbeats 1500000
set_option pp.maxSteps 300

theorem entryBlock (e : Env) (hg : Geometry e) :
    (Layout.withFrame frameAt Decrypt.doneAt (core e)).BlockSimulation fnCode .entry := by
  obtain ⟨n, cap, heap, src, sp⟩ := e
  rcases hg with ⟨⟨hpos, hlen⟩, hf, hn, hl, hsl, hsep, hc, hro, ha, hhs, hrs, hcs, hgs, hgs'⟩
  dsimp only at hpos hlen hf hn hl hsl hsep hc hro ha hhs hrs hcs hgs hgs'
  x86_refine [program]
  all_goals try subst sp
  all_goals try subst src
  all_goals try subst heap
  all_goals try subst n
  all_goals try assumption
  unfold limit
  dsimp only
  cases (addSpec fr.r8 cap).2.CF <;> rfl


end ChaCha20Poly1305.Proofs.Decrypt.Short
