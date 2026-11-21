import ChaCha20Poly1305.Proofs.Decrypt.Prefix

namespace ChaCha20Poly1305.Proofs.Decrypt.Prefix

open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted
open ChaCha20Poly1305.Proofs.Decrypt.Short hiding core

set_option maxRecDepth 14000
set_option maxHeartbeats 1500000
set_option pp.maxSteps 9000

theorem copyBlock (e : Env) (x : Inputs e) (hg : Geometry e (2^32)) :
    (Layout.withFrame frameAt Decrypt.doneAt (core e x)).BlockSimulation fnCode .copy := by
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
  all_goals
    have hsp : fr.rsp.toNat = sp.toNat - 144 := by rw [atom29]; bv_omega
    obtain ⟨g1, g2, g3, frame, copied, read, ret⟩ := Copy.segments (fr := fr) (m := mem)
      ⟨atom22, atom24, hsep⟩ (by omega) (by omega) atom11 atom13
    try simp only [cmpSpec_CF, decide_eq_true_eq, ← setWidth_sub _ _ (show 32 ≤ 64 by decide)]
    try simp only [← atom29]
  · exact ret
  · apply Eq.trans _ atom20
    apply frame.memLoad_eq
    simp only [Outside, Copy.region, List.mem_singleton, forall_eq]
    change 3145728 + 8 ≤ 2^64 ∧ (3145728 + 8 ≤ fr.rdi.toNat ∨ _ ≤ 3145728)
    omega
  · apply Eq.trans _ atom21
    apply frame.memLoad_eq
    simp only [Outside, Copy.region, List.mem_singleton, forall_eq]
    change 3145736 + 8 ≤ 2^64 ∧ (3145736 + 8 ≤ fr.rdi.toNat ∨ _ ≤ 3145736)
    omega
  · rw [← atom31]
    rw [BitVec.setWidth_eq]
    exact copied.trans atom32
  · apply hframe.trans frame
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact ⟨_, .tail _ (.head _), Nat.le_refl _, Nat.le_refl _⟩
  · exact Or.inr g1
  · exact Or.inr g2
  · exact Or.inr g3
  · exact read
  · exact (congrArg BitVec.toNat ret) ▸ atom14


end ChaCha20Poly1305.Proofs.Decrypt.Prefix
