import ChaCha20Poly1305.Proofs.Decrypt.ShortCore

namespace ChaCha20Poly1305.Proofs.Decrypt.Short

open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted

set_option maxRecDepth 14000
set_option maxHeartbeats 1500000
set_option pp.maxSteps 300

theorem allocBlock (e : Env) (hg : Geometry e) :
    (Layout.withFrame frameAt Decrypt.doneAt (core e)).BlockSimulation fnCode .alloc := by
  obtain ⟨n, cap, heap, src, sp⟩ := e
  rcases hg with ⟨⟨hpos, hlen⟩, hf, hn, hl, hsl, hsep, hc, hro, ha, hhs, hrs, hcs, hgs, hgs'⟩
  dsimp only at hpos hlen hf hn hl hsl hsep hc hro ha hhs hrs hcs hgs hgs'
  x86_refine [program]
  all_goals try subst sp
  all_goals try subst src
  all_goals try subst heap
  all_goals try subst n
  all_goals
    exfalso
    have hsum : (fr.r8 + n).toNat = fr.r8.toNat + n.toNat := by
      simp only [BitVec.toNat_add, Nat.mod_eq_of_lt (show fr.r8.toNat + n.toNat < 2^64 by omega)]
    have hno : (addSpec fr.r8 n).2.CF = false := by simp [addSpec, hsum]
    have hlast : (fr.r8 + n).toNat ≤ (limit ⟨n,cap,fr.r8,fr.rcx,fr.rsp⟩).toNat := by
      unfold limit
      dsimp only
      split
      · rw [hsum]; change _ ≤ 18446744073709551615; omega
      · rename_i hcarry
        have hval : (fr.r8 + cap).toNat = fr.r8.toNat + cap.toNat := by
          simpa [addSpec] using hcarry
        rw [hval, hsum]; omega
    first | exact (by assumption : ¬ _ ) hlast | exact Bool.noConfusion (hno.symm.trans (by assumption : _ = true))


end ChaCha20Poly1305.Proofs.Decrypt.Short
