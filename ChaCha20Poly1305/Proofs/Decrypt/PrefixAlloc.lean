import ChaCha20Poly1305.Proofs.Decrypt.Prefix

namespace ChaCha20Poly1305.Proofs.Decrypt.Prefix

open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted
open ChaCha20Poly1305.Proofs.Decrypt.Short hiding core

set_option maxRecDepth 14000
set_option maxHeartbeats 1500000
set_option pp.maxSteps 300

theorem allocBlock (e : Env) (x : Inputs e) (hg : Geometry e (2^32)) :
    (Layout.withFrame frameAt Decrypt.doneAt (core e x)).BlockSimulation fnCode .alloc := by
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
  all_goals try
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

  · simp (discharger := (apply RangeApart.of_toNat <;> bv_omega)) only [memLoad_memStore_of_rangeApart]
    apply Eq.trans (hframe.memLoad_eq ?_) atom52
    simp only [Outside,List.mem_cons,List.not_mem_nil,or_false, forall_eq_or_imp, forall_eq,
      Nat.mul_div_cancel_left _ (by decide : 0 < 8)]
    omega
  · rw [show fr.rsp - 72 = fr.rsp - 80 + 8 by bv_omega]; exact atom48
  · rw [show fr.rsp - 64 = fr.rsp - 80 + 16 by bv_omega]; exact atom49
  · rw [show fr.rsp - 56 = fr.rsp - 80 + 24 by bv_omega]; exact atom50
  · simpa only [BitVec.setWidth_eq] using done14

end ChaCha20Poly1305.Proofs.Decrypt.Prefix
