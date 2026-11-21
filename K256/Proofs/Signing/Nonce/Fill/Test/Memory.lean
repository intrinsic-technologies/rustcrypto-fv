import K256.Proofs.Signing.Nonce.Fill.Memory

namespace K256.Proofs.Signing.Nonce.Fill

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Verify.LIR
open Verify.Core (Registers)
open UpdateV.Finalize (outsideOffset)

abbrev testScratch (fr : Activation) : List MemoryRegion :=
  [⟨(sp fr - 8).toNat,48⟩, ⟨(sp fr + 72).toNat,32⟩, ⟨(sp fr + 152).toNat,8⟩]

theorem testScratch_sub {fr : Activation} (env : Environment fr) :
    RegionsWithin (testScratch fr) (regions fr) := by
  intro r hr
  have := env.depth
  have d := env.subNat 2160 (by decide)
  have a := env.pushNat
  have b := env.slotNat 72 (by decide)
  have c := env.slotNat 152 (by decide)
  simp only [testScratch,List.mem_cons,List.not_mem_nil,or_false] at hr
  refine ⟨fr.region, by simp only [regions,List.mem_cons,true_or], ?_⟩
  rcases hr with rfl|rfl|rfl <;>
    simp only [Activation.region,env.low,d,a,b,c,BitVec.reduceToNat] <;> omega

theorem testScratch_outside {fr : Activation} (env : Environment fr) {p : BitVec 64} {n : Nat}
    (bound : p.toNat + n ≤ 2^64)
    (h : fr.rsp.toNat - 192 ≤ p.toNat ∧ p.toNat + n ≤ fr.rsp.toNat - 160 ∨
         fr.rsp.toNat - 128 ≤ p.toNat ∧ p.toNat + n ≤ fr.rsp.toNat - 80 ∨
         fr.rsp.toNat - 72 ≤ p.toNat) : Outside (testScratch fr) p n := by
  have := env.depth
  have a := env.pushNat
  have b := env.slotNat 72 (by decide)
  have c := env.slotNat 152 (by decide)
  refine ⟨bound, fun r hr => ?_⟩
  simp only [testScratch,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl <;> simp only [a,b,c,BitVec.reduceToNat] <;> omega

theorem testStateOutside {fr : Activation} (env : Environment fr) :
    Outside (testScratch fr) (fr.rdi + 8) 64 := by
  have lim := env.limit
  rw [show fr.rdi + 8 = fr.rsp + 704 by rw [env.gen]; bv_omega]
  apply testScratch_outside env <;> rw [env.addNat 704 (by decide)] <;> simp only [BitVec.reduceToNat] <;> omega

theorem Frame.testStores {fr : Activation} {a b : Registers} {m n : Ram} (env : Environment fr)
    (frame : Frame fr a m) (writes : RamWriteFrame m n (testScratch fr))
    (keep : ∀ i : Fin Reg.count, i.val ∈ [4,22,39,50,51] → b[i] = a[i])
    (widths : ∀ i : Fin Reg.count, i.val ∈ Activation.entryNumbers → b[i].width = 64) : Frame fr b n := by
  refine frame.afterCall env writes (testScratch_sub env) ?_
    ((keep 4 (by decide)).trans frame.atoms.1) (fun i hi => keep i (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
      rcases hi with h|h|h|h <;> simp only [h] <;> decide)) widths
  intro k w hk
  apply writes.memLoad_eq
  have depth := env.depth
  have limit := env.limit
  have addr (hk : k.toNat ≤ 2160) := env.subNat k hk
  apply testScratch_outside env
  all_goals rcases hk with ⟨rfl,h⟩|⟨rfl,rfl⟩
  all_goals first
    | simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rw [addr (by omega)]
      omega
    | rw [env.subNat 176 (by decide)]
      simp only [BitVec.reduceToNat]
      omega

end K256.Proofs.Signing.Nonce.Fill
