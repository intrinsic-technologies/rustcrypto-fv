import K256.Proofs.Verify.Transfer.Signature.Certificates

namespace K256.Proofs.Verify.Transfer.Signature

open K256.Proofs.CFG K256.Proofs.Lift X86.Machine

theorem transferAt {d : Dialect Op Value Ram} {x : Proofs.LIR.Label} {y : Verify.LIR.Label} (pair : labelPair x y = true)
    {a : Values Value Reg.count} {m : Ram} {out : Output Value Ram Reg.count}
    (run : Proofs.LIR.program.Exec d
      ⟨⟨x, a, m⟩, []⟩ out) :
    ∃ o, Verify.LIR.program.Exec d
        ⟨⟨y, a, m⟩, []⟩ o ∧ o.store = out.store ∧ o.tag = out.tag ∧
      ∀ i : Fin Reg.count, i.val ∈ [0,1,2,3,4,5,6,7,8,9,12,13,14,15,22,39,50,51] →
        o.values[i] = out.values[i] := by
  apply Exists.elim (exec_of_matches Verify.LIR.program d (LocAgree labelPair Proofs.LIR.live)
    (OutAgree Proofs.LIR.retLive) Proofs.LIR.program ?_ run (y := ⟨y,a,m⟩) ?_)
  · rintro b ⟨hr, hmem, htag, hv⟩
    refine ⟨b, hr, hmem.symm, htag.symm, fun i hi => (hv i i ?_).symm⟩
    exact (of_decide_eq_true (by decide +kernel) :
      ∀ j : Fin Reg.count, j.val ∈ [0,1,2,3,4,5,6,7,8,9,12,13,14,15,22,39,50,51] →
        Supports Reg.count 0 Proofs.LIR.retLive j.val j.val = true) i hi
  · rintro ⟨x,a,m⟩ ⟨y,b,u⟩ ⟨hxy, hmem, hv⟩
    change m = u at hmem
    subst u
    change (labelTest x).any _ = true at hxy
    cases ht : labelTest x with
    | none => simp [ht] at hxy
    | some t =>
      rw [ht] at hxy
      obtain rfl := t.sound y hxy
      exact matchedAt x t ht d a b hv m
  · refine ⟨pair, rfl, ?_⟩
    intro i j h
    have : i.val = j.val := by
      simpa [Supports, indexAt, j.isLt] using (Bool.and_eq_true_iff.mp h).1
    exact congrArg (fun k : Fin Reg.count => a[k]) (Fin.ext this)

end K256.Proofs.Verify.Transfer.Signature
