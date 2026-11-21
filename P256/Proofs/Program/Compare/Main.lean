import P256.Proofs.Program.Compare.Call

namespace P256.Proofs.Program.Compare

open X86 X86.Machine X86.UserProcess X86Proofs

theorem correct [Bindings] : Correct := by
  intro boundary initial hp hb
  obtain ⟨n, s, ha, hs⟩ := prepare_body boundary initial hp hb
  rcases hs with hs | hs
  · obtain ⟨m, t, hat, ht⟩ := finish hp hb hs
    exact ⟨n + m, t, ha.trans hat, ht⟩
  · obtain ⟨m, body, hab, hbdy⟩ := body_tail hp hb hs
    obtain ⟨k, t, hat, ht⟩ := finish hp hb hbdy
    exact ⟨n + m + k, t, (ha.trans hab).trans hat, ht⟩

end P256.Proofs.Program.Compare
