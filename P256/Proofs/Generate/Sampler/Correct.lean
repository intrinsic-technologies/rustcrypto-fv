import P256.Proofs.Generate.Sampler.Loop
import P256.Proofs.Generate.Sampler.Finish.Correct

set_option autoImplicit false

namespace P256.Proofs.Generate.Sampler

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs
open Program SecretKeyFromBytes.Scalar

theorem sampler_correct (bindings : Bindings) : Contract bindings := by
  intro s boundary input d pre accepted
  have trace := draw_some_iff_trace.mp accepted
  obtain ⟨a,⟨na,ha⟩,sa⟩ := entry_correct pre
  obtain ⟨b,⟨nb,hb⟩,sb⟩ := first_read pre sa trace.available
  obtain ⟨c,⟨nc,hc⟩,sc,rip,scalar,pointer⟩ := trace_finish pre trace sb
  exact Finish.finish pre sc rip scalar pointer ⟨_,(ha.trans hb).trans hc⟩

end P256.Proofs.Generate.Sampler
