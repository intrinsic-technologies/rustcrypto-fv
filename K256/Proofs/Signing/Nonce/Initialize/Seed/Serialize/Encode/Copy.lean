import K256.Proofs.Signing.Nonce.Initialize.Seed.Serialize.Encode.State
import K256.Proofs.Verify.LIR.Generated.Values
import K256.Proofs.Verify.Hash.Update.Copy

namespace K256.Proofs.Signing.Nonce.Initialize.Encode

open K256.Spec.Program X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR Verify.Core

theorem copyArgumentWidths {a : Registers} {m : Ram} {out : Output Value Ram Reg.count}
    (run : program.Exec (dialect Extracted.programImage) ⟨⟨.l12a820,a,m⟩,[]⟩ out)
    (r9 : a[9].width = 64) : ParseSignature.ArgumentWidths out.values := by
  cases run with
  | done h =>
    change (program.runBlock _ ⟨.l12a820,a,m⟩).next _ [] = .done out at h
    cfg_eval [b_l12a820] at h
    repeat' (split at h)
    all_goals simp only [Transfer.next, Outcome.done.injEq, reduceCtorEq] at h
    all_goals
      subst out
      rintro ⟨i, hi⟩ hm
      simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> first | rfl | exact r9
  | next h _ =>
    change (program.runBlock _ ⟨.l12a820,a,m⟩).next _ [] = .next _ at h
    cfg_eval [b_l12a820] at h
    repeat' (split at h)
    all_goals simp only [Transfer.next, reduceCtorEq] at h

end K256.Proofs.Signing.Nonce.Initialize.Encode
