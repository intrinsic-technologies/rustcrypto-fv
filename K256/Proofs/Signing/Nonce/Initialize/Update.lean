import K256.Proofs.Signing.Nonce.Initialize.Update.Prepare
import K256.Proofs.Signing.Nonce.Initialize.Update.Absorb
import K256.Proofs.Signing.Nonce.Initialize.Update.FinishRound
import K256.Proofs.Signing.Nonce.Initialize.Update.Return

namespace K256.Proofs.Signing.Nonce.Initialize

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters Standards.NIST.SHA2

open Update

private theorem round {fr : Activation} {input : Input} {state : State}
    {a : Verify.Core.Registers} {m : Ram} (second : Bool) (env : Environment fr input)
    (ok : second = true → seeded input = true)
    (live : Live (start second) fr a m state) (slots : second = true → Slots fr m) :
    ∃ b n, Verify.Core.Reaches (start second) a m (resume second input) b n ∧
      Live (resume second input) fr b n (Drbg.updateRound (tag second) (seed input) state) ∧
      ((!second && seeded input) = true → Slots fr n) := by
  obtain ⟨b, n, ctxRun, ctxLive, saved, buf, ctx⟩ := prepare second env ok live slots
  obtain ⟨c, t, absorbRun, absorbLive, saved', msg⟩ := absorb second env ok ctxLive saved buf ctx
  obtain ⟨e, u, endRun, result⟩ := finishRound second env ok absorbLive saved' msg
  exact ⟨e, u, ctxRun.trans (absorbRun.trans endRun), result⟩

theorem update {fr : Activation} {a : Verify.Core.Registers} {input : Input} {state : State}
    (entry : Atom.All Extracted.programImage a fr.original (Fn103f30.frameAt .l103f30 fr))
    (image : ∀ b ∈ Extracted.programImage, fr.original[b.1]? = some b.2)
    (depth : 1920 ≤ fr.rsp.toNat) (low : fr.low = fr.rsp - 1920)
    (limit : fr.rsp.toNat + 8 < 2^32) (dataLow : fr.rdi.toNat + 64 < 2^32)
    (apart : fr.rdi.toNat + 64 ≤ fr.low.toNat ∨ fr.rsp.toNat + 8 ≤ fr.rdi.toNat)
    (writable : Writable Extracted.programImage fr.original fr.rdi 64)
    (slices : input.At fr) (bytes : StateAt fr.original fr.rdi state) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l103f30, a, fr.original⟩, []⟩ out ∧
      out.tag = some ⟨64,fr.ret⟩ ∧ Atom.All Extracted.programImage out.values out.store (Fn103f30.doneAt fr) ∧
      ParseSignature.ArgumentWidths out.values ∧
      RamWriteFrame fr.original out.store [fr.region, ⟨fr.rdi.toNat,64⟩] ∧
      StateAt out.store fr.rdi (input.apply state) := by
  have stack : Writable Extracted.programImage fr.original (fr.rsp - 1920) 1920 := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, w, _⟩ := entry
    exact w
  let env : Environment fr input := ⟨image, depth, low, limit, dataLow, apart, writable, slices, stack⟩
  have live : Live (start false) fr a fr.original state := by
    refine ⟨entry, RamWriteFrame.refl _ _, bytes, ?_, ?_⟩
    · intro impossible
      cases impossible
    · have atoms := entry
      simp only [Fn103f30.frameAt, Fn103f30.frameAtG4, Atom.All, Atom.Holds] at atoms
      obtain ⟨_, _, _, _, h3, h5, _, _, _, _, h12, h13, h14, h15, _⟩ := atoms
      intro ⟨i, bound⟩ hi
      simp only [Activation.calleeSavedNumbers, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | exact congrArg Value.width h3 | exact congrArg Value.width h5 |
          exact congrArg Value.width h12 | exact congrArg Value.width h13 |
          exact congrArg Value.width h14 | exact congrArg Value.width h15
  obtain ⟨b, m, first, ready, saved⟩ := round false env (by simp) live (by simp)
  cases input with
  | empty =>
    obtain ⟨out, ret, post⟩ := returnPath env ready
    exact ⟨out, Program.Exec.of_sem (first.exec ret.sem), post⟩
  | seeded secret reduced =>
    obtain ⟨c, n, second, result, _⟩ := round true env (fun _ => rfl) ready (fun _ => saved rfl)
    obtain ⟨out, ret, post⟩ := returnPath env result
    exact ⟨out, Program.Exec.of_sem ((first.trans second).exec ret.sem), post⟩

end K256.Proofs.Signing.Nonce.Initialize
