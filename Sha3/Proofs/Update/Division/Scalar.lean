import Sha3.Proofs.Image
import Sha3.Proofs.Run
import X86Proofs.Program.Compose

namespace Sha3.Proofs.Update.Division

open X86 X86.Machine X86.UserProcess X86Proofs Sha3.Spec.Program

theorem advanceScalar [Bindings] {boundary : ReturnBoundary}
    {p : BitVec 64} {bytes : List UInt8} {effect : RamState → Effect}
    {cs : List Component} {model s : RamState} {pre : RamState → Prop}
    (step : StepEffect pre (codeRange p bytes) effect)
    (image : ∀ x ∈ codeRange p bytes, x.1.toNat < Prelude.userAddressLimit ∧
      Extracted.programSections.fetchByte x.1 = some x.2)
    (full : ∀ s, ∀ w ∈ (effect s).writes, w.Full)
    (localWrites : ∀ a b, Obs a b → (effect a).writes = (effect b).writes)
    (frame : ∀ s, ∀ c ∈ (effect s).components, c ∈ cs)
    (nomem : ∀ c ∈ cs, ∀ x, ¬ c.Covers x)
    (next : ∀ t, InProgram (effect t).rip)
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (hb : ¬ InProgram boundary.rip) (ip : pre s) (obs : Obs model s) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      (effect s).Holds s t ∧
      Obs (applyWrites model (effect model).writes) t ∧ AgreesExcept cs s t := by
  have code : CodeIn (codeRange p bytes) s := by
    intro x hx
    exact ⟨(image x hx).1, programLoaded_fetchByte loaded (image x hx).2⟩
  obtain ⟨t, ht, hr, he⟩ := step s ready code ip
  have ha : AgreesExcept cs s t := he.agrees.mono (frame s)
  have hloaded : ProgramLoaded t := by
    unfold ProgramLoaded
    rw [ha.external nomem]
    exact loaded
  refine ⟨t, Advances.of_step ht (.inl (fun heq ↦ hb (heq ▸ (he.rip ▸ next s)))),
    hr, hloaded, he, ?_, ha⟩
  rw [localWrites model s obs]
  exact he.obs obs (full s)

end Sha3.Proofs.Update.Division
