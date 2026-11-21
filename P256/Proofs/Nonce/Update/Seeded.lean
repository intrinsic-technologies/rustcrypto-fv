import P256.Proofs.Nonce.Update.Seeded.Branch
import P256.Proofs.Nonce.Update.Seeded.Prepare
import P256.Proofs.Nonce.Update.Seeded.Absorb
import P256.Proofs.Nonce.Update.Seeded.Finish

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem seeded [Bindings]
    {initial s : RamState} {boundary : ReturnBoundary}
    {state : State} {secret reduced : ByteArray}
    (pre : UpdateSeededPre initial boundary state secret reduced)
    (zero : RoundZeroDone initial s state (.seeded secret reduced)) :
    ∃ fuel t, Advances boundary fuel s t ∧
      Finished initial t (updateState true (secret ++ reduced) state) := by
  obtain ⟨u, enterRun, entered⟩ := Seeded.enter pre zero
  obtain ⟨_, v, prepareRun, prepared⟩ := Seeded.prepare pre entered
  obtain ⟨_, w, absorbRun, absorbed⟩ := Seeded.absorb pre prepared
  obtain ⟨_, t, finishRun, finished⟩ := Seeded.finish pre absorbed
  exact ⟨_, t, ((enterRun.trans prepareRun).trans absorbRun).trans finishRun, finished⟩

end P256.Proofs.Nonce.Update
