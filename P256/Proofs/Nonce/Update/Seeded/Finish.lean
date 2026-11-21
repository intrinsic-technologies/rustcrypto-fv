import P256.Proofs.Nonce.Update.Seeded.Finish.Copy
import P256.Proofs.Nonce.Update.Seeded.Finish.PrepareHash
import P256.Proofs.Nonce.Update.Seeded.Finish.Save
import P256.Proofs.Nonce.Update.Seeded.Finish.Hash
import P256.Proofs.Nonce.Update.Finish.Value

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Seeded

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem finish [Bindings]
    {initial s : RamState} {boundary : ReturnBoundary}
    {original state : State} {secret reduced : ByteArray}
    (pre : UpdateSeededPre initial boundary original secret reduced)
    (absorbed : Absorbed initial s state (secret ++ reduced)) :
    ∃ fuel t, Advances boundary fuel s t ∧ Finished initial t (updateRound 1 (secret ++ reduced) state) := by
  obtain ⟨_, u, setupRun, copyReady⟩ := Finish.setup_copy pre.toDrbgCalleePre absorbed
  obtain ⟨_, v, copyRun, copied⟩ := Finish.copy_hmac pre.toDrbgCalleePre copyReady
  obtain ⟨_, w, prepareRun, hashReady⟩ := Finish.prepare_hash pre.toDrbgCalleePre copied
  have size : (state.value ++ ⟨#[1]⟩ ++ (secret ++ reduced)).size = 97 := by
    simp only [ByteArray.size_append]
    rw [hashReady.drbg.value_size, pre.secretSize, pre.reducedSize]
    rfl
  obtain ⟨_, x, hashRun, hashed⟩ := Finish.hash pre.toDrbgCalleePre hashReady size
  obtain ⟨_, y, saveRun, valueReady⟩ := Finish.Save.store pre.toDrbgCalleePre hashed
  obtain ⟨t, result⟩ := Update.Finish.value_call pre.toDrbgCalleePre valueReady.toFrameState
    (by decide) (by decide) (by decide) 0xa8dc 0x1f
    (by decide) (by decide +kernel) (by decide +kernel) valueReady.rip
    valueReady.drbgPointer valueReady.drbg
  obtain ⟨fuel, valueRun⟩ := result.execution
  exact ⟨_, t, ((((setupRun.trans copyRun).trans prepareRun).trans hashRun).trans saveRun).trans valueRun,
    result.toFrameState, result.rip, result.drbg⟩

end P256.Proofs.Nonce.Update.Seeded
