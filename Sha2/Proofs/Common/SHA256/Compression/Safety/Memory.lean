import Sha2.Proofs.Common.SHA256.Compression.Safety.Effects

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Compression.Safety

open Sha2.Spec Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs

theorem saved_load_store {initial model : RamState} {before : Position}
    (state : State initial model before) (saved : before.saved = true)
    {n : Nat} (off : Nat) (value : BitVec n) (width : n ≤ 128)
    (apart : OffsetsApart (BitVec.ofNat 64 off) (n / 8) 24 8) :
    memLoad (memStore model.external (stackPtr initial + BitVec.ofNat 64 off) value)
      (stackPtr initial + 24) 64 = initial.regValue .rsi := by
  rw [memLoad_memStore_apart _ _ _ _ _ _ apart width (by decide)]
  exact state.saved saved

variable [Bindings]

theorem StepCertificate.of_memory {initial : RamState} {hash : Array UInt32} {block : ByteArray}
    (pre : BlockPre initial hash block) {instruction : CheckedInstruction} {before after : Position}
    (n off : Nat)
    (access : ∀ model, State initial model before → instruction.access initial model)
    (rip : ∀ model, (instruction.effect model).rip = after.rip)
    (inside : InProgram after.rip)
    (bound : off + n / 8 ≤ 192 ∨ 208 ≤ off ∧ off + n / 8 ≤ 288)
    (output : ∀ model, State initial model before → ∃ value : BitVec n,
      (instruction.effect model).writes = [⟨.mem (stackPtr initial + BitVec.ofNat 64 off), value⟩] ∧
      (after.saved = true →
        memLoad (memStore model.external (stackPtr initial + BitVec.ofNat 64 off) value)
          (stackPtr initial + 24) 64 = initial.regValue .rsi))
    (pointers : ∀ r ∈ after.pointers, r ∈ before.pointers) :
    StepCertificate initial instruction before after := by
  have footprint : ∀ model, State initial model before →
      Footprint initial (instruction.effect model).components := by
    intro model state
    obtain ⟨value, writes, _⟩ := output model state
    apply Footprint.effect
    rw [writes]
    exact Footprint.memoryRange initial off (n / 8) bound
  refine ⟨access, ?_, ?_, ?_, footprint⟩
  · intro model state
    exact Footprint.avoids pre _ (footprint model state)
  · intro model _
    rw [rip model]
    exact inside
  · intro model state
    obtain ⟨value, writes, saved⟩ := output model state
    exact next_memory instruction state _ value writes (rip model) saved pointers

end Sha2.Proofs.Common.SHA256.Compression.Safety
