import P256.Proofs.SHA256.Compression.Safety.Effects

set_option autoImplicit false

namespace P256.Proofs.SHA256.Compression.Safety

open P256.Proofs.Common.SHA256.Compression

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [Bindings]

theorem StepCertificate.of_register {initial : RamState} {hash : Array UInt32} {block : ByteArray}
    (pre : BlockPre initial hash block) {instruction : CheckedInstruction} {before after : Position}
    (dst : BitVec 5)
    (access : ∀ model, State initial model before → instruction.access initial model)
    (rip : ∀ model, (instruction.effect model).rip = after.rip)
    (inside : InProgram after.rip)
    (allowed : Component.reg dst ∈ blockComponents initial)
    (rsp : dst ≠ 4)
    (saved : after.saved = true → before.saved = true)
    (output : ∀ model, State initial model before → ∃ value : BitVec 64,
      (instruction.effect model).writes = [⟨.reg dst, value⟩] ∧
      ∀ r ∈ after.pointers,
      (dst = r ∧ value = initial.regValue .rsi) ∨ (dst ≠ r ∧ r ∈ before.pointers)) :
    StepCertificate initial instruction before after := by
  have footprint : ∀ model, State initial model before →
      Footprint initial (instruction.effect model).components := by
    intro model state
    obtain ⟨value, writes, _⟩ := output model state
    apply Footprint.effect
    rw [writes]
    exact Footprint.register initial dst allowed
  refine ⟨access, ?_, ?_, ?_, footprint⟩
  · intro model state
    exact Footprint.avoids pre _ (footprint model state)
  · intro model _
    rw [rip model]
    exact inside
  · intro model state
    obtain ⟨value, writes, pointers⟩ := output model state
    exact next_register instruction state dst value writes (rip model) rsp saved pointers

omit [Bindings] in
theorem text_inside (offset : Nat) (bound : offset < 118431) :
    InProgram (0x100000 + BitVec.ofNat 64 offset) :=
  P256.Proofs.Program.inProgram_of_textOffset offset bound

end P256.Proofs.SHA256.Compression.Safety
