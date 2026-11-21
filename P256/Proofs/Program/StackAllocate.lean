import P256.Proofs.Program.Code
import X86Proofs.Instructions.Sub.Generated.Imm32.Triple

set_option autoImplicit false

namespace P256.Proofs.Program

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs

theorem stack_allocate32 [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (offset : Nat) (amount : BitVec 32)
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (outside : ¬ InProgram boundary.rip)
    (rip : s.RIP = Extracted.textAddress + BitVec.ofNat 64 offset)
    (bound : offset + 7 < 118431)
    (bytes : Extracted.textBytes.toListFrom offset 7 =
      [0x48, 0x81, 0xec] ++ immBytes 32 amount) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = Extracted.textAddress + BitVec.ofNat 64 (offset + 7) ∧
      stackPtr t = stackPtr s - amount.signExtend 64 ∧ t.external = s.external ∧
      AgreesExcept [.reg 4, .flags, .rip] s t := by
  have length : ([0x48, 0x81, 0xec] ++ immBytes 32 amount).length = 7 := by
    simp [immBytes]
  obtain ⟨t, step, readyT, effect⟩ :=
    sub_r64_imm32_effect_step _ 0x48 0xec amount
      (by simp [RexWPrefix]) rfl rfl s ready
      (programText_slice (programLoaded_codeIn loaded) offset
        ([0x48, 0x81, 0xec] ++ immBytes 32 amount) (by rw [length]; omega)
        (by rw [length]; exact bytes)) rip
  have ripT : t.RIP = Extracted.textAddress + BitVec.ofNat 64 (offset + 7) := by
    rw [effect.rip]
    change (Extracted.textAddress + BitVec.ofNat 64 offset) + 7 = _
    rw [BitVec.ofNat_add, BitVec.add_assoc]
    rfl
  have memory : t.external = s.external := effect.agrees.external
    (by simp [subR64Imm32Effect_components, Component.Covers])
  refine ⟨t, Advances.of_step step (.inl ?_), readyT, ?_, ripT, effect.writes,
    memory, effect.agrees⟩
  · rw [ripT]
    exact boundary_ne_program outside (inProgram_of_textOffset _ bound)
  · intro a b hb
    rw [memory]
    exact loaded a b hb

end P256.Proofs.Program
