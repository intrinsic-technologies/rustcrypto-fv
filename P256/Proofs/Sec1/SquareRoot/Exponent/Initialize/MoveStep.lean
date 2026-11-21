import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.Prologue
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false


namespace P256.Proofs.Sec1.SquareRoot.ExponentInitialize

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem frame_move_r64 [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (outside : ¬ InProgram boundary.rip) (hf : Frame s t)
    (offset : Nat) (rex modrm : UInt8) (hrex : RexWPrefix rex.toBitVec)
    (hmod : modrmMod modrm = 3)
    (hreg : gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) ≠ 4)
    (hip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 offset)
    (hbound : offset + 3 < 118431)
    (hcode : Extracted.textBytes.toListFrom offset 3 = [rex, 0x89, modrm]) :
    ∃ u, Advances boundary 1 t u ∧ Frame s u ∧
      u.RIP = Extracted.textAddress + BitVec.ofNat 64 (offset+3) ∧
      (Operand.reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) : Operand 64).read u =
        (Operand.reg (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) : Operand 64).read t ∧
      AgreesExcept [.reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)), .rip] t u ∧
      u.external = t.external := by
  obtain ⟨u, run, ready, effect⟩ :=
    (mov_r64_r64_effect_step (Extracted.textAddress + BitVec.ofNat 64 offset) rex modrm hrex hmod).advances
      (readyToStep hf.machine hf.bindingsSupported)
      (programText_slice (programLoaded_codeIn hf.loaded) offset _ (by simpa using Nat.le_of_lt hbound) hcode)
      hip (by
        have h := boundary_ne_program outside (inProgram_of_textOffset (offset+3) hbound)
        simpa [movR64R64Effect, BitVec.ofNat_add, BitVec.add_assoc] using h)
  have g : AgreesExcept [.reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)), .rip] t u := effect.agrees
  refine ⟨u, run, hf.after_registers ready g (by simp [Component.Covers])
    (by simpa using Ne.symm hreg), ?_, effect.writes, g, g.external (by simp [Component.Covers])⟩
  simpa [movR64R64Effect, BitVec.ofNat_add, BitVec.add_assoc] using effect.rip

end P256.Proofs.Sec1.SquareRoot.ExponentInitialize
