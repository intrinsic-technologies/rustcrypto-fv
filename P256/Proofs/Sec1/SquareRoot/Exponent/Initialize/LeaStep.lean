import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.Prologue
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false


namespace P256.Proofs.Sec1.SquareRoot.ExponentInitialize

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem frame_lea_r64 [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (outside : ¬ InProgram boundary.rip) (hf : Frame s t)
    (codeOffset : Nat) (rex : UInt8) (reg : BitVec 3) (am : AddrMode)
    (hrex : RexWPrefix rex.toBitVec) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (hreg : gprNumber 0 (rexR rex.toBitVec) reg ≠ 4)
    (hip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 codeOffset)
    (hbound : codeOffset + (3 + am.tail.length) < 118431)
    (hcode : Extracted.textBytes.toListFrom codeOffset (3+am.tail.length) =
      rex :: 0x8d :: am.modrm reg :: am.tail) :
    ∃ u, Advances boundary 1 t u ∧ Frame s u ∧
      u.RIP = Extracted.textAddress + BitVec.ofNat 64 (codeOffset+3+am.tail.length) ∧
      (Operand.reg (gprNumber 0 (rexR rex.toBitVec) reg) : Operand 64).read u =
        am.addr t (Extracted.textAddress + BitVec.ofNat 64 (codeOffset+3+am.tail.length)) ∧
      AgreesExcept [.reg (gprNumber 0 (rexR rex.toBitVec) reg), .rip] t u ∧ u.external = t.external := by
  let ip := Extracted.textAddress + BitVec.ofNat 64 codeOffset
  let len := 3+am.tail.length
  have hlen : (rex :: 0x8d :: am.modrm reg :: am.tail).length = len := by
    simp only [List.length_cons, len]
    omega
  have hnext : ip + BitVec.ofNat 64 len =
      Extracted.textAddress + BitVec.ofNat 64 (codeOffset+3+am.tail.length) := by
    simp [ip, len, BitVec.ofNat_add, BitVec.add_assoc]
  obtain ⟨u, run, ready, effect⟩ :=
    (lea_r64_effect_step ip rex hrex reg am hv hx hb).advances
      (readyToStep hf.machine hf.bindingsSupported)
      (programText_slice (programLoaded_codeIn hf.loaded) codeOffset _
        (by rw [hlen]; exact Nat.le_of_lt hbound) (by rw [hlen]; exact hcode))
      hip (by
        rw [show (leaR64Effect ip (gprNumber 0 (rexR rex.toBitVec) reg) am t).rip =
          ip + BitVec.ofNat 64 len from rfl, hnext]
        exact boundary_ne_program outside (inProgram_of_textOffset _ (by omega)))
  have agrees : AgreesExcept [.reg (gprNumber 0 (rexR rex.toBitVec) reg), .rip] t u := effect.agrees
  refine ⟨u, run, hf.after_registers ready agrees (by simp [Component.Covers])
    (by simpa using Ne.symm hreg), ?_, ?_, agrees, agrees.external (by simp [Component.Covers])⟩
  · exact effect.rip.trans hnext
  · have h := effect.writes
    change (Operand.reg (gprNumber 0 (rexR rex.toBitVec) reg) : Operand 64).read u =
      am.addr t (ip+BitVec.ofNat 64 len) at h
    rwa [hnext] at h

end P256.Proofs.Sec1.SquareRoot.ExponentInitialize
