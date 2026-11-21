import P256.Proofs.Sec1.Affine.Compressed.Finish.RelocateSetup
import P256.Proofs.Sec1.Affine.Compressed.Finish.Copy
import P256.Proofs.Sec1.Representation
import P256.Proofs.Common.Memory.LoadByte

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Compressed.Finish

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem relocate [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    {point : Option Standards.SECG.ECC.Curve.Point}
    (pre : AffineDecodePre s boundary bytes) (state : Frame s t)
    (rip : t.RIP = 0x110128) (source : t.regValue .r15 = stackPtr s - 592)
    (decoded : AffineResultAt t (stackPtr s - 592) point) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x110144 ∧
      AffineResultAt u (stackPtr s - 744) point ∧
      u.regValue .rdx = stackPtr s - 744 ∧
      u.regValue .r14 = BitVec.ofNat 64 point.isSome.toNat ∧
      u.regValue .rbx = t.regValue .rbx := by
  have readable := ScalarFrame.stack_readable pre.toCalleePre state
    (offset := 240) (len := 1) (by decide) (by decide)
  obtain ⟨n, a, runA, readyA, _, effect⟩ := relocate_setup boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x10128 relocateBytes
      (by decide) (by decide +kernel)) ⟨rip, readable⟩
  have agreesA : AgreesExcept [.reg 14, .reg 2, .reg 1, .reg 7, .reg 6, .rip] t a := effect.agrees
  have frameA := state.after_registers readyA agreesA (by simp [Component.Covers]) (by simp)
  have writes := effect.writes
  change a.regValue .r14 = (memLoad t.external (stackPtr t + 240) 8).setWidth 64 ∧
    a.regValue .rdx = stackPtr t + 16 ∧ a.regValue .rcx = 10 ∧
    a.regValue .rdi = stackPtr t + 16 ∧ a.regValue .rsi = t.regValue .r15 at writes
  have destination : stackPtr t + 16 = stackPtr s - 744 := by
    rw [state.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  obtain ⟨u, runU, frameU, ripU, agreesU, copied⟩ := stack_copy pre frameA
    (count := 10) (source := 592) (destination := 744) (codeOffset := 0x10141)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide +kernel) effect.rip (writes.2.2.2.2.trans source)
    (writes.2.2.2.1.trans destination) writes.2.2.1
  refine ⟨n + 10, u, runA.trans runU, frameU, ripU, ?_, ?_, ?_, ?_⟩
  · apply decoded.of_bytes_eq
    intro i hi
    simpa only [BitVec.ofNat_eq_ofNat, agreesA.external (by simp [Component.Covers])]
      using copied i (by omega)
  · exact (agreesU.read (n := 64) (r := 2) (by simp [copyComponents])).trans
      (writes.2.1.trans destination)
  · have address : stackPtr t + 240 = stackPtr s - 592 + 72 := by
      rw [state.rsp]
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
      rfl
    have value : (memLoad t.external (stackPtr t + 240) 8).setWidth 64 =
        BitVec.ofNat 64 point.isSome.toNat := by
      rw [address]
      cases point with
      | none => rw [P256.Proofs.Common.Memory.memLoad8_of_byte decoded]; decide +kernel
      | some point =>
        rw [P256.Proofs.Common.Memory.memLoad8_of_byte decoded.2]
        change (1 : UInt8).toBitVec.setWidth 64 = BitVec.ofNat 64 1
        decide +kernel
    exact (agreesU.read (n := 64) (r := 14) (by simp [copyComponents])).trans (writes.1.trans value)
  · exact ((agreesA.trans agreesU).read (n := 64) (r := 3) (by simp [copyComponents]))

end P256.Proofs.Sec1.Affine.Compressed.Finish
