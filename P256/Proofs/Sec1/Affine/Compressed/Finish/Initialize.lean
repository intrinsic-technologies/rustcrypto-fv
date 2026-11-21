import P256.Proofs.Sec1.Affine.Compressed.Finish.ConstantsSetup
import P256.Proofs.Sec1.Affine.Compressed.Finish.Constants

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Compressed.Finish

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem prepare_identity [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    {point : Option Standards.SECG.ECC.Curve.Point}
    (pre : AffineDecodePre s boundary bytes) (state : Frame s t)
    (rip : t.RIP = 0x110144) (decoded : AffineResultAt t (stackPtr s - 744) point) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x11015b ∧
      AffineResultAt u (stackPtr s - 744) point ∧
      AffineAt u (stackPtr s - 664) .infinity ∧ u.regValue .rax = stackPtr s - 664 ∧
      AgreesExcept [.reg 0, .reg 1, .reg 7, .reg 6, .mem (stackPtr s - 664) 72, .rip] t u := by
  obtain ⟨n, a, runA, readyA, _, effect⟩ := constants_setup boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x10144 constantsSetupBytes
      (by decide) (by decide +kernel)) rip
  have agreesA : AgreesExcept [.reg 0, .reg 1, .reg 7, .reg 6, .rip] t a := effect.agrees
  have frameA := state.after_registers readyA agreesA (by simp [Component.Covers]) (by simp)
  have writes := effect.writes
  change a.regValue .rax = stackPtr t + 96 ∧ a.regValue .rcx = 9 ∧
    a.regValue .rdi = stackPtr t + 96 ∧ a.regValue .rsi = 0x202df8 at writes
  have destination : stackPtr t + 96 = stackPtr s - 664 := by
    rw [state.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  obtain ⟨u, runU, frameU, ripU, identity, agreesU⟩ := copy_constants pre frameA
    (offset := 664) (by decide) (by decide) 0x10158 (by decide) (by decide +kernel)
    effect.rip writes.2.2.2 (writes.2.2.1.trans destination) writes.2.1
  refine ⟨n + 9, u, runA.trans runU, frameU, ripU, ?_, identity, ?_,
    (agreesA.trans agreesU).mono (by simp [constantComponents, BitVec.ofNat_eq_ofNat])⟩
  · apply decoded.of_bytes_eq
    intro i hi
    have unchanged : u.external[stackPtr s - 744 + BitVec.ofNat 64 i]? =
        a.external[stackPtr s - 744 + BitVec.ofNat 64 i]? := by
      apply agreesU.byte
      intro c hc ha
      simp only [constantComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals try exact ha.elim
      obtain ⟨j, hj, he⟩ := ha
      apply OffsetsApart.ne (c₁ := -664#64) (len₁ := 72) (c₂ := -744#64) (len₂ := 73)
        (by unfold OffsetsApart; decide +kernel) (stackPtr s) hj hi (by decide)
      simpa only [BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using he.symm
    exact unchanged.trans (by rw [agreesA.external (by simp [Component.Covers])])
  · exact (agreesU.read (n := 64) (r := 0) (by simp [constantComponents])).trans
      (writes.1.trans destination)

end P256.Proofs.Sec1.Affine.Compressed.Finish
