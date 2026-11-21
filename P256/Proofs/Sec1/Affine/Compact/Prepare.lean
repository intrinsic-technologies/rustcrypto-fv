import P256.Proofs.Sec1.Affine.Compressed.Setup
import P256.Proofs.Sec1.Affine.Compact.Setup
import P256.Proofs.Sec1.Affine.Compact.Arguments

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Compact

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem prepare [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    (pre : AffineDecodePre s boundary bytes) (state : Routed s t 5)
    (rip : t.RIP = 0x11020f) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x110227 ∧
      u.regValue .rsi = s.regValue .rsi + 1 ∧
      u.regValue .rdi = stackPtr s - 744 ∧
      u.regValue .rdx = 0 ∧
      u.regValue .rbx = s.regValue .rdi ∧ u.regValue .r15 = stackPtr s - 744 ∧ u.regValue .r13 = 0 := by
  obtain ⟨a, runA, frameA, ripA, diA, zeroA, agreesA⟩ := setup pre state rip
  obtain ⟨b, runB, frameB, ripB, axB, agreesB⟩ := Compressed.choice pre frameA 0x10214 0x8e57
    (by decide) (by decide +kernel) (by decide) ripA
  obtain ⟨fuel, u, runU, readyU, _, effectU⟩ := arguments_correct boundary pre.outerBoundary b
    (readyToStep frameB.machine frameB.bindingsSupported)
    (programText_slice (programLoaded_codeIn frameB.loaded) 0x10219 argumentBytes
      (by decide) (by decide +kernel)) ripB
  have agreesU : AgreesExcept [.reg 2, .reg 15, .reg 7, .reg 6, .rip] b u := effectU.agrees
  have writes := effectU.writes
  change u.regValue .rdx = ((b.regValue .rax).setWidth 8).setWidth 64 ∧
    u.regValue .r15 = stackPtr b + 16 ∧ u.regValue .rdi = stackPtr b + 16 ∧
    u.regValue .rsi = b.regValue .r14 at writes
  have address : stackPtr b + 16 = stackPtr s - 744 := by
    rw [frameB.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  refine ⟨2 + 6 + fuel, u, (runA.trans runB).trans runU,
    frameB.after_registers readyU agreesU (by simp [Component.Covers]) (by simp), effectU.rip,
    ?_, writes.2.2.1.trans address, ?_, ?_, writes.2.1.trans address, ?_⟩
  · exact writes.2.2.2.trans (((agreesA.trans agreesB).read (n := 64) (r := 14)
      (by simp [ScalarFrame.choiceClobbers])).trans state.xPointer)
  · rw [writes.1, axB, diA]
    decide +kernel
  · exact ((((agreesA.trans agreesB).trans agreesU).read (n := 64) (r := 3)
      (by simp [ScalarFrame.choiceClobbers])).trans state.output)

  · exact (((agreesB.trans agreesU).read (n := 64) (r := 13)
      (by simp [ScalarFrame.choiceClobbers])).trans zeroA)

end P256.Proofs.Sec1.Affine.Compact
