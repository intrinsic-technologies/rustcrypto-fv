import P256.Proofs.Sec1.Affine.Compressed.Setup
import P256.Proofs.Sec1.Affine.Compressed.Arguments

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Compressed

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem prepare [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    {tag : UInt8} (pre : AffineDecodePre s boundary bytes) (state : Routed s t tag)
    (valid : tag = 2 ∨ tag = 3) (rip : t.RIP = 0x110108) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x110123 ∧
      u.regValue .rsi = s.regValue .rsi + 1 ∧
      u.regValue .rdi = stackPtr s - 592 ∧
      u.regValue .rdx = BitVec.ofNat 64 (tag == 3).toNat ∧
      u.regValue .rbx = s.regValue .rdi ∧ u.regValue .r15 = stackPtr s - 592 := by
  obtain ⟨a, runA, frameA, ripA, diA, agreesA⟩ := parity_setup pre state rip
  obtain ⟨b, runB, frameB, ripB, axB, agreesB⟩ := choice pre frameA 0x1010d 0x8f5e
    (by decide) (by decide +kernel) (by decide) ripA
  obtain ⟨fuel, u, runU, readyU, _, effectU⟩ := arguments_correct boundary pre.outerBoundary b
    (readyToStep frameB.machine frameB.bindingsSupported)
    (programText_slice (programLoaded_codeIn frameB.loaded) 0x10112 argumentBytes
      (by decide) (by decide +kernel)) ripB
  have agreesU : AgreesExcept [.reg 2, .reg 15, .reg 7, .reg 6, .rip] b u := effectU.agrees
  have writes := effectU.writes
  change u.regValue .rdx = ((b.regValue .rax).setWidth 8).setWidth 64 ∧
    u.regValue .r15 = stackPtr b + 168 ∧ u.regValue .rdi = stackPtr b + 168 ∧
    u.regValue .rsi = b.regValue .r14 at writes
  have address : stackPtr b + 168 = stackPtr s - 592 := by
    rw [frameB.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  refine ⟨2 + 6 + fuel, u, (runA.trans runB).trans runU,
    frameB.after_registers readyU agreesU (by simp [Component.Covers]) (by simp), effectU.rip,
    ?_, writes.2.2.1.trans address, ?_, ?_, writes.2.1.trans address⟩
  · exact writes.2.2.2.trans (((agreesA.trans agreesB).read (n := 64) (r := 14)
      (by simp [ScalarFrame.choiceClobbers])).trans state.xPointer)
  · rw [writes.1, axB, diA]
    rcases valid with rfl | rfl <;> decide
  · exact ((((agreesA.trans agreesB).trans agreesU).read (n := 64) (r := 3)
      (by simp [ScalarFrame.choiceClobbers])).trans state.output)

end P256.Proofs.Sec1.Affine.Compressed
