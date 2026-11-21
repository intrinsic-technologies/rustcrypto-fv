import P256.Proofs.SignatureFromDer.Fixed.Scalar.Prologue
import P256.Proofs.Program.ScalarFrame.Prologue
import P256.Proofs.SignatureFromDer.Fixed.Scalar.Decode.Prefix
import P256.Proofs.SignatureFromDer.Fixed.Scalar.Decode.Length
import P256.Proofs.SignatureFromDer.Fixed.Scalar.Decode.State

set_option autoImplicit false

open P256.Proofs.Program (CalleePre programLoaded_codeIn programText_slice)

namespace P256.Proofs.SignatureFromDer.Fixed.Scalar.Decode

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem start_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10fa20 32 40 288) (length : s.regValue .rdx = 32) :
    ∃ t, Stage s t boundary ∧ t.RIP = 0x10fa41 ∧ t.regValue .rsi = s.regValue .rsi := by
  obtain ⟨u, runU, readyU, loadedU, ripU, rspU, memoryU, agreesU⟩ := scalar_prologue pre
  have stateU := Program.ScalarFrame.prologue_frame pre (by decide) readyU loadedU rspU memoryU agreesU
  obtain ⟨n, v, runV, readyV, _, effectV⟩ := prefix_correct boundary pre.outerBoundary
    u readyU (programText_slice (programLoaded_codeIn loadedU) 0xfa2e prefixBytes
      (by decide +kernel) (by decide +kernel)) ripU
  have stateV := stateU.after_registers readyV effectV.agrees
    (by simp [prefixEffect, Effect.components, Component.Covers])
    (by simp [prefixEffect, Effect.components])
  have lengthV : v.regValue .rdx = 32 :=
    (effectV.agrees.read (n := 64) (r := 2) (by simp [prefixEffect, Effect.components])).trans
      ((agreesU.read (n := 64) (r := 2)
        (by simp [P256.Proofs.Program.saveFrame])).trans length)
  obtain ⟨t, runT, readyT, ripT, agreesT⟩ := length_branch readyV stateV.loaded
    effectV.rip lengthV pre.outerBoundary
  have stateT := stateV.after_registers readyT agreesT (by simp [Component.Covers]) (by simp)
  refine ⟨t, ⟨stateT, ⟨7+n+2, (runU.trans runV).trans runT⟩, ?_, ?_⟩, ripT, ?_⟩
  · exact (agreesT.read (n := 64) (r := 3) (by simp)).trans
      (effectV.writes.1.trans (agreesU.read (n := 64) (r := 7)
        (by simp [P256.Proofs.Program.saveFrame])))
  · exact (agreesT.read (n := 64) (r := 14) (by simp)).trans effectV.writes.2
  · exact (agreesT.read (n := 64) (r := 6) (by simp)).trans
      ((effectV.agrees.read (n := 64) (r := 6) (by simp [prefixEffect, Effect.components])).trans
        (agreesU.read (n := 64) (r := 6)
          (by simp [P256.Proofs.Program.saveFrame])))

end P256.Proofs.SignatureFromDer.Fixed.Scalar.Decode
