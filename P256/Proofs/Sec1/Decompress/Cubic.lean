import P256.Proofs.Sec1.Decompress.State
import P256.Proofs.Sec1.Decompress.Cubic.Power
import P256.Proofs.Sec1.Decompress.Cubic.Linear
import P256.Proofs.Sec1.Decompress.Cubic.Sum
import P256.Proofs.Sec1.Decompress.Cubic.RootSetup
import P256.Proofs.Program.FieldCall.Unary

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decompress

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Field Cubic

private theorem polynomial (x : Nat) :
    (((x*x%P256.Spec.Operations.domain.p*x%P256.Spec.Operations.domain.p +
      P256.Spec.Operations.domain.a*x%P256.Spec.Operations.domain.p)%
      P256.Spec.Operations.domain.p + P256.Spec.Operations.domain.b)%
      P256.Spec.Operations.domain.p) = P256.Spec.Points.curveRhs x := by
  simp [P256.Spec.Points.curveRhs, Nat.add_mod, Nat.mul_mod]

theorem root_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} {odd : Bool}
    (pre : Pre s boundary bytes odd)
    (state : InputState s t (Standards.SECG.ECC.Encoding.octetsToNat bytes) odd)
    (sqrt : ∀ (v : RamState) (x : Nat), SquareRoot.Pre v boundary →
      MontgomeryAt v (v.regValue .rsi) x →
      ∃ u, CalleeResult v u boundary 40 2176 ∧
        SquareRoot.SquareRootResultAt u (v.regValue .rdi) x) :
    ∃ fuel u, Advances boundary fuel t u ∧
      RootState s u (Standards.SECG.ECC.Encoding.octetsToNat bytes) odd := by
  obtain ⟨n, a, ra, sa, ipa, a13, a15, va, pa⟩ :=
    power_three pre.toCalleePre state.toFrameState state.rip state.r15 state.xCoordinate
  obtain ⟨m, b, rb, sb, ipb, b15, vb, pb⟩ :=
    add_linear pre.toCalleePre sa ipa a15 a13 (pa.montgomery state.xCoordinate) va
  obtain ⟨k, c, rc, sc, ipc, c12, vc, pc⟩ := add_constant pre.toCalleePre sb ipb b15 vb
  rw [polynomial] at vc
  have kept := (pa.trans pb).trans pc
  obtain ⟨j, d, rd, ready, _, effect⟩ := sqrt_setup boundary pre.outerBoundary c
    (readyToStep sc.machine sc.bindingsSupported)
    (programText_slice (programLoaded_codeIn sc.loaded) 0xfece sqrtSetupBytes
      (by decide) (by decide +kernel)) ipc
  have agrees : AgreesExcept [.reg 13,.reg 7,.reg 6,.rip] c d := effect.agrees
  have sd := sc.after_registers ready agrees (by simp [Component.Covers]) (by simp)
  have pd : PreservesInputs s c d := PreservesInputs.of_registers agrees
    (by simp [Component.Covers]) (by simp) (by simp)
  have value : MontgomeryAt d (stackPtr s - 80)
      (P256.Spec.Points.curveRhs (checkedX (Standards.SECG.ECC.Encoding.octetsToNat bytes))) := montgomeryAt_of_copy vc
    (fun i hi ↦ congrArg (fun mem : Ram ↦ mem[_]?) (agrees.external (by simp [Component.Covers])))
  have addr : stackPtr c + 80 = stackPtr s - 328 := input_stack_address sc.rsp (by decide)
  let layout : StackCallLayout 2592 32 40 2176 :=
    ⟨416, 80, 328, by decide, by decide, by decide, by decide, by decide, by decide,
      .inr (by decide)⟩
  obtain ⟨l, u, ru, su, ipu, result, regs, memory, _⟩ :=
    FieldCall.unary_call (x := P256.Spec.Points.curveRhs (checkedX (Standards.SECG.ECC.Encoding.octetsToNat bytes)))
      (resultAt := fun u a ↦ SquareRoot.SquareRootResultAt u a
        (P256.Spec.Points.curveRhs (checkedX (Standards.SECG.ECC.Encoding.octetsToNat bytes))))
      pre.toCalleePre sd layout rfl (by decide)
      0xfed9 0x4532 (by decide) (by decide +kernel) (by decide) (by decide)
      (inProgram_of_textOffset 0x14410 (by decide))
      (fun v hp hx ↦ sqrt v _ hp hx) effect.rip
      (effect.writes.2.2.trans c12) (effect.writes.2.1.trans addr) value
  have allKept := kept.trans pd
  refine ⟨n+m+k+j+l, u, (((ra.trans rb).trans rc).trans rd).trans ru,
    ⟨⟨su, ?_, ?_, ?_, ?_⟩, ipu, ?_, ?_, ⟨result, trivial⟩⟩⟩
  · have read : memLoad u.external (stackPtr s - 224) 64 =
        memLoad d.external (stackPtr s - 224) 64 := by
      apply memLoad_congr
      intro i hi
      change (u.external[_]?).getD 0 = (d.external[_]?).getD 0
      exact congrArg (fun b : Option UInt8 ↦ b.getD 0)
        (memory 224 8 (by decide) (by decide) (.inl (by decide)) i hi)
    exact read.trans ((allKept.read (offset := 224) (n := 64)
      (by simp [preservedWindows])).trans state.output)
  · have read : memLoad u.external (stackPtr s - 332) 32 =
        memLoad d.external (stackPtr s - 332) 32 := by
      apply memLoad_congr
      intro i hi
      change (u.external[_]?).getD 0 = (d.external[_]?).getD 0
      exact congrArg (fun b : Option UInt8 ↦ b.getD 0)
        (memory 332 4 (by decide) (by decide) (.inr (by decide)) i hi)
    exact read.trans ((allKept.read (offset := 332) (n := 32)
      (by simp [preservedWindows])).trans state.parity)
  · exact (regs .rbp (by simp)).trans ((allKept.1 .rbp (by simp)).trans state.valid)
  · exact montgomeryAt_of_copy (allKept.montgomery state.xCoordinate)
      (fun i hi ↦ memory 288 32 (by decide) (by decide) (.inl (by decide)) i hi)
  · exact (regs .r14 (by simp)).trans ((allKept.1 .r14 (by simp)).trans state.r14)
  · exact (regs .r13 (by simp)).trans (effect.writes.1.trans addr)

end P256.Proofs.Sec1.Decompress
