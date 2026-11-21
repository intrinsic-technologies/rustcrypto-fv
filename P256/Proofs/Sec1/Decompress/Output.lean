import P256.Proofs.Sec1.Decompress.Output.Payload
import P256.Proofs.Sec1.Decompress.Output.SetupEntry
import P256.Proofs.Sec1.Decompress.Output.Transfer
import P256.Proofs.Sec1.Decompress.Output.Tag
import P256.Proofs.Sec1.Decompress.Output.Choice
import P256.Proofs.Sec1.Decompress.Output.Store
import P256.Proofs.Sec1.Decompress.Output.Model

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decompress

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Standards.SECG.ECC
open Output

theorem output_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} {odd : Bool} (pre : Pre s boundary bytes odd)
    (state : SelectedState s t (Encoding.octetsToNat bytes) odd) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x1100b9 ∧
      AffineResultAt u (s.regValue .rdi)
        (P256.Spec.Points.decompress (Encoding.octetsToNat bytes) odd) := by
  obtain ⟨nA, a, runA, stateA, ripA, copied, frameA⟩ :=
    copy_payload pre.toCalleePre state.toFrameState state.rip
  have savedA : memLoad a.external (stackPtr s - 224) 64 = s.regValue .rdi := by
    rw [← state.output]
    apply memLoad_congr
    intro i hi
    apply memByte_congr
    exact copy_keeps_byte pre.toCalleePre frameA (offset := 224) (len := 8)
      (by decide) (by decide) hi
  obtain ⟨nB, b, runB, stateB, ripB, srcB, dstB, rbxB, countB, pointB, frameB⟩ :=
    setup_point pre.toCalleePre stateA ripA savedA
  have affineB : ∀ y, P256.Spec.Points.decompress (Encoding.octetsToNat bytes) odd =
      some (.affine (Encoding.octetsToNat bytes) y) →
      AffineAt b (stackPtr s - 408) (.affine (Encoding.octetsToNat bytes) y) := by
    intro y decoded
    have coordinates := state.coordinates y decoded
    apply pointB _ y (coordinates.1.of_bytes_eq copied)
    exact coordinates.2.of_bytes_eq (fun i hi =>
      copy_keeps_byte pre.toCalleePre frameA (offset := 376) (len := 32)
        (by decide) (by decide) hi)
  obtain ⟨c, runC, stateC, ripC, copiedC, frameC⟩ :=
    transfer pre.toCalleePre stateB ripB srcB dstB countB
  have regs := (frameA.trans frameB).trans frameC
  have rootC : (c.regValue .r15).setWidth 8 =
      BitVec.ofNat 8 (P256.Spec.Operations.sqrtMod
        (P256.Spec.Points.curveRhs (checkedX (Encoding.octetsToNat bytes)))).isSome.toNat := by
    have eq : c.regValue .r15 = t.regValue .r15 :=
      regs.read (n := 64) (r := 15) (by simp [copyComponents, setupComponents, transferComponents])
    rw [eq]
    exact state.rootValid
  have validC : c.regValue .rbp = BitVec.ofNat 64
      (decide (Encoding.octetsToNat bytes < P256.Spec.Operations.domain.p)).toNat :=
    (regs.read (n := 64) (r := 5) (by simp [copyComponents, setupComponents, transferComponents])).trans state.valid
  have rbxC : c.regValue .rbx = s.regValue .rdi :=
    (frameC.read (n := 64) (r := 3) (by simp [transferComponents])).trans rbxB
  obtain ⟨d, runD, readyD, ripD, valD, frameD⟩ := tag_arguments
    (readyToStep stateC.machine stateC.bindingsSupported) stateC.loaded pre.outerBoundary ripC
  have stateD := stateC.after_registers readyD frameD (by simp [Component.Covers]) (by simp)
  have tagD : d.regValue .rdi = (BitVec.ofNat 8
      (P256.Spec.Points.decompress (Encoding.octetsToNat bytes) odd).isSome.toNat).setWidth 64 := by
    rw [valD, rootC, validC,
      BitVec.setWidth_ofNat_of_le (by decide : 8 ≤ 64), validity_and]
  have rbxD : d.regValue .rbx = s.regValue .rdi :=
    (frameD.read (n := 64) (r := 3) (by simp)).trans rbxC
  obtain ⟨e, runE, stateE, ripE, valE, frameE⟩ := choice pre.toCalleePre stateD ripD
  have tagE : (Operand.reg 0 : Operand 8).read e =
      BitVec.ofNat 8 (P256.Spec.Points.decompress (Encoding.octetsToNat bytes) odd).isSome.toNat := by
    change (e.regValue .rax).setWidth 8 = _
    rw [valE, tagD]
    simp only [BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64), BitVec.setWidth_eq]
  have rbxE : e.regValue .rbx = s.regValue .rdi :=
    (frameE.read (n := 64) (r := 3) (by simp [ScalarFrame.choiceClobbers])).trans rbxD
  obtain ⟨u, runU, stateU, ripU, tagU, frameU⟩ :=
    store_validity pre.toCalleePre stateE ripE rbxE tagE
  refine ⟨_, u, ((((runA.trans runB).trans runC).trans runD).trans runE).trans runU,
    stateU, ripU, affineResult_of_tag_coordinates tagU ?_⟩
  intro y decoded
  have pointC := (affineB y decoded).of_bytes_eq (fun i hi => copiedC i (by omega))
  have pointD : AffineAt d (s.regValue .rdi) (.affine (Encoding.octetsToNat bytes) y) :=
    pointC.of_bytes_eq (fun i _ => by rw [frameD.external (by simp [Component.Covers])])
  have pointE := pointD.of_bytes_eq (fun i hi => choice_keeps_byte pre.toCalleePre frameE (by omega : i < 80))
  exact pointE.of_bytes_eq (fun _ hi => store_keeps_byte frameU hi)

end P256.Proofs.Sec1.Decompress
