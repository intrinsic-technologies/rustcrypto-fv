import P256.Proofs.Verifying.Core.Combine.Run
import P256.Proofs.Verifying.Core.Combine.Memory
import P256.Proofs.Verifying.Core.Combine.Constants
import P256.Proofs.Verifying.Core.Combine.Movsq

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Combine

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame
open SecretKeyFromBytes.Scalar (Nat256At)
open Projective.Multiply.Machine.Basepoint (basePoint)

set_option maxHeartbeats 1200000 in
theorem prepare_prefix [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {point : Projective} {u v r : Nat} (pre : Core.Pre s boundary)
    (state : Input s t point u v r) :
    ∃ fuel z, Advances boundary fuel t z ∧ PrefixReady s z point u v r := by
  obtain ⟨n,a,runA,frameA,effA⟩ := registers pre state.toFrameState
    0xdd69 generatorBytes generatorEffect (by decide) (by decide +kernel)
    (generator_setup boundary pre.outerBoundary) state.rip
    (by simp [generatorEffect,Effect.components,Component.Covers])
    (by simp [generatorEffect,Effect.components])
  have aw : a.regValue .rax = frameBase s+576#64 ∧ a.regValue .rcx = 12 ∧
      a.regValue .rdi = frameBase s+576#64 ∧ a.regValue .rsi = 0x202ac8 := by
    have h := effA.writes
    change a.regValue .rax = rspOf t+576#64 ∧ a.regValue .rcx = 12 ∧
      a.regValue .rdi = rspOf t+576#64 ∧ a.regValue .rsi = 0x202ac8 at h
    rw [show rspOf t = frameBase s from state.rsp] at h
    exact h
  have memA : a.external = t.external := effA.agrees.external
    (by simp [generatorEffect,Effect.components,Component.Covers])
  obtain ⟨b,runB,frameB,ripB,bytesB,agB⟩ := movsq pre.toCalleePre frameA
    0xdd80 576 12 (by decide) (by decide) (by decide) (by decide +kernel)
    effA.rip (by rw [frameA.rsp]; exact aw.2.2.1) aw.2.1
    (by rw [aw.2.2.2]; exact generator_readable frameA.loaded)
    (by rw [aw.2.2.2,aw.2.2.1]
        have addr : frameBase s+576#64 = stackPtr s-600 := by
          simp only [frameBase,BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl
        rw [addr]
        exact generator_stack_disjoint pre.toCalleePre (by decide) (by decide))
  rw [aw.2.2.1] at bytesB agB
  have uB : Nat256At b (frameBase s+800#64) u :=
    nat256_of_bytes state.scalar1 (fun i hi => by
      rw [byte_of_copy agB (by decide) (offset := 800) (len := 32) (by decide)
        (.inl (by decide)) hi,memA]; rfl)
  obtain ⟨m,c,runC,frameC,effC,uC⟩ := first_scalar pre frameB ripB uB
  obtain ⟨k,d,runD,frameD,effD⟩ := registers pre frameC
    0xddc3 pointBytes pointEffect (by decide) (by decide +kernel)
    (point_setup boundary pre.outerBoundary) effC.rip
    (by simp [pointEffect,Effect.components,Component.Covers])
    (by simp [pointEffect,Effect.components])
  have dw : d.regValue .rdx = frameBase s ∧ d.regValue .rcx = 12 ∧
      d.regValue .rdi = frameBase s ∧ d.regValue .rsi = frameBase s+1000 := by
    have h := effD.writes
    change d.regValue .rdx = rspOf c ∧ d.regValue .rcx = 12 ∧
      d.regValue .rdi = rspOf c ∧ d.regValue .rsi = rspOf c+1000 at h
    rw [show rspOf c = frameBase s from frameC.rsp] at h
    exact h
  have memD : d.external = c.external := effD.agrees.external
    (by simp [pointEffect,Effect.components,Component.Covers])
  obtain ⟨z,runZ,frameZ,ripZ,bytesZ,agZ⟩ := movsq pre.toCalleePre frameD
    0xddd6 0 12 (by decide) (by decide) (by decide) (by decide +kernel)
    effD.rip (by rw [BitVec.add_zero,frameD.rsp]; exact dw.2.2.1) dw.2.1
    (by rw [dw.2.2.2]; exact input_readable pre frameD)
    (by rw [dw.2.2.2,dw.2.2.1]; exact point_disjoint pre)
  rw [dw.2.2.1,dw.2.2.2] at bytesZ
  rw [dw.2.2.1] at agZ
  have generatorB : ProjectiveAt b (frameBase s+576#64) basePoint :=
    (generator_at frameA.loaded).of_bytes_eq (fun i hi => by rw [bytesB i hi,aw.2.2.2])
  have keyA : ProjectiveAt a (frameBase s+1000) point :=
    state.key.of_bytes_eq (fun i _ => by rw [memA])
  have keyC := key_after_stack pre (key_after_stack pre keyA (copy_memory pre frameA agB (by decide)))
    (first_memory pre frameB effC)
  have keyD : ProjectiveAt d (frameBase s+1000) point :=
    keyC.of_bytes_eq (fun i _ => by rw [memD])
  have generatorZ : ProjectiveAt z (frameBase s+576#64) basePoint := by
    apply generatorB.of_bytes_eq
    intro i hi
    rw [byte_of_copy (dst := 0) (by simpa only [BitVec.add_zero] using agZ)
      (by decide) (offset := 576) (len := 96) (by decide) (.inl (by decide)) hi,
      memD,first_byte frameB.rsp effC (offset := 576) (len := 96)
      (by decide) (.inl (by decide)) hi]
  have scalar1Z : Nat256At z (frameBase s+672#64) u :=
    nat256_of_bytes uC (fun i hi => by
      rw [byte_of_copy (dst := 0) (by simpa only [BitVec.add_zero] using agZ)
        (by decide) (offset := 672) (len := 32) (by decide) (.inl (by decide)) hi,memD]; rfl)
  have preserve {off x : Nat} (lo : 704 ≤ off) (hi : off+32 ≤ 1128)
      (val : Nat256At t (frameBase s+BitVec.ofNat 64 off) x) :
      Nat256At z (frameBase s+BitVec.ofNat 64 off) x := by
    apply nat256_of_bytes val
    intro i hi'
    rw [byte_of_copy (dst := 0) (by simpa only [BitVec.add_zero] using agZ)
      (by decide) (by omega) (.inl (by omega)) hi',memD,
      first_byte frameB.rsp effC (by omega) (.inr (by omega)) hi',
      byte_of_copy agB (by decide) (by omega) (.inl (by omega)) hi',memA]
  refine ⟨n+12+m+k+12,z,(((runA.trans runB).trans runC).trans runD).trans runZ,
    ⟨frameZ,ripZ,?_,?_,?_,generatorZ,scalar1Z,keyD.of_bytes_eq bytesZ,
      preserve (off := 832) (by decide) (by decide) state.scalar2,
      preserve (off := 704) (by decide) (by decide) state.savedR⟩⟩
  · exact (agZ.read (n := 64) (r := 0) (by simp)).trans
      ((effD.agrees.read (n := 64) (r := 0) (by simp [pointEffect,Effect.components])).trans
        ((effC.agrees.read (n := 64) (r := 0) (by simp [FirstScalar.effect,Effect.components])).trans
          ((agB.read (n := 64) (r := 0) (by simp)).trans aw.1)))
  · exact (agZ.read (n := 64) (r := 2) (by simp)).trans dw.1
  · have mB := copy_memory pre frameA agB (by decide)
    have mC := first_memory pre frameB effC
    have mZ := copy_memory pre frameD (by simpa only [BitVec.add_zero] using agZ) (dst := 0) (by decide)
    have readZ := prefix_load pre mZ (offset := 384) (n := 64) (by decide) (by decide)
    have readC := prefix_load pre mC (offset := 384) (n := 64) (by decide) (by decide)
    have readB := prefix_load pre mB (offset := 384) (n := 64) (by decide) (by decide)
    change memLoad z.external (frameBase s+384#64) 64 = _
    rw [readZ,memD,readC,readB,memA]
    exact state.output

end P256.Proofs.Verifying.Core.Combine
