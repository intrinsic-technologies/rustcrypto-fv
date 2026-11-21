import P256.Proofs.Verifying.Core.Combine.Prefix

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Combine

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame
open SecretKeyFromBytes.Scalar (Nat256At)
open Projective.Multiply.Machine.Basepoint (basePoint)
open Digest (base_add_toNat)

set_option maxHeartbeats 1200000 in
theorem pack [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {point : Projective} {u v r : Nat} (pre : Core.Pre s boundary)
    (state : PrefixReady s t point u v r) :
    ∃ fuel z, Advances boundary fuel t z ∧ Ready s z point u v r := by
  obtain ⟨n,a,runA,frameA,effA,vA⟩ := second_scalar pre state.toFrameState state.rip state.scalar2
  obtain ⟨m,b,runB,frameB,effB⟩ := registers pre frameA
    0xde0d firstBytes firstEffect (by decide) (by decide +kernel)
    (first_setup boundary pre.outerBoundary) effA.rip
    (by simp [firstEffect,Effect.components,Component.Covers])
    (by simp [firstEffect,Effect.components])
  have axA : a.regValue .rax = frameBase s+576#64 :=
    (effA.agrees.read (n := 64) (r := 0) (by simp [SecondScalar.effect,Effect.components])).trans state.generatorPointer
  have bw : b.regValue .r8 = frameBase s+128#64 ∧ b.regValue .rcx = 16 ∧
      b.regValue .rdi = frameBase s+128#64 ∧ b.regValue .rsi = frameBase s+576#64 := by
    have h := effB.writes
    change b.regValue .r8 = rspOf a+128#64 ∧ b.regValue .rcx = 16 ∧
      b.regValue .rdi = rspOf a+128#64 ∧ b.regValue .rsi = a.regValue .rax at h
    rw [axA] at h
    rw [show rspOf a = frameBase s from frameA.rsp] at h
    exact h
  have memB : b.external = a.external := effB.agrees.external
    (by simp [firstEffect,Effect.components,Component.Covers])
  obtain ⟨c,runC,frameC,ripC,bytesC,agC⟩ := movsq pre.toCalleePre frameB
    0xde20 128 16 (by decide) (by decide) (by decide) (by decide +kernel)
    effB.rip (by rw [frameB.rsp]; exact bw.2.2.1) bw.2.1
    (by rw [bw.2.2.2]; have h := stack_readable (frameOffset := 1176) pre.toCalleePre frameB
          (offset := 576) (len := 128) (by decide) (by decide)
        rw [frameB.rsp] at h; exact h)
    (by rw [bw.2.2.2,bw.2.2.1,base_add_toNat pre (by decide),base_add_toNat pre (by decide)]
        exact .inr (by omega))
  rw [bw.2.2.1,bw.2.2.2] at bytesC
  rw [bw.2.2.1] at agC
  obtain ⟨k,d,runD,frameD,effD⟩ := registers pre frameC
    0xde23 secondBytes secondEffect (by decide) (by decide +kernel)
    (second_setup boundary pre.outerBoundary) ripC
    (by simp [secondEffect,Effect.components,Component.Covers])
    (by simp [secondEffect,Effect.components])
  have dxC : c.regValue .rdx = frameBase s :=
    (agC.read (n := 64) (r := 2) (by simp)).trans
      ((effB.agrees.read (n := 64) (r := 2) (by simp [firstEffect,Effect.components])).trans
        ((effA.agrees.read (n := 64) (r := 2) (by simp [SecondScalar.effect,Effect.components])).trans state.keyPointer))
  have dw : d.regValue .rdi = frameBase s+256#64 ∧ d.regValue .rcx = 16 ∧
      d.regValue .rsi = frameBase s := by
    have h := effD.writes
    change d.regValue .rdi = rspOf c+256#64 ∧ d.regValue .rcx = 16 ∧
      d.regValue .rsi = c.regValue .rdx at h
    rw [dxC] at h
    rw [show rspOf c = frameBase s from frameC.rsp] at h
    exact h
  have memD : d.external = c.external := effD.agrees.external
    (by simp [secondEffect,Effect.components,Component.Covers])
  obtain ⟨e,runE,frameE,ripE,bytesE,agE⟩ := movsq pre.toCalleePre frameD
    0xde33 256 16 (by decide) (by decide) (by decide) (by decide +kernel)
    effD.rip (by rw [frameD.rsp]; exact dw.1) dw.2.1
    (by rw [dw.2.2]; have h := stack_readable (frameOffset := 1176) pre.toCalleePre frameD
          (offset := 0) (len := 128) (by decide) (by decide)
        rw [frameD.rsp,BitVec.add_zero] at h; exact h)
    (by rw [dw.2.2,dw.1,base_add_toNat pre (by decide)]
        have h : (frameBase s).toNat = (stackPtr s).toNat-1176 := stack_sub_toNat pre.stack (by decide)
        rw [h]; exact .inl (by omega))
  rw [dw.1,dw.2.2] at bytesE
  rw [dw.1] at agE
  obtain ⟨l,z,runZ,frameZ,effZ⟩ := registers pre frameE
    0xde36 callBytes callEffect (by decide) (by decide +kernel)
    (call_setup boundary pre.outerBoundary) ripE
    (by simp [callEffect,Effect.components,Component.Covers])
    (by simp [callEffect,Effect.components])
  have r8E : e.regValue .r8 = frameBase s+128#64 :=
    (agE.read (n := 64) (r := 8) (by simp)).trans
      ((effD.agrees.read (n := 64) (r := 8) (by simp [secondEffect,Effect.components])).trans
        ((agC.read (n := 64) (r := 8) (by simp)).trans bw.1))
  have zw : z.regValue .rdi = frameBase s ∧ z.regValue .rsi = frameBase s+128#64 := by
    have h := effZ.writes
    change z.regValue .rdi = rspOf e ∧ z.regValue .rsi = e.regValue .r8 at h
    rw [r8E] at h
    rw [show rspOf e = frameBase s from frameE.rsp] at h
    exact h
  have memZ : z.external = e.external := effZ.agrees.external
    (by simp [callEffect,Effect.components,Component.Covers])
  have genB : ProjectiveAt b (frameBase s+576#64) basePoint := by
    apply state.generator.of_bytes_eq
    intro i hi
    rw [memB,second_byte state.rsp effA (offset := 576) (len := 96)
      (by decide) (.inr (by decide)) hi]
    rfl
  have genC : ProjectiveAt c (frameBase s+128#64) basePoint :=
    genB.of_bytes_eq (fun i hi => bytesC i (by omega))
  have genZ : ProjectiveAt z (frameBase s+128#64) basePoint := by
    apply genC.of_bytes_eq
    intro i hi
    rw [memZ,byte_of_copy agE (by decide) (offset := 128) (len := 96)
      (by decide) (.inr (by decide)) hi,memD]
  have uB : Nat256At b (frameBase s+672#64) u :=
    nat256_of_bytes state.scalar1 (fun i hi => by
      rw [memB,second_byte state.rsp effA (offset := 672) (len := 32)
        (by decide) (.inr (by decide)) hi]; rfl)
  have uC : Nat256At c (frameBase s+224#64) u := by
    apply nat256_of_bytes uB
    intro i hi
    have h := bytesC (96+i) (by omega)
    rw [BitVec.ofNat_add] at h
    simp only [← BitVec.add_assoc] at h
    rw [BitVec.add_assoc (frameBase s) 128#64 96#64,
      BitVec.add_assoc (frameBase s) 576#64 96#64] at h
    exact h
  have uZ : Nat256At z (frameBase s+224#64) u :=
    nat256_of_bytes uC (fun i hi => by
      rw [memZ,byte_of_copy agE (by decide) (offset := 224) (len := 32)
        (by decide) (.inr (by decide)) hi,memD])
  have keyD : ProjectiveAt d (frameBase s) point := by
    apply state.key.of_bytes_eq
    intro i hi
    rw [memD,show frameBase s = frameBase s+0#64 from (BitVec.add_zero _).symm,
      byte_of_copy agC (by decide) (offset := 0) (len := 96) (by decide) (.inr (by decide)) hi,
      memB,second_byte state.rsp effA (offset := 0) (len := 96)
      (by decide) (.inl (by decide)) hi]
  have keyZ : ProjectiveAt z (frameBase s+256#64) point := by
    apply keyD.of_bytes_eq
    intro i hi
    rw [memZ,bytesE i (by omega)]
  have vD : Nat256At d (frameBase s+96#64) v :=
    nat256_of_bytes vA (fun i hi => by
      rw [memD,byte_of_copy agC (by decide) (offset := 96) (len := 32)
        (by decide) (.inr (by decide)) hi,memB]; rfl)
  have vZ : Nat256At z (frameBase s+352#64) v := by
    apply nat256_of_bytes vD
    intro i hi
    rw [memZ]
    have h := bytesE (96+i) (by omega)
    rw [BitVec.ofNat_add] at h
    simp only [← BitVec.add_assoc] at h
    rw [BitVec.add_assoc (frameBase s) 256#64 96#64] at h
    exact h
  have rZ : Nat256At z (frameBase s+704#64) r :=
    nat256_of_bytes state.savedR (fun i hi => by
      rw [memZ,byte_of_copy agE (by decide) (offset := 704) (len := 32)
        (by decide) (.inl (by decide)) hi,memD,
        byte_of_copy agC (by decide) (offset := 704) (len := 32)
        (by decide) (.inl (by decide)) hi,memB,
        second_byte state.rsp effA (offset := 704) (len := 32)
        (by decide) (.inr (by decide)) hi]; rfl)
  refine ⟨n+m+16+k+16+l,z,((((runA.trans runB).trans runC).trans runD).trans runE).trans runZ,
    ⟨frameZ,effZ.rip,zw.1,zw.2,?_,?_,rZ⟩⟩
  · have mC := copy_memory pre frameB agC (by decide)
    have mE := copy_memory pre frameD agE (by decide)
    have readE := prefix_load pre mE (offset := 384) (n := 64) (by decide) (by decide)
    have readC := prefix_load pre mC (offset := 384) (n := 64) (by decide) (by decide)
    have readA : memLoad a.external (frameBase s+384#64) 64 =
        memLoad t.external (frameBase s+384#64) 64 := by
      apply memLoad_congr
      intro i hi
      exact congrArg (fun value : Option UInt8 => value.getD 0)
        (second_byte state.rsp effA (offset := 384) (len := 8)
          (by decide) (.inr (by decide)) hi)
    change memLoad z.external (frameBase s+384#64) 64 = _
    rw [memZ,readE,memD,readC,memB,readA]
    exact state.output
  · refine ⟨genZ,?_,?_,?_⟩
    · simpa only [BitVec.add_assoc,BitVec.reduceAdd] using uZ
    · simpa only [BitVec.add_assoc,BitVec.reduceAdd] using keyZ
    · simpa only [BitVec.add_assoc,BitVec.reduceAdd] using vZ

end P256.Proofs.Verifying.Core.Combine
