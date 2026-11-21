import P256.Proofs.Sec1.Decode.Prepare.Prefix.Setup
import P256.Proofs.Sec1.Decode.Prepare.Prefix.CopySetup
import P256.Proofs.Sec1.Decode.Prepare.Prefix.Copy

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decode.Prepare

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem «prefix» [Bindings] {initial s : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    (pre : DecodePre initial boundary bytes) (state : Frame initial s)
    (rip : s.RIP = 0x10e522) (destination : s.regValue .rdi = initial.regValue .rdi)
    (source : s.regValue .rsi = initial.regValue .rsi)
    (count : s.regValue .rdx = BitVec.ofNat 64 bytes.size) (shape : EncodingShape bytes) :
    ∃ n t, Advances boundary n s t ∧ BufferReady initial t bytes := by
  obtain ⟨n1,t1,run1,ready1,_,effect1⟩ := setup boundary pre.outerBoundary bytes.size shape.size s
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xe522 setupBytes
      (by decide) (by decide +kernel)) ⟨rip,count⟩
  have frame1 := state.after_registers pre ready1 effect1.agrees
    (by simp [setupEffect,Effect.components,Component.Covers])
    (by simp [setupEffect,Effect.components])
    (by simp [setupEffect,Effect.components])
    (by simp [setupEffect,Effect.components])
    (by simp [setupEffect,Effect.components])
  have w15 : t1.regValue .r15 = initial.regValue .rdi := effect1.writes.1.trans destination
  have w12 : t1.regValue .r12 = 0 := effect1.writes.2.2.1
  have wbx : t1.regValue .rbx = initial.regValue .rsi := effect1.writes.2.2.2.2.2.1.trans source
  have w14 : t1.regValue .r14 = BitVec.ofNat 64 bytes.size := effect1.writes.2.2.2.2.2.2.2.1
  have dst1 : t1.regValue .rdi = stackPtr initial - 312#64 + BitVec.ofNat 64 bytes.size := by
    have h : t1.regValue .rdi = stackPtr s + BitVec.ofNat 64 bytes.size :=
      effect1.writes.2.2.2.2.1
    rw [h,state.rsp]
    bv_omega
  obtain ⟨n2,t2,run2,frame2,rip2,saved2,padding2⟩ := fill pre frame1 shape effect1.rip dst1
    effect1.writes.2.2.2.2.2.2.1 effect1.writes.2.2.2.2.2.2.2.2
  obtain ⟨n3,t3,run3,ready3,_,effect3⟩ := copy_setup boundary pre.outerBoundary t2
    (readyToStep frame2.machine frame2.bindingsSupported)
    (programText_slice (programLoaded_codeIn frame2.loaded) 0xe552 copySetupBytes
      (by decide) (by decide +kernel)) rip2
  have frame3 := frame2.after_registers pre ready3 effect3.agrees
    (by simp [copySetupEffect,Effect.components,Component.Covers])
    (by simp [copySetupEffect,Effect.components])
    (by simp [copySetupEffect,Effect.components])
    (by simp [copySetupEffect,Effect.components])
    (by simp [copySetupEffect,Effect.components])
  have dst3 : t3.regValue .rdi = stackPtr initial - 312#64 := by
    have h : t3.regValue .rdi = stackPtr t2 := effect3.writes.1
    rw [h,frame2.rsp]
    bv_omega
  have source3 : t3.regValue .rsi = initial.regValue .rsi :=
    effect3.writes.2.1.trans ((saved2 .rbx (by simp)).trans wbx)
  have count3 : t3.regValue .rdx = BitVec.ofNat 64 bytes.size :=
    effect3.writes.2.2.trans ((saved2 .r14 (by simp)).trans w14)
  have output3 : t3.regValue .r15 = initial.regValue .rdi :=
    (effect3.agrees.read (n := 64) (r := 15) (by simp [copySetupEffect,Effect.components])).trans
      ((saved2 .r15 (by simp)).trans w15)
  have zero3 : t3.regValue .r12 = 0 :=
    (effect3.agrees.read (n := 64) (r := 12) (by simp [copySetupEffect,Effect.components])).trans
      ((saved2 .r12 (by simp)).trans w12)
  have padding3 : ∀ i < 65, bytes.size ≤ i →
      t3.external[stackPtr initial - 312#64 + BitVec.ofNat 64 i]? = some 0 := by
    rw [effect3.agrees.external (by simp [copySetupEffect,Effect.components,Component.Covers])]
    exact padding2
  obtain ⟨n4,t4,run4,ready4⟩ := copy pre frame3 shape effect3.rip dst3 source3 count3 output3 zero3 padding3
  exact ⟨n1+n2+n3+n4,t4,((run1.trans run2).trans run3).trans run4,ready4⟩

end P256.Proofs.Sec1.Decode.Prepare
