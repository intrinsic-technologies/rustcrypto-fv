import P256.Proofs.Verifying.Core.Normalize.SelectSetup
import P256.Proofs.Verifying.Core.Memory
import P256.Proofs.Common.Field.SquareRoot.Exponent.ReadDigit.State

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Normalize

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame

theorem select_setup_pre [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Core.Pre s boundary) (state : Frame s t) (rip : t.RIP = 0x10de56) :
    SelectSetupPre t := by
  refine ⟨rip,stack_readable (frameOffset := 1176) pre.toCalleePre state (by decide) (by decide),?_,?_⟩
  · intro k hk
    exact local_writable8 pre state (by omega) (by omega)
  · intro k hk offset len hlen
    exact stack_code (frameOffset := 1176) pre.toCalleePre state (by decide) (by omega) hlen

theorem select_setup_writes [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Core.Pre s boundary) (state : Frame s t) :
    WritesWithin (selectSetupEffect t).components #v[registerRegion s .rdi 24,workRegion s 9992] := by
  intro c hc a ha
  simp [selectSetupEffect,Effect.components,Write.component,Operand.component] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals try exact ha.elim
  all_goals exact ⟨workRegion s 9992,by simp,local_work_contains pre state (by decide) ha⟩

theorem select_setup [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Core.Pre s boundary) (state : Frame s t) (rip : t.RIP = 0x10de56) :
    ∃ n u, Advances boundary n t u ∧ Frame s u ∧ (selectSetupEffect t).Holds t u := by
  obtain ⟨n,u,run,ready,_,effect⟩ := select_setup_block boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xde56 selectSetupBytes
      (by decide) (by decide +kernel)) (select_setup_pre pre state rip)
  exact ⟨n,u,run,state.after_effect pre.toCalleePre (by decide) ready effect.agrees
    (select_setup_writes pre state) (by simp [selectSetupEffect,Effect.components]),effect⟩

theorem select_setup_bytes {t u : RamState} {offset len : Nat}
    (effect : (selectSetupEffect t).Holds t u)
    (apart : ∀ k < 4, OffsetsApart (BitVec.ofNat 64 (864+8*k)) 8 (BitVec.ofNat 64 offset) len)
    (small : 8+len < 2^64) :
    ∀ i < len, u.external[stackPtr t + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      t.external[stackPtr t + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  intro i hi
  apply effect.agrees.byte
  intro c hc ha
  simp [selectSetupEffect,Effect.components,Write.component,Operand.component] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha
  all_goals obtain ⟨j,hj,he⟩ := ha
  · exact OffsetsApart.ne (apart 3 (by decide)) (stackPtr t) hj hi small he.symm
  · exact OffsetsApart.ne (apart 2 (by decide)) (stackPtr t) hj hi small he.symm
  · exact OffsetsApart.ne (apart 1 (by decide)) (stackPtr t) hj hi small he.symm
  · exact OffsetsApart.ne (apart 0 (by decide)) (stackPtr t) hj hi small (by simpa using he.symm)

theorem select_setup_choice {t u : RamState} {flag : UInt8}
    (effect : (selectSetupEffect t).Holds t u)
    (value : t.external[stackPtr t+928]? = some flag) :
    (u.regValue .rbx).setWidth 8 = flag.toBitVec ∧
      (u.regValue .rcx).setWidth 8 = flag.toBitVec := by
  have values := effect.writes
  simp only [selectSetupEffect,Write.AllHold] at values
  have hv : ((memLoad t.external (stackPtr t+928) 32).setWidth 64).setWidth 8 = flag.toBitVec := by
    rw [BitVec.setWidth_setWidth_of_le _ (by decide),
      P256.Proofs.Common.Field.SquareRoot.memLoad_setWidth_of_le _ _ (by decide) (by decide)]
    have hb := storedByte_memLoad t.external (stackPtr t+928) 0 (by decide : 0 < 8/8)
    have hb' : memLoad t.external (stackPtr t+928) 8 =
        (t.external[stackPtr t+928]?.getD 0).toBitVec := by
      simpa [storedByte,memByte,PhysicalMemory.read] using congrArg UInt8.toBitVec hb
    rw [value] at hb'
    exact hb'
  exact ⟨congrArg (BitVec.setWidth 8) values.2.2.2.2.1 |>.trans hv,
    congrArg (BitVec.setWidth 8) values.2.2.2.2.2.2.2.2.2 |>.trans hv⟩

end P256.Proofs.Verifying.Core.Normalize
