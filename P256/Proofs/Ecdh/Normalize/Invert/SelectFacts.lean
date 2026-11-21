import P256.Proofs.Ecdh.Normalize.Invert.Call
import P256.Proofs.Ecdh.Normalize.Invert.SelectSetup
import P256.Proofs.Common.Field.SquareRoot.Exponent.ReadDigit.State

set_option autoImplicit false
namespace P256.Proofs.Ecdh.Normalize
open P256.Spec P256.Spec.Program P256.Spec.Operations Standards.SECG.ECC Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

theorem select_setup_pre [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {point : Projective} (pre : CalleePre s boundary 0x100000 32 32 3464)
    (state : Inverted s t boundary point) : SelectSetupPre t := by
  refine ⟨state.rip, stack_readable pre state.toFrameState (by decide) (by decide), ?_, ?_⟩
  · intro k hk
    rw [scalar_stack_address (frameOffset := 2056) state.rsp (by decide) (by omega)]
    apply writable_of_grow (stack_sub_writable8 pre.stack ?_ (by omega) (by omega)) state.allocated
    intro a ha hp
    exact pre.avoids (Stack.region s 3464) (by simp) a ha (.inr hp)
  · intro k hk offset len hlen
    exact stack_code (frameOffset := 2056) pre state.toFrameState (by decide) (by omega) hlen

theorem select_setup_frame [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x100000 32 32 3464)
    (state : FrameState s t 32 3464 2056) (ready : ReadyToStep u)
    (effect : (selectSetupEffect t).Holds t u) : FrameState s u 32 3464 2056 := by
  apply state.after_effect pre (by decide) ready effect.agrees ?_ (by simp [selectSetupEffect,Effect.components])
  intro c hc a ha
  simp [selectSetupEffect,Effect.components,Write.component,Operand.component] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact False.elim ha
  all_goals refine ⟨workRegion s 3464, by simp, ?_⟩
  · apply work_contains pre (offset := 2016) (len := 8) (by decide) (by decide)
    simpa only [scalar_stack_address (frameOffset := 2056) (offset := 40) state.rsp (by decide) (by decide)] using ha
  · apply work_contains pre (offset := 2024) (len := 8) (by decide) (by decide)
    simpa only [scalar_stack_address (frameOffset := 2056) (offset := 32) state.rsp (by decide) (by decide)] using ha
  · apply work_contains pre (offset := 2032) (len := 8) (by decide) (by decide)
    simpa only [scalar_stack_address (frameOffset := 2056) (offset := 24) state.rsp (by decide) (by decide)] using ha
  · apply work_contains pre (offset := 2040) (len := 8) (by decide) (by decide)
    simpa only [scalar_stack_address (frameOffset := 2056) (offset := 16) state.rsp (by decide) (by decide)] using ha

theorem select_setup_bytes {t u : RamState} {offset len : Nat}
    (effect : (selectSetupEffect t).Holds t u)
    (apart : ∀ k < 4, OffsetsApart (BitVec.ofNat 64 (16+8*k)) 8 (BitVec.ofNat 64 offset) len)
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

theorem select_setup_zero [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x100000 32 32 3464)
    (state : FrameState s u 32 3464 2056) (sp : stackPtr u = stackPtr t)
    (effect : (selectSetupEffect t).Holds t u) : Field.MontgomeryAt u (stackPtr t + 16) 0 := by
  refine ⟨by decide, ?_⟩
  simp only [Nat.zero_mul,Nat.zero_mod]
  apply SecretKeyFromBytes.Scalar.nat256At_of_memLoad_limbs (by decide)
  · have hr := stack_readable pre state (offset := 16) (len := 32) (by decide) (by decide)
    simpa only [sp,BitVec.ofNat_eq_ofNat,BitVec.add_zero] using hr.mem
  · intro j hj
    have values := effect.writes
    simp only [selectSetupEffect,Write.AllHold] at values
    have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    · simpa only [Operand.read, Nat.reduceMul, Nat.zero_div, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using values.2.2.2.1
    · simpa only [Operand.read, Nat.reduceMul, Nat.zero_div, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using values.2.2.1
    · simpa only [Operand.read, Nat.reduceMul, Nat.zero_div, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using values.2.1
    · simpa only [Operand.read, Nat.reduceMul, Nat.zero_div, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using values.1

theorem select_setup_choice {t u : RamState} {flag : UInt8}
    (effect : (selectSetupEffect t).Holds t u)
    (value : t.external[stackPtr t+112]? = some flag) :
    (u.regValue .rbp).setWidth 8 = flag.toBitVec ∧
      (u.regValue .rcx).setWidth 8 = flag.toBitVec := by
  have values := effect.writes
  simp only [selectSetupEffect,Write.AllHold] at values
  have hv : ((memLoad t.external (stackPtr t+112) 32).setWidth 64).setWidth 8 = flag.toBitVec := by
    rw [BitVec.setWidth_setWidth_of_le _ (by decide),
      P256.Proofs.Common.Field.SquareRoot.memLoad_setWidth_of_le _ _ (by decide) (by decide)]
    have hb := storedByte_memLoad t.external (stackPtr t+112) 0 (by decide : 0 < 8/8)
    have hb' : memLoad t.external (stackPtr t+112) 8 =
        (t.external[stackPtr t+112]?.getD 0).toBitVec := by
      simpa [storedByte,memByte,PhysicalMemory.read] using congrArg UInt8.toBitVec hb
    rw [value] at hb'
    exact hb'
  exact ⟨congrArg (BitVec.setWidth 8) values.2.2.2.2.1 |>.trans hv,
    congrArg (BitVec.setWidth 8) values.2.2.2.2.2.2.2.2.2 |>.trans hv⟩

end P256.Proofs.Ecdh.Normalize
