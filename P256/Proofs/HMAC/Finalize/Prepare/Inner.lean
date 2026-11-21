import P256.Proofs.HMAC.Finalize.Prepare.Interface
import P256.Proofs.HMAC.Finalize.Frame
import P256.Proofs.Common.Instructions.RepMovsqAny

set_option autoImplicit false

namespace P256.Proofs.HMAC.Finalize.Prepare

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Program.ScalarFrame (workRegion)
open P256.Proofs.Common
open P256.Proofs.Program (stack_bounds stack_sub_toNat)

theorem copy_inner [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {key input : ByteArray} (pre : HashCalleePre initial boundary 0x100f10 168 672)
    (state : CopyReady initial s key input) :
    ∃ t, Advances boundary 13 s t ∧ Prepared initial t key input ∧
      t.RIP = paddingStart false := by
  have dstAddress : stackPtr s + 72 = stackPtr initial - 256#64 :=
    stack_address state.rsp (by decide : 72 ≤ 328)
  have hn : (rcx.read s).toNat = 13 := by
    change (s.regValue .rcx).toNat = 13
    rw [state.countRegister]
    rfl
  have src : MemReadable s (rsi.read s) (8 * 13) := by
    change MemReadable s (s.regValue .rsi) 104
    rw [state.inputPointer]
    exact state_readable pre state.toFrameState (by decide)
  have dst : Common.Instructions.CrossPageStore.Writable s (rdi.read s) (8 * 13) := by
    change Common.Instructions.CrossPageStore.Writable s (s.regValue .rdi) 104
    rw [state.destinationPointer]
    exact ScalarFrame.stack_writable (stackPre pre) state.toFrameState (by decide) (by decide) (by decide)
  have apart : (rsi.read s).toNat + 8 * 13 ≤ (rdi.read s).toNat ∨
      (rdi.read s).toNat + 8 * 13 ≤ (rsi.read s).toNat := by
    change (s.regValue .rsi).toNat + 104 ≤ (s.regValue .rdi).toNat ∨
      (s.regValue .rdi).toNat + 104 ≤ (s.regValue .rsi).toNat
    rw [state.inputPointer, state.destinationPointer, dstAddress]
    change (initial.regValue .rdi + BitVec.ofNat 64 64).toNat + 104 ≤
        (stackPtr initial - BitVec.ofNat 64 256).toNat ∨
      (stackPtr initial - BitVec.ofNat 64 256).toNat + 104 ≤
        (initial.regValue .rdi + BitVec.ofNat 64 64).toNat
    rw [state_address_toNat pre (offset := 64) (by decide),
      stack_sub_toNat pre.stack (offset := 256) (by decide)]
    have bounds := stack_bounds pre.stack
    apply Classical.byContradiction
    intro overlap
    apply pre.separation 1 2 (by decide)
      (max ((initial.regValue .rdi).toNat + 64) ((stackPtr initial).toNat - 256))
    · change (initial.regValue .rdi).toNat ≤ _ ∧ _ < (initial.regValue .rdi).toNat + 168
      omega
    · change (stackPtr initial).toNat - 672 ≤ _ ∧
        _ < (Stack.region initial 672).start + (Stack.region initial 672).size
      rw [stack_region_end]
      omega
  have pc := Common.Instructions.RepMovsqAny.pre_of_memory state.rip
    state.directionFlag.df hn src dst apart
    (by change RangeApart (s.regValue .rdi) 104 _ 3
        rw [state.destinationPointer]
        exact ScalarFrame.stack_code (stackPre pre) state.toFrameState (by decide) (by decide)
          (codeOffset := 0xfb4) (by decide))
  obtain ⟨run, ready, effect, copied⟩ := Common.Instructions.RepMovsqAny.rep_movsq_execution pre.bindingsSupported.stringStride
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xfb4 [0xf3, 0x48, 0xa5]
      (by decide) (by decide +kernel)) pc hn
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xfb4 (by decide)))
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xfb7 (by decide)))
  simp only [show max 13 1 = 13 from rfl] at run ready effect copied
  generalize ht : nextStates 13 s = t at run ready effect copied
  have agrees : AgreesExcept [.reg 6, .reg 7, .reg 1,
      .mem (stackPtr s + 72) 104, .rip] s t := by
    simpa only [repMovsqEffect_components, hn, Nat.reduceMul,
      show rdi.read s = stackPtr s + 72 from state.destinationPointer] using effect.agrees
  have frame := state.toFrameState.after_effect (stackPre pre) (by decide) ready agrees (by
    intro c hc a covered
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact covered.elim
    exact ⟨workRegion initial 672, by simp,
      local_work_contains pre state.rsp (by decide) covered⟩) (by simp)
  refine ⟨t, run, ⟨⟨frame,
    (agrees.read (n := 64) (r := 3) (by simp)).trans state.outputPointer, ?_⟩, ?_⟩, effect.rip⟩
  · apply state.inner.copy
    change ∀ i < 104, t.external[s.regValue .rdi + BitVec.ofNat 64 i]? =
      s.external[s.regValue .rsi + BitVec.ofNat 64 i]? at copied
    simpa only [state.destinationPointer, state.inputPointer, dstAddress] using copied
  · apply state.outer.copy
    intro i hi
    apply agrees.byte
    intro c hc covered
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact covered.elim
    obtain ⟨j, hj, eq⟩ := covered
    apply OffsetsApart.ne (c₁ := -256#64) (len₁ := 104)
      (c₂ := -152#64) (len₂ := 104) (i := j) (j := i)
      (by unfold OffsetsApart; decide +kernel) (stackPtr initial) hj hi (by decide +kernel)
    simpa only [dstAddress, BitVec.sub_eq_add_neg] using eq.symm

end P256.Proofs.HMAC.Finalize.Prepare
