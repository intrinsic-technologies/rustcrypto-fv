import Sha2.Proofs.Reset.Normalize
import Sha2.Proofs.Reset.Finalize
import Sha2.Proofs.Reset.Prefix

set_option autoImplicit false

namespace Sha2.Proofs.Reset

open Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.SHA256
open Sha2.Proofs.Common.SHA256.Instances

theorem normalized [bindings : Bindings] {initial s : RamState} {inputs : Array Input}
    {message : ByteArray} (v : Wrapper.Variant) (first : Bool)
    {form : Normalize.Form} {routine : Routine}
    (machine : SupportedMachine bindings initial)
    (call : TwoOutputs.ValidCall routine initial inputs)
    (state : ExecutionState initial s (regions routine initial))
    (rsp : stackPtr s = stackPtr initial - BitVec.ofNat 64 form.frameBytes)
    (rip : s.RIP = Normalize.entry first v form)
    (hasher : HasherAt s (if form = .reset then rspOf s else rspOf s + BitVec.ofNat 64 (Normalize.bufferOffset first form)) message v.initialHash)
    (stackSize : routine.minStackBytes = form.reserve := by cases v <;> rfl) :
    ∃ n, ExecutionState initial n (regions routine initial) ∧
      (Normalize.effect (Normalize.entry first v form) first s form).Holds s n ∧
      Finalize.Prepared ((Normalize.finalization first form).layout v) (rspOf s) message n := by
  have stack : Stack.Valid initial form.reserve := by
    simpa only [stackSize] using call.stack
  have read (offset len : Nat)
      (bound : offset + len ≤ form.frameBytes) :
      MemReadable s (rspOf s + BitVec.ofNat 64 offset) len := by
    change rspOf s = stackPtr initial - BitVec.ofNat 64 form.frameBytes at rsp
    rw [rsp]
    exact stack_frame_readable stack (by cases form <;> cases first <;> decide) state.allocated bound
  have pre : Normalize.Pre (Normalize.entry first v form) first s form := by
    refine ⟨rip, read _ 1 ?_, read _ 8 ?_, ?_⟩
    · cases form <;> cases first <;> decide
    · cases form <;> cases first <;> decide
    · cases first
      · trivial
      · exact read _ 8 (by cases form <;> decide)
  obtain ⟨fuel, n, run, ready, _, result⟩ := Normalize.run (Normalize.entry first v form) first
    (returnBoundary initial) (valid_return_boundary machine call.stack call.returnAddress).2.2
    (form := form) (Normalize.inside first v form) s (supportedMachine_readyToStep state.machine)
    (Normalize.code first v state.loaded form) pre
  have noMem : ∀ c ∈ (Normalize.effect (Normalize.entry first v form) first s form).components,
      ∀ a, ¬ c.Covers a := by
    cases form <;> cases first <;> simp [Normalize.effect, Normalize.shifted,
      Normalize.tailReg, Normalize.outputReg, Normalize.finalization, Finalization.variant,
      Finalize.Variant.registers, Blocks.Length.Registers.tail, Effect.components, Component.Covers]
  refine ⟨n, state.of_agrees ?_ run ready result.agrees ?_ ?_, result,
    Normalize.prepared first (form := form) (by
      cases form <;> cases first <;> simpa only [Normalize.bufferOffset, Normalize.finalization,
        Finalization.variant, Finalize.Variant.buffer, Blocks.Zero.Offset.value,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero, reduceCtorEq, ↓reduceIte] using hasher) result⟩
  · intro region member a ha hp
    have mem : region ∈ [TwoOutputs.outputRegion routine initial,
        TwoOutputs.secondOutputRegion routine initial,
        Stack.region initial routine.minStackBytes] := by
      simpa only [regions, Vector.mem_mk, List.mem_toArray] using member
    exact (call.separation.2 region mem).2 a ha (.inl hp)
  · intro c hc a ha
    exact (noMem c hc a ha).elim
  · cases form <;> cases first <;> simp [Normalize.effect, Normalize.shifted,
      Normalize.tailReg, Normalize.outputReg, Normalize.finalization, Finalization.variant,
      Finalize.Variant.registers, Blocks.Length.Registers.tail, Effect.components]

theorem normalized_finalized [bindings : Bindings] {initial s : RamState}
    {inputs : Array Input} {message : ByteArray} (v : Wrapper.Variant) (first : Bool)
    {form : Normalize.Form} {routine : Routine}
    (stride : UnitStringStride bindings) (machine : SupportedMachine bindings initial)
    (call : TwoOutputs.ValidCall routine initial inputs)
    (state : ExecutionState initial s (regions routine initial))
    (rsp : stackPtr s = stackPtr initial - BitVec.ofNat 64 form.frameBytes)
    (rip : s.RIP = Normalize.entry first v form)
    (hasher : HasherAt s (if form = .reset then rspOf s else rspOf s + BitVec.ofNat 64 (Normalize.bufferOffset first form)) message v.initialHash)
    (stackSize : routine.minStackBytes = form.reserve := by cases v <;> rfl) :
    ∃ n t, ExecutionState initial n (regions routine initial) ∧
      (Normalize.effect (Normalize.entry first v form) first s form).Holds s n ∧
      Finalize.Prepared ((Normalize.finalization first form).layout v) (rspOf s) message n ∧
      Finalize.Finalized ((Normalize.finalization first form).layout v) initial n t
        (regions routine initial) message := by
  obtain ⟨n, stateN, effectN, preparedN⟩ := normalized v first (form := form)
    (routine := routine) machine call state rsp rip hasher stackSize
  have sp : ((Normalize.finalization first form).layout v).sp initial = rspOf s := by
    change rspOf s = stackPtr initial - BitVec.ofNat 64 form.frameBytes at rsp
    rw [rsp]
    cases form <;> cases first <;> rfl
  obtain ⟨t, result⟩ := finalized v (Normalize.finalization first form) (by
      cases form <;> cases first <;> exact stackSize) stride machine call
    stateN (by rw [sp]; exact preparedN)
  exact ⟨n, t, stateN, effectN, preparedN, result⟩

theorem normalized_empty [bindings : Bindings] {initial s : RamState} {inputs : Array Input}
    (v : Wrapper.Variant) (form : Normalize.Form) {routine : Routine}
    (machine : SupportedMachine bindings initial)
    (call : TwoOutputs.ValidCall routine initial inputs)
    (state : ExecutionState initial s (regions routine initial))
    (rip : s.RIP = Normalize.emptyEntry v form)
    (hasher : HasherAt s (rspOf s + BitVec.ofNat 64 (Normalize.bufferOffset true form))
      ByteArray.empty v.initialHash)
    :
    ∃ n, ExecutionState initial n (regions routine initial) ∧
      (Normalize.emptyEffect (Normalize.emptyEntry v form) form s).Holds s n ∧
      Finalize.Prepared ((Normalize.finalization true form).layout v) (rspOf s) ByteArray.empty n ∧
      n.external = s.external := by
  obtain ⟨fuel, n, run, ready, _, result⟩ := Normalize.empty_run (Normalize.emptyEntry v form) form
    (returnBoundary initial) (valid_return_boundary machine call.stack call.returnAddress).2.2
    (Normalize.empty_inside v form) s (supportedMachine_readyToStep state.machine)
    (Normalize.empty_code v form state.loaded) rip
  have noMem : ∀ c ∈ (Normalize.emptyEffect (Normalize.emptyEntry v form) form s).components,
      ∀ a, ¬ c.Covers a := by
    cases form <;> simp [Normalize.emptyEffect, Effect.components, Component.Covers]
  refine ⟨n, state.of_agrees ?_ run ready result.agrees ?_ ?_, result,
    Normalize.empty_prepared form hasher result, result.agrees.external noMem⟩
  · intro region member a ha hp
    have mem : region ∈ [TwoOutputs.outputRegion routine initial,
        TwoOutputs.secondOutputRegion routine initial,
        Stack.region initial routine.minStackBytes] := by
      simpa only [regions, Vector.mem_mk, List.mem_toArray] using member
    exact (call.separation.2 region mem).2 a ha (.inl hp)
  · intro c hc a ha
    exact (noMem c hc a ha).elim
  · cases form <;> simp [Normalize.emptyEffect, Normalize.tailReg, Normalize.finalization,
      Finalization.variant, Finalize.Variant.registers, Blocks.Length.Registers.tail,
      Effect.components]

end Sha2.Proofs.Reset
