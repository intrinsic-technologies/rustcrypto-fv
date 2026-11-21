import P256.Proofs.Generate.Sampler.Entry
import P256.Proofs.Generate.Sampler.Available
import P256.Proofs.Generate.Sampler.Preserve

set_option autoImplicit false

namespace P256.Proofs.Generate.Sampler

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

abbrev ReadReady [Bindings] (s t : RamState) (input : ByteArray) (offset : Nat) :=
  LoopReady s t input offset 0x100ca0 32

theorem first_read [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {input : ByteArray} {offset : Nat} (pre : Pre s boundary input)
    (state : LoopReady s t input offset) (available : offset+32 ≤ input.size) :
    ∃ u, (∃ fuel, Advances boundary fuel t u) ∧ ReadReady s u input offset := by
  let a := t
  have frameA := state.toState
  have outputA := state.output
  have remainA : a.regValue .r13 = BitVec.ofNat 64 (input.size-offset) :=
    state.remaining
  have remainBound : 32 ≤ ((Operand.reg 13 : Operand 64).read a).toNat := by
    change 32 ≤ (a.regValue .r13).toNat
    rw [remainA,BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
    · omega
    · have bounded : (source s).toNat + input.size < 2^32 := pre.bounded
      omega
  obtain ⟨fuelU,u,runU,readyU,_,effectU⟩ := available_run boundary pre.outerBoundary a
    (readyToStep frameA.machine frameA.bindingsSupported) (available_loaded frameA.loaded)
    ⟨state.rip,remainBound⟩
  have frameU := frameA.after_registers pre readyU effectU.agrees
    (by simp [availableEffect,Effect.components,Component.Covers])
    (by simp [availableEffect,Effect.components])
  refine ⟨u,⟨_,runU⟩,
    { toState := frameU, rip := effectU.rip, descriptor := ?_, source := ?_,
      remaining := ?_, decoded := ?_, buffer := ?_, output := ?_ }⟩
  · exact (effectU.agrees.read (n := 64) (r := 14) (by simp [availableEffect,Effect.components])).trans
      state.descriptor
  · have rbpA : a.regValue .rbp = source s+BitVec.ofNat 64 offset :=
      state.source
    have h : u.regValue .rbp = a.regValue .rbp+32#64 := effectU.writes
    rw [h,rbpA,BitVec.ofNat_add,BitVec.add_assoc]
  · exact (effectU.agrees.read (n := 64) (r := 13) (by simp [availableEffect,Effect.components])).trans remainA
  · exact (effectU.agrees.read (n := 64) (r := 15) (by simp [availableEffect,Effect.components])).trans
      state.decoded
  · exact (effectU.agrees.read (n := 64) (r := 12) (by simp [availableEffect,Effect.components])).trans
      state.buffer
  · rw [effectU.agrees.external (by simp [availableEffect,Effect.components,Component.Covers])]
    exact outputA

end P256.Proofs.Generate.Sampler
