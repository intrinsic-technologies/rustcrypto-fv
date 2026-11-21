import Hkdf.Proofs.Common.Machine.Boundary
import Hkdf.Proofs.Standard.Update
import Hkdf.Proofs.Standard.Update.State

set_option autoImplicit false

namespace Hkdf.Proofs.Standard.Update

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Spec.Program Hkdf.Proofs.Common

theorem prepare_input [Bindings] {initial s : RamState} {salt : Option ByteArray}
    {inputs : Array Input} {index : Nat} (ctx : Context initial salt inputs)
    (state : LoopState initial s salt inputs index) :
    ∃ short fuel t, Advances (returnBoundary initial) fuel s t ∧ ReadyToStep t ∧
      PreparedInput initial t salt inputs index short := by
  obtain ⟨first, a, runA, readyA, buffered, ripA, pointer, length, tail, ix, copy⟩ :=
    load_input ctx state
  obtain ⟨second, t, runT, readyT, ripT, capacity, rest, frame⟩ :=
    prepare_case readyA buffered.loaded (returnBoundary_valid ctx).2.2 ripA
  have current := buffered_of_noMem ctx buffered runT readyT frame
    (by simp [Component.Covers]) (by simp) (by simp)
  let position := (prefixConcatenation inputs index).size % 64
  let count := (inputs[index]'state.remaining).bytes.size
  have positionBound : position < 64 := Nat.mod_lt _ (by decide)
  have countBound : count < 2^32 := extract_input_bound ctx.call ⟨index, state.remaining⟩
  have cap : 64 - a.regValue .r15 = BitVec.ofNat 64 (64 - position) := by
    rw [tail]
    have h : (64 : BitVec 64) - BitVec.ofNat 64 position =
        BitVec.ofNat 64 (64 - position) :=
      BitVec.ofNat_sub_ofNat_of_le 64 position (by omega) (by omega)
    exact h
  rw [length, cap] at ripT rest
  rw [cap] at capacity
  have target : t.RIP = if count < 64 - position then 0x101620 else 0x101674 := by
    change t.RIP = if count % 2^64 < (64 - position) % 2^64 then _ else _ at ripT
    simpa only [Nat.mod_eq_of_lt (by omega : count < 2^64),
      Nat.mod_eq_of_lt (by omega : 64 - position < 2^64)] using ripT
  refine ⟨decide (count < 64 - position), first + second, t, runA.trans runT, readyT, {
    toBuffered := current
    remaining := state.remaining
    rip := by simpa only [decide_eq_true_eq] using target
    pointer := (frame.read (n := 64) (r := 13) (by simp)).trans pointer
    length := (frame.read (n := 64) (r := 3) (by simp)).trans length
    tail := (frame.read (n := 64) (r := 15) (by simp)).trans tail
    capacity := capacity
    rest := rest
    indexRegister := (frame.read (n := 64) (r := 14) (by simp)).trans ix
    copyRegister := (frame.read (n := 64) (r := 12) (by simp)).trans copy
    branch := ?_
  }⟩
  change if decide (count < 64 - position) then count < 64 - position
    else 64 - position ≤ count
  by_cases small : count < 64 - position
  · simp only [small, decide_true, ↓reduceIte]
  · simp only [small, decide_false, Bool.false_eq_true, ↓reduceIte]
    change 64 - position ≤ count
    omega

end Hkdf.Proofs.Standard.Update
