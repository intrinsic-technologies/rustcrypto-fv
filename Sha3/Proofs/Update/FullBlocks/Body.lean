import Sha3.Proofs.Update.Frame
import Sha3.Proofs.Update.FullBlocks.Context

namespace Sha3.Proofs.Update.FullBlocks

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program
open Keccak Permutation

theorem block_stateWrites (initial : RamState) :
    StateWrites initial (clobbers (initial.regValue .rsi)) := by
  intro c hc address hcover
  simp only [clobbers, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  all_goals try exact hcover.elim
  obtain ⟨i, hi, he⟩ := hcover
  exact ⟨i, by omega, he⟩

theorem body_invariant [Bindings] {boundary : ReturnBoundary} {v : Variant}
    {initial s : RamState} {bytes : ByteArray} {state : Incremental.State} {offset : Nat}
    (hCall : CallContext v initial bytes state) (hInv : BodyInvariant initial s)
    (hb : ¬ InProgram boundary.rip) (hip : s.RIP = start v)
    (hpointer : s.regValue .r15 = initial.regValue .rsi)
    (hinput : (Operand.reg 14 : Operand 64).read s =
      initial.regValue .rdx + .ofNat 64 offset) (hsize : offset + 8 * v.lanes ≤ bytes.size) :
    ∃ t, Advances boundary (2 * v.lanes) s t ∧ BodyInvariant initial t ∧
      t.RIP = loadPC v v.lanes ∧ AgreesExcept (clobbers (initial.regValue .rsi)) s t ∧
      memoryLanes (initial.regValue .rsi) t = fun lane ↦
        memoryLanes (initial.regValue .rsi) s lane ^^^
          Absorption.blockLanes bytes offset v.rate lane := by
  have ctx := Context.of_invariant hCall hInv hpointer hinput hsize hb
  obtain ⟨t, ht, ct, ipt, ft, lt⟩ := body_advance_bytes ctx hip (input_bytes hCall hInv) hsize
  refine ⟨t, ht, ?_, ipt, ft, lt⟩
  exact BodyInvariant.of_stateWrites hCall hInv ct.ready ft (block_stateWrites initial)
    (by simp [clobbers])

end Sha3.Proofs.Update.FullBlocks
