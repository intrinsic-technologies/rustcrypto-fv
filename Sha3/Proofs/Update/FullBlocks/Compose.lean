import Sha3.Proofs.Update.FullBlocks.Body
import Sha3.Proofs.Update.FullBlocks.Control

namespace Sha3.Proofs.Update.FullBlocks

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program
open Keccak Permutation

theorem setup_stateWrites (initial : RamState) : StateWrites initial setupClobbers := by
  intro c hc address hcover
  exact (setup_nomem c hc address hcover).elim

theorem body_to_call [Bindings] {boundary : ReturnBoundary} {v : Variant}
    {initial s : RamState} {bytes : ByteArray} {state : Incremental.State} {offset : Nat}
    (hCall : CallContext v initial bytes state) (hInv : BodyInvariant initial s)
    (hb : ¬ InProgram boundary.rip) (hip : s.RIP = start v)
    (hpointer : s.regValue .r15 = initial.regValue .rsi)
    (hinput : (Operand.reg 14 : Operand 64).read s =
      initial.regValue .rdx + .ofNat 64 offset) (hsize : offset + v.rate ≤ bytes.size) :
    ∃ t, Advances boundary (2 * v.lanes + 3) s t ∧ BodyInvariant initial t ∧
      t.RIP = callPC v ∧
      (Operand.reg 5 : Operand 64).read t =
        (Operand.reg 5 : Operand 64).read s - .ofNat 64 v.rate ∧
      (Operand.reg 14 : Operand 64).read t =
        initial.regValue .rdx + .ofNat 64 (offset + v.rate) ∧
      (Operand.reg 7 : Operand 64).read t = initial.regValue .rsi ∧
      AgreesExcept (clobbers (initial.regValue .rsi) ++ setupClobbers) s t ∧
      memoryLanes (initial.regValue .rsi) t = (fun lane ↦
        memoryLanes (initial.regValue .rsi) s lane ^^^
          Absorption.blockLanes bytes offset v.rate lane) ∧
      cursor (initial.regValue .rsi) t = cursor (initial.regValue .rsi) s := by
  obtain ⟨u, hu, iu, ipu, fu, lanes⟩ := body_invariant hCall hInv hb hip hpointer hinput hsize
  obtain ⟨t, ht, rt, _, ipt, counter, source, argument, ft⟩ :=
    setup_advance iu.ready iu.loaded hb ipu
  have it := BodyInvariant.of_stateWrites hCall iu rt ft (setup_stateWrites initial)
    (by simp [setupClobbers])
  have he := ft.external setup_nomem
  refine ⟨t, hu.trans ht, it, ipt, ?_, ?_, ?_, fu.trans ft, ?_, ?_⟩
  · rw [counter, fu.read (by simp [clobbers])]
    rfl
  · rw [source, fu.read (by simp [clobbers]), hinput, BitVec.add_assoc, ← BitVec.ofNat_add]
    rfl
  · exact argument.trans ((fu.read (by simp [clobbers])).trans hpointer)
  · have hl : memoryLanes (initial.regValue .rsi) t =
        memoryLanes (initial.regValue .rsi) u := by
      unfold memoryLanes
      simp only [Operand.read, he]
    exact hl.trans lanes
  · have hc := cursor_of_frame fu
    simpa only [cursor, Operand.read, he] using hc

end Sha3.Proofs.Update.FullBlocks
