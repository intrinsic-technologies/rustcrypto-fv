import Md5.Proofs.Buffered.FinalizeReset.Prepare.Run
import Md5.Proofs.Buffered.FinalizeReset.Prepare.Bytes

namespace Md5.Proofs.Buffered.FinalizeReset.Prepare

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem run {variant : Variant} [Bindings] {boundary : ReturnBoundary} {message : ByteArray}
    {s : RamState} (hp : Pre boundary message s variant) :
    ∃ t, Result boundary message s t variant := by
  have hsize := variant.stackBytes_bounds
  obtain ⟨u, v, t, hc, hs, ha, hm⟩ := run_to_memset hp
  exact ⟨t, result_of_effects hp hc hs ha hm⟩

theorem Result.rbp {variant : Variant} [Bindings] {boundary : ReturnBoundary} {message : ByteArray}
    {s t : RamState} (h : Result boundary message s t variant) :
    (.reg 5 : Operand 64).read t = (.reg 5 : Operand 64).read s :=
  h.agrees.read (by simp [prepareChanges])

theorem Result.r12 {variant : Variant} [Bindings] {boundary : ReturnBoundary} {message : ByteArray}
    {s t : RamState} (h : Result boundary message s t variant) :
    (.reg 12 : Operand 64).read t = (.reg 12 : Operand 64).read s :=
  h.agrees.read (by simp [prepareChanges])

theorem Result.r13 {variant : Variant} [Bindings] {boundary : ReturnBoundary} {message : ByteArray}
    {s t : RamState} (h : Result boundary message s t variant) :
    (.reg 13 : Operand 64).read t = (.reg 13 : Operand 64).read s :=
  h.agrees.read (by simp [prepareChanges])

theorem Result.r14 {variant : Variant} [Bindings] {boundary : ReturnBoundary} {message : ByteArray}
    {s t : RamState} (h : Result boundary message s t variant) :
    (.reg 14 : Operand 64).read t = (.reg 14 : Operand 64).read s :=
  h.agrees.read (by simp [prepareChanges])

theorem Result.agrees_reset {variant : Variant} [Bindings] {boundary : ReturnBoundary} {message : ByteArray}
    {s t : RamState} (h : Result boundary message s t variant) :
    AgreesExcept (changes s) s t := prepare_agrees_reset h.agrees

theorem Result.saved_read {variant : Variant} [Bindings] {boundary : ReturnBoundary} {message : ByteArray}
    {s t : RamState} (h : Result boundary message s t variant) (hs : Storage s variant)
    (offset n : Nat) (hlo : 160 ≤ offset) (hhi : offset + n / 8 ≤ 232) :
    (.mem (stackPtr s + BitVec.ofNat 64 offset) : Operand n).read t =
      (.mem (stackPtr s + BitVec.ofNat 64 offset) : Operand n).read s :=
  agrees_saved_read hs h.agrees_reset offset n hlo hhi

end Md5.Proofs.Buffered.FinalizeReset.Prepare
