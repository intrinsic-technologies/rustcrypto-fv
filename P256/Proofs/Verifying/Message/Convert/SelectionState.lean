import P256.Proofs.Verifying.Message.Convert.Context
import P256.Proofs.Verifying.Message.Convert.Write
import P256.Proofs.Verifying.Message.Convert.Select
import P256.Proofs.Projective.Multiply.Operations
import P256.Proofs.Projective.Preserve

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Convert

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Program ScalarFrame Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem Context.after_select [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
    {message : ByteArray} {ret : BitVec 64} {destination value : Nat}
    (pre : Pre initial boundary message) (state : Context initial s boundary message)
    (result : SelectResult initial s t boundary ret destination value)
    (apart : 792 + 32 ≤ destination ∨ destination + 88 ≤ 792) :
    Context initial t boundary message := by
  obtain ⟨fuel, run⟩ := result.execution
  apply state.advance run result.toFrameState (work_frame_stack pre.toCalleePre result.writes)
  intro i hi
  change t.external[frameBase initial + BitVec.ofNat 64 384 + BitVec.ofNat 64 i]? =
    s.external[frameBase initial + BitVec.ofNat 64 384 + BitVec.ofNat 64 i]?
  rw [frame_address initial 384 (by decide)]
  exact result.bytes 792 88 (by decide) (by decide) apart i hi

theorem SelectResult.preserve_field [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
    {ret : BitVec 64} {destination value offset x : Nat}
    (result : SelectResult initial s t boundary ret destination value)
    (bound : offset + 32 ≤ 1176)
    (apart : (1176-offset) + 32 ≤ destination ∨ destination + 32 ≤ 1176-offset)
    (input : MontgomeryAt s (frameBase initial + BitVec.ofNat 64 offset) x) :
    MontgomeryAt t (frameBase initial + BitVec.ofNat 64 offset) x := by
  rw [frame_address initial offset (by omega)] at input ⊢
  exact result.memory (by omega) (by omega) apart input

structure Selecting [Bindings] (initial s : RamState) (boundary : ReturnBoundary)
    (message : ByteArray) (x y : Nat) : Prop extends Context initial s boundary message where
  yPointer : s.regValue .rbx = frameBase initial + 32
  zPointer : s.regValue .r14 = frameBase initial + 64
  identityPointer : s.regValue .r15 = frameBase initial + 128
  choice : s.regValue .rbp = 0
  x : MontgomeryAt s (frameBase initial + 0) x
  y : MontgomeryAt s (frameBase initial + 32) y
  z : MontgomeryAt s (frameBase initial + 64) 1
  identity : ProjectiveAt s (frameBase initial + 128) Projective.identity

theorem Selecting.after_select [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
    {message : ByteArray} {x y : Nat} {ret : BitVec 64} {destination value : Nat}
    (pre : Pre initial boundary message) (state : Selecting initial s boundary message x y)
    (result : SelectResult initial s t boundary ret destination value) (bound : destination ≤ 176) :
    Selecting initial t boundary message x y := by
  refine ⟨state.toContext.after_select pre result (.inr (by omega)),
    (result.registers .rbx (by simp)).trans state.yPointer,
    (result.registers .r14 (by simp)).trans state.zPointer,
    (result.registers .r15 (by simp)).trans state.identityPointer,
    (result.registers .rbp (by simp)).trans state.choice, ?_, ?_, ?_, ?_⟩
  · exact result.preserve_field (offset := 0) (by decide) (.inr (by omega)) state.x
  · exact result.preserve_field (offset := 32) (by decide) (.inr (by omega)) state.y
  · exact result.preserve_field (offset := 64) (by decide) (.inr (by omega)) state.z
  · apply state.identity.of_bytes_eq
    have h := result.bytes 1048 96 (by decide) (by decide) (.inr (by omega))
    simpa only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg,
      BitVec.reduceAdd] using h

theorem Selecting.after_registers [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
    {message : ByteArray} {x y fuel : Nat} {cs : List Component}
    (state : Selecting initial s boundary message x y) (run : Advances boundary fuel s t)
    (ready : ReadyToStep t) (agrees : AgreesExcept cs s t)
    (memory : ∀ c ∈ cs, ∀ a, ¬ c.Covers a) (sp : .reg 4 ∉ cs)
    (df : .df ∉ cs) (mxcsr : .mxcsr ∉ cs) (fcw : .fcw ∉ cs)
    (rbx : .reg 3 ∉ cs) (rbp : .reg 5 ∉ cs) (r14 : .reg 14 ∉ cs) (r15 : .reg 15 ∉ cs) :
    Selecting initial t boundary message x y := by
  have unchanged := agrees.external memory
  refine ⟨state.toContext.after_registers run ready agrees memory sp df mxcsr fcw,
    (agrees.read (n := 64) (r := 3) rbx).trans state.yPointer,
    (agrees.read (n := 64) (r := 14) r14).trans state.zPointer,
    (agrees.read (n := 64) (r := 15) r15).trans state.identityPointer,
    (agrees.read (n := 64) (r := 5) rbp).trans state.choice, ?_, ?_, ?_, ?_⟩
  · exact state.x.of_bytes_eq (by intro i hi; rw [unchanged])
  · exact state.y.of_bytes_eq (by intro i hi; rw [unchanged])
  · exact state.z.of_bytes_eq (by intro i hi; rw [unchanged])
  · exact state.identity.of_bytes_eq (by intro i hi; rw [unchanged])

end P256.Proofs.Verifying.Message.Convert
