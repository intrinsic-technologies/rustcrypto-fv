import P256.Proofs.Verifying.Message.Hash.Interface
import P256.Proofs.Verifying.Message.Frame
import P256.Proofs.Program.WrapperMemory

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Convert

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Program ScalarFrame
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Context [Bindings] (initial s : RamState) (boundary : ReturnBoundary)
    (message : ByteArray) : Prop extends Message.Frame initial s where
  execution : ∃ fuel, Advances boundary fuel initial s
  digest : (MemoryRegion.mk (frameBase initial + 424).toNat 32).HasBytes
    s.external (Operations.hash message)
  savedKey : memLoad s.external (frameBase initial + 456) 64 = initial.regValue .rsi
  savedOutput : memLoad s.external (frameBase initial + 384) 64 = initial.regValue .rdi
  savedSignature : memLoad s.external (frameBase initial + 464) 64 = initial.regValue .r8
  stackFrame : MemoryWriteFrame initial s #v[Stack.region initial 9992]

theorem Context.of_hash [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {message : ByteArray} (state : Hash.Result initial s boundary message) :
    Context initial s boundary message :=
  ⟨state.toFrameState, state.execution, state.digest, state.savedKey, state.savedOutput,
    state.savedSignature, state.stackFrame⟩

theorem Context.advance [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
    {message : ByteArray} {fuel : Nat} (state : Context initial s boundary message)
    (run : Advances boundary fuel s t) (frame : Message.Frame initial t)
    (writes : MemoryWriteFrame s t #v[Stack.region initial 9992])
    (bytes : ∀ i < 88, t.external[frameBase initial + 384 + BitVec.ofNat 64 i]? =
      s.external[frameBase initial + 384 + BitVec.ofNat 64 i]?) :
    Context initial t boundary message := by
  have keep (offset : Nat) (bound : offset + 8 ≤ 88) :
      memLoad t.external (frameBase initial + 384 + BitVec.ofNat 64 offset) 64 =
        memLoad s.external (frameBase initial + 384 + BitVec.ofNat 64 offset) 64 := by
    apply memLoad_congr
    intro i hi
    change (t.external[frameBase initial + 384 + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?).getD 0 = _
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, bytes (offset+i) (by omega)]
    rfl
  refine ⟨frame, ?_, ?_, ?_, ?_, ?_, memoryWriteFrame_trans state.stackFrame writes⟩
  · obtain ⟨before, execution⟩ := state.execution
    exact ⟨before + fuel, execution.trans run⟩
  · refine ⟨state.digest.1, ?_⟩
    intro i
    have hi : i.val < 32 := by have size := state.digest.1; change _ = 32 at size; omega
    have h := state.digest.2 i
    change t.external[BitVec.ofNat 64 ((frameBase initial + 424).toNat + i.val)]? = _
    change s.external[BitVec.ofNat 64 ((frameBase initial + 424).toNat + i.val)]? = _ at h
    simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at h ⊢
    have v := bytes (40+i.val) (by omega)
    have address : frameBase initial + 384 + BitVec.ofNat 64 (40+i.val) =
        frameBase initial + 424 + BitVec.ofNat 64 i.val := by
      rw [BitVec.ofNat_add, ← BitVec.add_assoc]
      exact congrArg (fun a : BitVec 64 => a + BitVec.ofNat 64 i.val)
        (by rw [BitVec.add_assoc]; rfl)
    rw [address] at v
    exact v.trans h
  · have h : memLoad t.external (frameBase initial + 456) 64 =
        memLoad s.external (frameBase initial + 456) 64 := by
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using keep 72 (by decide)
    exact h.trans state.savedKey
  · have h : memLoad t.external (frameBase initial + 384) 64 =
        memLoad s.external (frameBase initial + 384) 64 := by
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] using keep 0 (by decide)
    exact h.trans state.savedOutput
  · have h : memLoad t.external (frameBase initial + 464) 64 =
        memLoad s.external (frameBase initial + 464) 64 := by
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using keep 80 (by decide)
    exact h.trans state.savedSignature

theorem Context.after_registers [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
    {message : ByteArray} {fuel : Nat} {cs : List Component}
    (state : Context initial s boundary message) (run : Advances boundary fuel s t)
    (ready : ReadyToStep t) (agrees : AgreesExcept cs s t)
    (memory : ∀ c ∈ cs, ∀ a, ¬ c.Covers a) (sp : .reg 4 ∉ cs)
    (df : .df ∉ cs) (mxcsr : .mxcsr ∉ cs) (fcw : .fcw ∉ cs) :
    Context initial t boundary message := by
  have unchanged := agrees.external memory
  exact state.advance run (state.toFrameState.after_registers ready agrees memory sp df mxcsr fcw)
    (by intro a ha; rw [unchanged]) (by intro i hi; rw [unchanged])

end P256.Proofs.Verifying.Message.Convert
