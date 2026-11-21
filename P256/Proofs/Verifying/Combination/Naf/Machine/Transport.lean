import P256.Proofs.Verifying.Combination.Naf.Interface
import P256.Proofs.Verifying.Combination.Naf.Machine.LoopState

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Machine

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar

theorem LoopState.after_registers [Bindings] {s t u : RamState} {n i k c : Nat}
    {ds : List Int} {pc pc' : BitVec 64} {cs : List Component}
    (state : LoopState s t n i k c ds pc) (ready : ReadyToStep u)
    (agrees : AgreesExcept cs t u) (memory : ∀ comp ∈ cs, ∀ a, ¬comp.Covers a)
    (rsp : .reg 4 ∉ cs) (r12 : .reg 12 ∉ cs) (r13 : .reg 13 ∉ cs)
    (r14 : .reg 14 ∉ cs) (r15 : .reg 15 ∉ cs) (rbp : .reg 5 ∉ cs)
    (rip : u.RIP = pc')
    (hdf : Component.df ∉ cs := by component_not_mem)
    (hmxcsr : Component.mxcsr ∉ cs := by component_not_mem)
    (hfcw : Component.fcw ∉ cs := by component_not_mem) : LoopState s u n i k c ds pc' := by
  have mem := agrees.external memory
  refine ⟨state.toFrameState.after_registers ready agrees memory rsp, rip,
    state.indexBound, state.carryBound, state.cachedIndex, state.dsLength, state.specification,
    ?_, ?_, ?_, (agrees.read (n := 64) r12).trans state.r12, (agrees.read (n := 64) r13).trans state.r13,
    (agrees.read (n := 64) r14).trans state.r14, (agrees.read (n := 64) r15).trans state.r15,
    (agrees.read (n := 64) rbp).trans state.rbp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨state.source.1, fun j hj => ?_⟩
    rw [mem]
    exact state.source.2 j hj
  · intro j hj
    rw [mem]
    exact state.output j hj
  · constructor
    · rw [mem]; exact state.iterator.pointer
    · rw [mem]; exact state.iterator.remaining
    · rw [mem]; exact state.iterator.index
    · rw [mem]; exact state.iterator.low
    · rw [mem]; exact state.iterator.high
  · rw [mem]; exact state.outputLength
  · rw [mem]; exact state.outputPointer
  · rw [mem]; exact state.bits
  · rw [mem]; exact state.half
  · rw [mem]; exact state.mask
  · rw [mem]; exact state.byteWindow

end P256.Proofs.Verifying.Combination.Naf.Machine
