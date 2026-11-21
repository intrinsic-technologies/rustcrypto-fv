import P256.Proofs.SHA256.Frame.State

set_option autoImplicit false

namespace P256.Proofs.SHA256

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

def LocalWrite (initial : RamState) (address : BitVec 64) : Prop :=
  (registerRegion initial .rdi 32).Contains address.toNat ∨
    (stackPtr initial).toNat - 336 ≤ address.toNat ∧
    address.toNat < (stackPtr initial).toNat - 48

theorem _root_.P256.Proofs.Program.ScalarFrame.FrameState.sha_after_agrees [Bindings]
    {initial s t : RamState} {boundary : ReturnBoundary}
    {hash : Array UInt32} {input : ByteArray} {count : Nat}
    (pre : CompressionPre initial boundary hash input count)
    (state : ScalarFrame.FrameState initial s 32 336 336) {cs : List Component}
    (ready : ReadyToStep t) (h : AgreesExcept cs s t) (hsp : .reg 4 ∉ cs)
    (hwrite : ∀ c ∈ cs, ∀ address, c.Covers address → LocalWrite initial address)
    (hdf : Component.df ∉ cs := by component_not_mem)
    (hmxcsr : Component.mxcsr ∉ cs := by component_not_mem)
    (hfcw : Component.fcw ∉ cs := by component_not_mem) :
    ScalarFrame.FrameState initial t 32 336 336 := by
  apply state.after_effect pre.toCalleePre (by decide) ready h ?_ hsp hdf hmxcsr hfcw
  intro c hc a ha
  rcases hwrite c hc a ha with out | loc
  · exact ⟨_, by simp, out⟩
  · refine ⟨ScalarFrame.workRegion initial 336, by simp, ?_⟩
    have bounds := stack_bounds pre.stack
    change (stackPtr initial).toNat - 336 ≤ a.toNat ∧
      a.toNat < (stackPtr initial).toNat - 336 + (336 - 48)
    constructor <;> omega

end P256.Proofs.SHA256
