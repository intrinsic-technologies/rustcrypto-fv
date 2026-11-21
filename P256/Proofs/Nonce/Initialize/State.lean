import P256.Proofs.Nonce.Initialize.PrologueFrame

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

structure Stage [Bindings] (initial s : RamState) (boundary : ReturnBoundary)
    (offset : BitVec 64 := 280) : Prop extends ScalarFrame.FrameState initial s 72 2144 offset where
  execution : ∃ fuel, Advances boundary fuel initial s

theorem entry [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} (pre : InitializePre s boundary orderAddress) :
    ∃ t, Stage s t boundary ∧ t.RIP = 0x1077a1 ∧
      AgreesExcept (Program.saveFrame s ++ [.flags]) s t := by
  obtain ⟨t, run, frame, rip, agrees⟩ := prologue_frame pre
  exact ⟨t, ⟨frame, 7, run⟩, rip, agrees⟩

theorem Stage.after_registers [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
    {cs : List Component} {fuel : Nat} {offset : BitVec 64}
    (stage : Stage initial s boundary offset) (run : Advances boundary fuel s t)
    (ready : ReadyToStep t) (agrees : AgreesExcept cs s t)
    (memory : ∀ c ∈ cs, ∀ a, ¬ c.Covers a) (rsp : .reg 4 ∉ cs)
    (df : Component.df ∉ cs := by component_not_mem)
    (mx : Component.mxcsr ∉ cs := by component_not_mem)
    (fc : Component.fcw ∉ cs := by component_not_mem) : Stage initial t boundary offset := by
  obtain ⟨n, hn⟩ := stage.execution
  exact ⟨stage.toFrameState.after_registers ready agrees memory rsp df mx fc,
    n + fuel, hn.trans run⟩

end P256.Proofs.Nonce.Initialize
