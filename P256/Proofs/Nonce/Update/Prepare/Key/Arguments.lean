import P256.Proofs.Nonce.Update.Prepare.Key.Setup
import P256.Proofs.Nonce.Update.Prepare.State

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Prepare.Key

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

structure Arguments [Bindings] (initial s : RamState) (state : State) : Prop extends
    Context initial s state where
  rip : s.RIP = 0x109f4a
  source : s.regValue .rdi = initial.regValue .rdi

theorem arguments [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {state : State} (pre : DrbgCalleePre initial boundary 0x109f30 1856 state)
    (saved : Saved initial s state) :
    ∃ fuel t, Advances boundary fuel s t ∧ Arguments initial t state := by
  obtain ⟨fuel, t, run, ready, _, effect⟩ := Setup.run boundary pre.outerBoundary s
    (readyToStep saved.machine saved.bindingsSupported) (Setup.code saved.loaded) saved.rip
  have agrees : AgreesExcept [.reg 13, .reg 5, .reg 3, .rip] s t := effect.agrees
  have memory : t.external = s.external := agrees.external (by simp [Component.Covers])
  have finalFrame := saved.toFrameState.after_registers ready agrees
    (by simp [Component.Covers]) (by simp)
  have values := effect.writes
  change t.regValue .r13 = s.regValue .rdx ∧
    t.regValue .rbp = s.regValue .rsi ∧ t.regValue .rbx = s.regValue .rdi at values
  refine ⟨fuel,t,run,⟨finalFrame,values.2.2.trans saved.statePointer,
    values.2.1.trans saved.descriptors,values.1.trans saved.inputCount,?_⟩,
    effect.rip,(agrees.read (n := 64) (r := 7) (by simp)).trans saved.statePointer⟩
  · apply saved.drbg.copy
    intro i hi
    exact congrArg (fun m : Ram => m[initial.regValue .rdi + BitVec.ofNat 64 i]?) memory

end P256.Proofs.Nonce.Update.Prepare.Key
