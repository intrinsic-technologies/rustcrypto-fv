import Sha2.Proofs.Common.SHA256.Absorb.Contract
import Sha2.Proofs.Common.SHA256.Finalize.Proof.Transport

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Absorb

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

structure Context [bindings : Bindings] (l : Layout) (initial : RamState)
    {n : Nat} (regions : Vector MemoryRegion n) (reserve : Nat) : Prop where
  wf : WellFormed l reserve
  flow : Flow l
  code : CodeFacts l
  targets : CallTargets l
  blocks : BlockContracts l (returnBoundary initial)
  stride : UnitStringStride bindings
  machine : SupportedMachine bindings initial
  stack : Stack.Valid initial reserve
  avoids : (Stack.region initial reserve).Avoids (fun a => InProgram a ∨ InPageTables a)
  returnAddress : ValidReturnAddress initial
  within : ∀ region ∈ footprint l (l.sp initial), ∀ a, region.Contains a →
    ∃ outer ∈ regions, outer.Contains a

theorem Context.outside [Bindings] {l : Layout} {initial : RamState}
    {n reserve : Nat} {regions : Vector MemoryRegion n}
    (ctx : Context l initial regions reserve) : ¬ InProgram (returnBoundary initial).rip :=
  (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2

theorem PhaseFrame.refl (l : Layout) (sp : BitVec 64) (s : RamState) :
    PhaseFrame l sp s s :=
  ⟨memoryWriteFrame_refl s _, fun _ _ _ => rfl⟩

theorem PhaseFrame.trans {l : Layout} {sp : BitVec 64} {s t u : RamState}
    (first : PhaseFrame l sp s t) (second : PhaseFrame l sp t u) :
    PhaseFrame l sp s u :=
  ⟨memoryWriteFrame_trans first.memory second.memory,
    fun r hr kept => (second.registers r hr kept).trans (first.registers r hr kept)⟩

theorem PhaseFrame.of_agrees {l : Layout} {sp : BitVec 64} {s t : RamState}
    {components : List Component} (agrees : AgreesExcept components s t)
    (writes : WritesWithin components (footprint l sp))
    (registers : ∀ r : BitVec 5, r.toNat < 16 → r ∉ l.clobbered →
      .reg r ∉ components) : PhaseFrame l sp s t :=
  ⟨agrees.memoryWriteFrame writes,
    fun r hr kept => agrees.read (registers r hr kept)⟩

theorem Preserved.initial [Bindings] {l : Layout} {initial s : RamState}
    {n : Nat} {regions : Vector MemoryRegion n} (state : ExecutionState initial s regions)
    (rsp : stackPtr s = l.sp initial) : Preserved l initial s s regions :=
  ⟨state, rsp, PhaseFrame.refl l _ s⟩

end Sha2.Proofs.Common.SHA256.Absorb
