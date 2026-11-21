import Sha2.Proofs.Common.SHA256.Finalize.Contract

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Finalize

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

structure Context [bindings : Bindings] (L : Layout) (initial : RamState)
    {n : Nat} (regions : Vector MemoryRegion n) (reserve : Nat) : Prop where
  wf : WellFormed L reserve
  flow : Flow L
  code : CodeFacts L
  blocks : BlockContracts L (returnBoundary initial)
  stride : UnitStringStride bindings
  machine : SupportedMachine bindings initial
  stack : Stack.Valid initial reserve
  avoids : (Stack.region initial reserve).Avoids (fun a => InProgram a ∨ InPageTables a)
  returnAddress : ValidReturnAddress initial
  within : ∀ region ∈ footprint L (L.sp initial), ∀ a, region.Contains a →
    ∃ outer ∈ regions, outer.Contains a

theorem Context.outside [Bindings] {L : Layout} {initial : RamState}
    {n reserve : Nat} {regions : Vector MemoryRegion n}
    (ctx : Context L initial regions reserve) : ¬ InProgram (returnBoundary initial).rip :=
  (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2

theorem PhaseFrame.refl (L : Layout) (sp : BitVec 64) (s : RamState) :
    PhaseFrame L sp s s :=
  ⟨memoryWriteFrame_refl s _, fun _ _ _ => rfl⟩

theorem PhaseFrame.trans {L : Layout} {sp : BitVec 64} {s t u : RamState}
    (first : PhaseFrame L sp s t) (second : PhaseFrame L sp t u) :
    PhaseFrame L sp s u :=
  ⟨memoryWriteFrame_trans first.memory second.memory,
    fun r hr kept => (second.registers r hr kept).trans (first.registers r hr kept)⟩

theorem PhaseFrame.of_agrees {L : Layout} {sp : BitVec 64} {s t : RamState}
    {components : List Component} (agrees : AgreesExcept components s t)
    (writes : WritesWithin components (footprint L sp))
    (registers : ∀ r : BitVec 5, r.toNat < 16 → r ∉ L.variant.clobbered →
      .reg r ∉ components) : PhaseFrame L sp s t :=
  ⟨agrees.memoryWriteFrame writes,
    fun r hr kept => agrees.read (registers r hr kept)⟩

theorem Context.outer_frame [Bindings] {L : Layout} {initial s t : RamState}
    {n reserve : Nat} {regions : Vector MemoryRegion n}
    (ctx : Context L initial regions reserve)
    (frame : MemoryWriteFrame s t (footprint L (L.sp initial))) :
    MemoryWriteFrame s t regions := by
  intro address outside
  apply frame address
  intro region member contains
  obtain ⟨outer, ho, ha⟩ := ctx.within region member address.toNat contains
  exact outside outer ho ha

theorem Preserved.initial [Bindings] {L : Layout} {initial s : RamState}
    {n : Nat} {regions : Vector MemoryRegion n} (state : ExecutionState initial s regions)
    (rsp : stackPtr s = L.sp initial) : Preserved L initial s s regions :=
  ⟨state, rsp, PhaseFrame.refl L _ s⟩

end Sha2.Proofs.Common.SHA256.Finalize
