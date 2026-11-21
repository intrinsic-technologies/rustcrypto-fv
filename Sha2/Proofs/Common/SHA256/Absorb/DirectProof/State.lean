import Sha2.Proofs.Common.SHA256.Absorb.DirectProof.Code
import Sha2.Proofs.Common.SHA256.Finalize.Proof.Transport
import Sha2.Proofs.Common.SHA256.Absorb.Proof.CallFrame

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Absorb.Direct

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

structure Context [bindings : Bindings] (l : Layout) (initial : RamState)
    {n : Nat} (regions : Vector MemoryRegion n) (reserve : Nat) : Prop where
  wf : WellFormed l reserve
  flow : Flow l
  code : CodeFacts l
  blocks : BlockContracts l (returnBoundary initial)
  stride : UnitStringStride bindings
  machine : SupportedMachine bindings initial
  stack : Stack.Valid initial reserve
  avoids : (Stack.region initial reserve).Avoids (fun a => InProgram a ∨ InPageTables a)
  returnAddress : ValidReturnAddress initial
  within : ∀ region ∈ footprint l (l.sp initial), ∀ a, region.Contains a →
    ∃ outer ∈ regions, outer.Contains a

structure Preserved [Bindings] (l : Layout) (initial before current : RamState)
    {n : Nat} (regions : Vector MemoryRegion n) : Prop where
  state : ExecutionState initial current regions
  rsp : stackPtr current = l.sp initial
  memory : MemoryWriteFrame before current (footprint l (l.sp initial))
  registers : ∀ r : BitVec 5, r.toNat < 16 → r ∉ clobbered →
    (.reg r : Operand 64).read current = (.reg r : Operand 64).read before

theorem Preserved.initial [Bindings] {l : Layout} {initial s : RamState}
    {n : Nat} {regions : Vector MemoryRegion n} (state : ExecutionState initial s regions)
    (rsp : stackPtr s = l.sp initial) : Preserved l initial s s regions :=
  ⟨state, rsp, memoryWriteFrame_refl s _, fun _ _ _ => rfl⟩

theorem kept_register_cases {r : BitVec 5} (small : r.toNat < 16) (kept : r ∉ clobbered) :
    r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 12 ∨ r = 13 := by
  simp only [clobbered, List.mem_cons, List.not_mem_nil, or_false, not_or,
    ← BitVec.toNat_inj, BitVec.reduceToNat] at kept ⊢
  omega

theorem stage_preserves_registers (stage : Stage) (l : Layout) (sp : BitVec 64) (s : RamState)
    (r : BitVec 5) (small : r.toNat < 16) (kept : r ∉ clobbered) :
    Component.reg r ∉ (stage.effect l sp s).components := by
  rcases kept_register_cases small kept with rfl | rfl | rfl | rfl | rfl
  all_goals cases stage <;> simp [Stage.effect, Effect.components, Write.component, Operand.component]

theorem Preserved.of_agrees [Bindings] {l : Layout} {initial before s t : RamState}
    {n fuel : Nat} {regions : Vector MemoryRegion n} {components : List Component}
    (input : Preserved l initial before s regions)
    (within : ∀ region ∈ footprint l (l.sp initial), ∀ a, region.Contains a →
      ∃ outer ∈ regions, outer.Contains a)
    (avoids : ∀ region ∈ footprint l (l.sp initial), region.Avoids InProgram)
    (run : Advances (returnBoundary initial) fuel s t) (ready : ReadyToStep t)
    (agrees : AgreesExcept components s t)
    (writes : WritesWithin components (footprint l (l.sp initial)))
    (registers : ∀ r : BitVec 5, r.toNat < 16 → r ∉ clobbered → .reg r ∉ components)
    (df : .df ∉ components) : Preserved l initial before t regions := by
  have frame := agrees.memoryWriteFrame writes
  have outer : MemoryWriteFrame s t regions := by
    intro address outside
    apply frame address
    intro region member contains
    obtain ⟨region, member, contains⟩ := within region member address.toNat contains
    exact outside region member contains
  obtain ⟨priorFuel, prior⟩ := input.state.execution
  refine ⟨⟨⟨priorFuel + fuel, prior.trans run⟩,
    supportedMachine_of_ready_agrees input.state.machine ready agrees, ?_,
    fun a ha => agrees.grow a (input.state.allocated a ha),
    agrees.directionFlagClear df input.state.directionFlag,
    memoryWriteFrame_trans input.state.frame outer⟩, ?_,
    memoryWriteFrame_trans input.memory frame,
    fun r small kept => (agrees.read (registers r small kept)).trans (input.registers r small kept)⟩
  · intro address byte fetch
    rw [frame address]
    · exact input.state.loaded address byte fetch
    · intro region member contains
      exact avoids region member address contains ⟨byte, fetch⟩
  · exact (agrees.read (n := 64) (r := 4)
      (registers 4 (by decide) (by decide))).trans input.rsp

theorem Preserved.of_run_call_result [Bindings]
    {l : Layout} {initial before s u t : RamState} {n fuel outputBytes reserve : Nat}
    {regions : Vector MemoryRegion n} {target : RamState → BitVec 64} {ret : BitVec 64}
    (input : Preserved l initial before s regions)
    (within : ∀ region ∈ footprint l (l.sp initial), ∀ a, region.Contains a →
      ∃ outer ∈ regions, outer.Contains a)
    (run : Advances (returnBoundary initial) fuel s t)
    (effect : (callEffect target ret s).Holds s u)
    (callWrites : WritesWithin (callEffect target ret s).components (footprint l (l.sp initial)))
    (result : CalleeResult u t (returnBoundary initial) outputBytes reserve)
    (calleeWithin : ∀ region ∈ #v[registerRegion u .rdi outputBytes, Stack.region u reserve],
      ∀ a, region.Contains a → ∃ outer ∈ footprint l (l.sp initial), outer.Contains a) :
    Preserved l initial before t regions := by
  have memory := call_result_frame effect callWrites result calleeWithin
  have stack : stackPtr t = stackPtr s := result.rsp.trans (callEffect_stack effect).2
  refine ⟨input.state.of_run_call_result run effect ?_ result ?_, stack.trans input.rsp,
    memoryWriteFrame_trans input.memory memory, ?_⟩
  · intro c hc a ha
    obtain ⟨region, member, contains⟩ := callWrites c hc a ha
    exact within region member a.toNat contains
  · intro region member a contains
    obtain ⟨region, member, contains⟩ := calleeWithin region member a contains
    exact within region member a contains
  · intro r small kept
    apply Eq.trans _ (input.registers r small kept)
    change r ∉ ([0,1,2,6,7,8,9,10,11] ++ [14,15] : List (BitVec 5)) at kept
    exact call_result_register effect result small
      (fun member => kept (List.mem_append_left _ member))

theorem Preserved.of_call_result [Bindings]
    {l : Layout} {initial before s u t : RamState} {n fuel outputBytes reserve : Nat}
    {regions : Vector MemoryRegion n} {target : RamState → BitVec 64} {ret : BitVec 64}
    (input : Preserved l initial before s regions)
    (within : ∀ region ∈ footprint l (l.sp initial), ∀ a, region.Contains a →
      ∃ outer ∈ regions, outer.Contains a)
    (run : Advances (returnBoundary initial) fuel s u)
    (effect : (callEffect target ret s).Holds s u)
    (callWrites : WritesWithin (callEffect target ret s).components (footprint l (l.sp initial)))
    (result : CalleeResult u t (returnBoundary initial) outputBytes reserve)
    (calleeWithin : ∀ region ∈ #v[registerRegion u .rdi outputBytes, Stack.region u reserve],
      ∀ a, region.Contains a → ∃ outer ∈ footprint l (l.sp initial), outer.Contains a) :
    Preserved l initial before t regions := by
  obtain ⟨calleeFuel, callee⟩ := result.execution
  exact input.of_run_call_result within (run.trans callee) effect callWrites result calleeWithin

end Sha2.Proofs.Common.SHA256.Absorb.Direct
