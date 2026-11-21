import Sha2.Proofs.Common.SHA256.Finalize.Proof.Geometry
import Sha2.Proofs.Common.SHA256.Finalize.Proof.Transport

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Finalize

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

theorem Preserved.of_agrees [Bindings] {L : Layout} {initial before s t : RamState}
    {n reserve fuel : Nat} {regions : Vector MemoryRegion n} {components : List Component}
    (ctx : Context L initial regions reserve) (input : Preserved L initial before s regions)
    (run : Advances (returnBoundary initial) fuel s t) (ready : ReadyToStep t)
    (agrees : AgreesExcept components s t)
    (writes : WritesWithin components (footprint L (L.sp initial)))
    (registers : ∀ r : BitVec 5, r.toNat < 16 → r ∉ L.variant.clobbered → .reg r ∉ components)
    (df : .df ∉ components) : Preserved L initial before t regions := by
  have frame := PhaseFrame.of_agrees agrees writes registers
  have memory := ctx.outer_frame frame.memory
  obtain ⟨steps, execution⟩ := input.state.execution
  refine ⟨⟨⟨steps + fuel, execution.trans run⟩,
    supportedMachine_of_ready_agrees input.state.machine ready agrees, ?_,
    fun a ha => agrees.grow a (input.state.allocated a ha),
    agrees.directionFlagClear df input.state.directionFlag,
    memoryWriteFrame_trans input.state.frame memory⟩, ?_, input.frame.trans frame⟩
  · intro address byte fetch
    rw [frame.memory address]
    · exact input.state.loaded address byte fetch
    · intro region member contains
      exact ctx.footprint_avoids region member address contains ⟨byte, fetch⟩
  · have rsp := frame.registers 4 (by decide) (by
      cases L.variant <;> simp [Variant.clobbered, Variant.registers,
        Blocks.Length.Registers.tail, Blocks.Length.Registers.blocks,
        Blocks.Length.Registers.preShifted, Variant.padReg, Variant.hashReg])
    exact rsp.trans input.rsp

theorem saved_register_cases {L : Layout} {r : BitVec 5}
    (small : r.toNat < 16) (kept : r ∉ L.variant.clobbered) :
    r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 12 ∨ r = 13 ∨ r = 14 ∨ r = 15 := by
  have caller : r ∉ ([0,1,2,6,7,8,9,10,11] : List (BitVec 5)) := by
    intro member
    apply kept
    simp only [Variant.clobbered, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at member ⊢
    rcases member with h | h | h | h | h | h | h | h | h <;> simp [h]
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or,
    ← BitVec.toNat_inj, BitVec.reduceToNat] at caller ⊢
  omega

theorem Preserved.of_run_call_result [Bindings]
    {L : Layout} {initial before s u t : RamState} {n reserve fuel outputBytes calleeReserve : Nat}
    {regions : Vector MemoryRegion n} {target : RamState → BitVec 64} {ret : BitVec 64}
    (ctx : Context L initial regions reserve) (input : Preserved L initial before s regions)
    (run : Advances (returnBoundary initial) fuel s t)
    (effect : (callEffect target ret s).Holds s u)
    (callWrites : WritesWithin (callEffect target ret s).components (footprint L (L.sp initial)))
    (result : CalleeResult u t (returnBoundary initial) outputBytes calleeReserve)
    (calleeWithin : ∀ region ∈ #v[registerRegion u .rdi outputBytes, Stack.region u calleeReserve],
      ∀ a, region.Contains a → ∃ outer ∈ footprint L (L.sp initial), outer.Contains a) :
    Preserved L initial before t regions := by
  have memory := call_result_frame effect callWrites result calleeWithin
  have stack : stackPtr t = stackPtr s := result.rsp.trans (callEffect_stack effect).2
  have frame : PhaseFrame L (L.sp initial) s t := by
    refine ⟨memory, ?_⟩
    intro r small kept
    rcases saved_register_cases small kept with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (result.abi.1 .rbx (by simp)).trans (effect.agrees.read (n := 64) (r := 3) (by simp [callEffect, pushEffect_components]))
    · exact stack
    · exact (result.abi.1 .rbp (by simp)).trans (effect.agrees.read (n := 64) (r := 5) (by simp [callEffect, pushEffect_components]))
    · exact (result.abi.1 .r12 (by simp)).trans (effect.agrees.read (n := 64) (r := 12) (by simp [callEffect, pushEffect_components]))
    · exact (result.abi.1 .r13 (by simp)).trans (effect.agrees.read (n := 64) (r := 13) (by simp [callEffect, pushEffect_components]))
    · exact (result.abi.1 .r14 (by simp)).trans (effect.agrees.read (n := 64) (r := 14) (by simp [callEffect, pushEffect_components]))
    · exact (result.abi.1 .r15 (by simp)).trans (effect.agrees.read (n := 64) (r := 15) (by simp [callEffect, pushEffect_components]))
  refine ⟨input.state.of_run_call_result run effect ?_ result ?_,
    stack.trans input.rsp, input.frame.trans frame⟩
  · intro c hc a ha
    obtain ⟨inner, member, contains⟩ := callWrites c hc a ha
    exact ctx.within inner member a.toNat contains
  · intro region member a contains
    obtain ⟨inner, hi, ha⟩ := calleeWithin region member a contains
    exact ctx.within inner hi a ha

theorem Preserved.of_call_result [Bindings]
    {L : Layout} {initial before s u t : RamState} {n reserve fuel outputBytes calleeReserve : Nat}
    {regions : Vector MemoryRegion n} {target : RamState → BitVec 64} {ret : BitVec 64}
    (ctx : Context L initial regions reserve) (input : Preserved L initial before s regions)
    (run : Advances (returnBoundary initial) fuel s u)
    (effect : (callEffect target ret s).Holds s u)
    (callWrites : WritesWithin (callEffect target ret s).components (footprint L (L.sp initial)))
    (result : CalleeResult u t (returnBoundary initial) outputBytes calleeReserve)
    (calleeWithin : ∀ region ∈ #v[registerRegion u .rdi outputBytes, Stack.region u calleeReserve],
      ∀ a, region.Contains a → ∃ outer ∈ footprint L (L.sp initial), outer.Contains a) :
    Preserved L initial before t regions := by
  obtain ⟨calleeFuel, callee⟩ := result.execution
  exact Preserved.of_run_call_result ctx input (run.trans callee) effect callWrites result calleeWithin

end Sha2.Proofs.Common.SHA256.Finalize
