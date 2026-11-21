import Sha2.Proofs.Common.SHA256.Absorb.Proof.Frame

set_option autoImplicit false

namespace Sha2.Proofs.Common.Machine

open Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem call_result_register [Bindings] {s u t : RamState} {boundary : ReturnBoundary}
    {outputBytes reserve : Nat} {target : RamState → BitVec 64} {ret : BitVec 64}
    (effect : (callEffect target ret s).Holds s u)
    (result : CalleeResult u t boundary outputBytes reserve)
    {r : BitVec 5} (small : r.toNat < 16)
    (kept : r ∉ ([0, 1, 2, 6, 7, 8, 9, 10, 11] : List (BitVec 5))) :
    (.reg r : Operand 64).read t = (.reg r : Operand 64).read s := by
  have cases : r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 12 ∨ r = 13 ∨ r = 14 ∨ r = 15 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or,
      ← BitVec.toNat_inj, BitVec.reduceToNat] at kept ⊢
    omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (result.abi.1 .rbx (by simp)).trans
      (effect.agrees.read (n := 64) (r := 3) (by simp [callEffect, pushEffect_components]))
  · exact result.rsp.trans (callEffect_stack effect).2
  · exact (result.abi.1 .rbp (by simp)).trans
      (effect.agrees.read (n := 64) (r := 5) (by simp [callEffect, pushEffect_components]))
  · exact (result.abi.1 .r12 (by simp)).trans
      (effect.agrees.read (n := 64) (r := 12) (by simp [callEffect, pushEffect_components]))
  · exact (result.abi.1 .r13 (by simp)).trans
      (effect.agrees.read (n := 64) (r := 13) (by simp [callEffect, pushEffect_components]))
  · exact (result.abi.1 .r14 (by simp)).trans
      (effect.agrees.read (n := 64) (r := 14) (by simp [callEffect, pushEffect_components]))
  · exact (result.abi.1 .r15 (by simp)).trans
      (effect.agrees.read (n := 64) (r := 15) (by simp [callEffect, pushEffect_components]))

end Sha2.Proofs.Common.Machine

namespace Sha2.Proofs.Common.SHA256.Absorb

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

theorem Preserved.of_run_call_result [Bindings]
    {l : Layout} {initial before s u t : RamState} {n reserve fuel outputBytes calleeReserve : Nat}
    {regions : Vector MemoryRegion n} {target : RamState → BitVec 64} {ret : BitVec 64}
    (ctx : Context l initial regions reserve) (input : Preserved l initial before s regions)
    (run : Advances (returnBoundary initial) fuel s t)
    (effect : (callEffect target ret s).Holds s u)
    (callWrites : WritesWithin (callEffect target ret s).components (footprint l (l.sp initial)))
    (result : CalleeResult u t (returnBoundary initial) outputBytes calleeReserve)
    (within : ∀ region ∈ #v[registerRegion u .rdi outputBytes, Stack.region u calleeReserve],
      ∀ a, region.Contains a → ∃ outer ∈ footprint l (l.sp initial), outer.Contains a) :
    Preserved l initial before t regions := by
  have frame : PhaseFrame l (l.sp initial) s t := by
    refine ⟨call_result_frame effect callWrites result within, ?_⟩
    intro r small kept
    exact call_result_register effect result small (fun member => kept (ctx.flow.callerClobbers r member))
  refine ⟨input.state.of_run_call_result run effect ?_ result ?_,
    (result.rsp.trans (callEffect_stack effect).2).trans input.rsp, input.frame.trans frame⟩
  · intro c member a covered
    obtain ⟨inner, hi, ha⟩ := callWrites c member a covered
    exact ctx.within inner hi a.toNat ha
  · intro region member a contains
    obtain ⟨inner, hi, ha⟩ := within region member a contains
    exact ctx.within inner hi a ha

end Sha2.Proofs.Common.SHA256.Absorb
