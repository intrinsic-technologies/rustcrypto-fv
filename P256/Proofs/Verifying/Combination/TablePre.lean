import P256.Proofs.Verifying.Combination.StackRegion
import P256.Proofs.Verifying.Combination.Table.Interface
import P256.Proofs.Program.CalleeStack
import P256.Proofs.Verifying.Combination.Interface

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Spec.Program.Routines

def tableCallLayout : StackCallLayout 8808 8 768 2120 :=
  ⟨6560, 6520, 4656, by decide, by decide, by decide, by decide, by decide, by decide, .inl (by decide)⟩

theorem table_pre [Bindings] {s t : RamState} {boundary : ReturnBoundary} {po : Nat}
    (pre : Pre s boundary) (state : State s t 6560)
    (pointLow : 4752 ≤ po) (pointHigh : po ≤ 6240)
    (rip : t.RIP = 0x10aff0) (input : t.regValue .rsi = stackPtr s - 6520)
    (output : t.regValue .rdi = stackPtr s - 4656)
    (cursor : memLoad t.external (stackPtr s - 6520) 64 = stackPtr s - 6496)
    (point : memLoad t.external (stackPtr s - 6496) 64 = stackPtr s - BitVec.ofNat 64 po)
    (ret : InProgram (returnBoundary t).rip) :
    Table.TablePre t boundary (stackPtr s - 6496) (stackPtr s - BitVec.ofNat 64 po) := by
  have cp := CalleePre.of_stack pre tableCallLayout state.bindingsSupported state.machine state.directionFlag state.loaded
    state.allocated rip state.rsp input output ret
  refine ⟨cp, ?_, point, localRegion_bounded pre (offset := 6496) (by decide) (by decide),
    localRegion_allocated pre state (offset := 6496) (by decide) (by decide),
    localRegion_avoids pre (offset := 6496) (by decide) (by decide), ?_,
    localRegion_bounded pre (by omega) (by omega),
    localRegion_allocated pre state (by omega) (by omega), ?_, ?_⟩
  · rw [input]
    exact cursor
  · intro region hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change (localRegion s 6496 8).Disjoint ⟨(t.regValue .rsi).toNat, 8⟩
      rw [input]
      exact localRegion_disjoint pre (a := 6496) (b := 6520) (by decide) (by decide) (.inl (by decide))
    · exact localRegion_disjoint pre (a := 6496) (b := po) (by decide) (by omega) (.inr (by omega))
    · change (localRegion s 6496 8).Disjoint ⟨(t.regValue .rdi).toNat, 768⟩
      rw [output]
      exact localRegion_disjoint pre (a := 6496) (b := 4656) (by decide) (by decide) (.inr (by decide))
    · exact localRegion_stack_disjoint pre state (offset := 6496) (by decide)
  · change (localRegion s po 96).Disjoint ⟨(t.regValue .rdi).toNat, 768⟩
    rw [output]
    exact localRegion_disjoint pre (a := po) (b := 4656) (by omega) (by decide) (.inr (by omega))
  · exact localRegion_stack_disjoint pre state (by omega)


end P256.Proofs.Verifying.Combination
