import P256.Proofs.Field.Inverse.Tail.SecondZeroResult
import P256.Proofs.Field.Inverse.Tail.SecondArguments
import P256.Proofs.Field.Inverse.Tail.Select

set_option autoImplicit false


open P256.Proofs.Program (CalleePre)

namespace P256.Proofs.Field.Inverse

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)

theorem second_prepare_selected [Bindings] {s t : RamState} {boundary : ReturnBoundary} {beta : Nat} {select : Bool}
    (pre : Pre s boundary) (state : FrameState s t)
    (rip : t.RIP = 0x1141c2) (rbp : t.regValue .rbp = if select then 1 else 0)
    (candidate : Nat256At t (stackPtr s - 128) beta) :
    ∃ n u, Advances boundary n t u ∧ SelectCallState s u 128 select ∧ u.RIP = 0x1141ff ∧
      Nat256At u (stackPtr s - BitVec.ofNat 64 (if select then 128 else 168))
        (if select then beta else 0) := by
  obtain ⟨n1,t1,run1,state1,rip1,candidate1,zero1,agrees1⟩ := SecondZero.zero_stage_with_zero pre state rip candidate
  have rbp1 : t1.regValue .rbp = if select then 1 else 0 :=
    (agrees1.read (r := 5) (n := 64) (by simp [zeroComponents])).trans rbp
  obtain ⟨n2,t2,run2,ready2,_,effect2⟩ := SecondArguments.select_setup boundary pre.outerBoundary t1
    (readyToStep state1.machine state1.bindingsSupported) (SecondArguments.select_setup_code state1.loaded) rip1
  have mem2 := effect2.agrees.external (by
    simp [SecondArguments.selectSetupEffect, Effect.components, Component.Covers])
  have state2 := state1.of_registers pre ready2 effect2.agrees (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [SecondArguments.selectSetupEffect, Effect.components])
    (by simp [SecondArguments.selectSetupEffect, Effect.components, Component.Covers])
  have byte : (((Operand.reg 5 : Operand 64).read t1).setWidth 32).setWidth 64 = (if select then 1 else 0 : BitVec 64) := by
    change ((t1.regValue .rbp).setWidth 32).setWidth 64 = _
    rw [rbp1]
    cases select <;> rfl
  refine ⟨n1+n2,t2,run1.trans run2,
    ⟨state2,effect2.writes.2.2.1,effect2.writes.2.2.2.1,?_,?_,
      effect2.writes.2.2.2.2.trans byte,?_⟩,effect2.rip,?_⟩
  · exact effect2.writes.1.trans state1.rsp
  · exact effect2.writes.2.1.trans (state1.stack_address 40)
  · exact (effect2.agrees.read (r := 5) (n := 64) (by
      simp [SecondArguments.selectSetupEffect, Effect.components])).trans rbp1
  · cases select
    · exact nat256At_copy zero1 (fun i hi => congrArg (fun m : Ram => m[_]?) mem2)
    · exact nat256At_copy candidate1 (fun i hi => congrArg (fun m : Ram => m[_]?) mem2)

end P256.Proofs.Field.Inverse
