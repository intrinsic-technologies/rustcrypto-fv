import Hkdf.Proofs.Common.ExtractCaller
import Hkdf.Proofs.Common.Pad.Loop

set_option autoImplicit false

namespace Hkdf.Proofs.Common.ExtractCaller

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Spec.Program Hkdf.Proofs.Common

theorem inner_pad [bindings : Bindings] (simple : Bool)
    {initial : RamState} {salt : Option ByteArray} {inputs : Array Input}
    (environment : MachineRamUnitStrideDecodable bindings initial)
    (machine : SupportedIntegerMachineState bindings.processor initial)
    (call : ValidExtractCall (EnterKey.routine simple) initial salt inputs) :
    ∃ fuel t, Advances (returnBoundary initial) fuel initial t ∧ ReadyToStep t ∧
      CallFrame.Running initial (returnBoundary initial)
        #v[Stack.region initial (EnterKey.routine simple).minStackBytes] t ∧
      t.regValue .rsp = stackPtr initial - BitVec.ofNat 64 (Prepare.allocation simple) ∧
      t.RIP = (if simple then 0x105d1d else 0x1014be) ∧
      t.regValue .rax = 67 ∧
      (⟨(stackPtr initial - BitVec.ofNat 64 (EnterKey.layout simple).outputOffset).toNat,
        64⟩ : MemoryRegion).HasBytes t.external
        (HMAC.xorPad (HMAC.keyBlock (Standard.saltKey salt)) 0x36) := by
  obtain ⟨fuel, s, beforeRun, ready, running, rsp, pre⟩ :=
    pad_pre simple environment machine call
  have first : (Pad.layout (if simple then .v105d00 else .v1014a0)).first = 3 := by
    cases simple <;> rfl
  obtain ⟨loopFuel, t, loop, readyT, ripT, raxT, frame, stored⟩ :=
    Pad.contract_of_loop first pre ready pre.outside
  have writes : WritesWithin
      (Pad.components (stackPtr initial - BitVec.ofNat 64 (EnterKey.layout simple).outputOffset))
      #v[Stack.region initial (EnterKey.routine simple).minStackBytes] := by
    intro c hc a ha
    simp only [Pad.components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact ha.elim
    · exact ha.elim
    · refine ⟨Stack.region initial (EnterKey.routine simple).minStackBytes, by simp, ?_⟩
      exact Hkdf.Proofs.Common.Machine.stackRegion_contains_sub call.stack.2.2.1
        (by cases simple <;> decide +kernel) (by cases simple <;> decide +kernel) ha
    · exact ha.elim
  have final := running.of_agrees loop readyT frame writes (by
    intro region member a contained inside
    have equal : region = Stack.region initial (EnterKey.routine simple).minStackBytes := by
      simpa using member
    subst region
    exact (call.stackSeparation.2 _ (by simp)).2 a contained (.inl inside))
    (by simp only [Pad.components, List.mem_cons, List.not_mem_nil, or_false,
      reduceCtorEq, not_false_eq_true])
  refine ⟨fuel + loopFuel, t, beforeRun.trans loop, readyT, final,
    (frame.read (n := 64) (r := 4) (by simp [Pad.components])).trans rsp,
    ?_, ?_, ?_⟩
  · cases simple <;> exact ripT
  · rw [first] at raxT
    exact raxT
  · cases simple <;> exact stored

end Hkdf.Proofs.Common.ExtractCaller
