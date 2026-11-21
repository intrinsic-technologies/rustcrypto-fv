import AesGcm.Proofs.Machine.Runtime.Tactics
import AesGcm.Proofs.Machine.LIR.Program
namespace AesGcm.Proofs.Machine.GCM
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime
set_option maxHeartbeats 1600000 in
theorem exit_runBlock (use256 : Bool) (code : CodeMap)
    (args : Values Value Reg.count) (mem : Ram)
    (hr : Readable mem (args[4].get 64) 64)
    (hret : (memLoad mem (args[4].get 64 + 56) 64).toNat < 2^32) :
    ∃ output,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l1022b1 else .l102171), args, mem⟩ = .returned output ∧
      output.store = mem ∧
      output.tag = some ⟨64, memLoad mem (args[4].get 64 + 56) 64⟩ ∧
      output.values[4] = ⟨64, args[4].get 64 + 64⟩ ∧
      output.values[3] = ⟨64, memLoad mem (args[4].get 64 + 40) 64⟩ ∧
      output.values[14] = ⟨64, memLoad mem (args[4].get 64 + 48) 64⟩ ∧
      (∀ r : Fin 53, r.val ∈ [5,12,13,15,22,39,50,51] → output.values[r] = args[r]) ∧
      (GPRsTyped args → GPRsTyped output.values) := by
  cases use256
  all_goals
    refine ⟨?_, ?exec, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    case exec =>
      first
        | change LIR.program.runBlock (dialect code) ⟨.l102171, args, mem⟩ = _
        | change LIR.program.runBlock (dialect code) ⟨.l1022b1, args, mem⟩ = _
      cfg_eval []
      refine_norm []
      runtime_guards returned
      rfl
    all_goals first
      | rfl
      | (intro hTypes; runtime_typed)
      | (rintro ⟨r, hr⟩ hin; simp only [List.mem_cons, List.not_mem_nil, or_false] at hin;
          rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
      | runtime_finish []
end AesGcm.Proofs.Machine.GCM
