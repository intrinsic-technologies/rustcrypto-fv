import AesGcm.Proofs.Machine.Runtime.Tactics
import AesGcm.Proofs.Machine.LIR.Program

namespace AesGcm.Proofs.Machine.Core.Decrypt

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
theorem exit_runBlock (use256 : Bool) (code : CodeMap)
    (args : Values Value Reg.count) (mem : Ram)
    (hr : Readable mem (args[4].get 64 + 168) 56)
    (hret : (memLoad mem (args[4].get 64 + 216) 64).toNat < 2^32) :
    ∃ output,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l102961 else .l102501), args, mem⟩ = .returned output ∧
      output.store = mem ∧
      output.tag = some ⟨64, memLoad mem (args[4].get 64 + 216) 64⟩ ∧
      output.values[4] = ⟨64, args[4].get 64 + 224⟩ ∧
      output.values[3] = ⟨64, memLoad mem (args[4].get 64 + 168) 64⟩ ∧
      output.values[12] = ⟨64, memLoad mem (args[4].get 64 + 176) 64⟩ ∧
      output.values[13] = ⟨64, memLoad mem (args[4].get 64 + 184) 64⟩ ∧
      output.values[14] = ⟨64, memLoad mem (args[4].get 64 + 192) 64⟩ ∧
      output.values[15] = ⟨64, memLoad mem (args[4].get 64 + 200) 64⟩ ∧
      output.values[5] = ⟨64, memLoad mem (args[4].get 64 + 208) 64⟩ ∧
      (∀ r : Fin 53, r.val ∈ [0, 22, 39, 50, 51] → output.values[r] = args[r]) ∧
      (GPRsTyped args → GPRsTyped output.values) := by
  cases use256
  all_goals
    refine ⟨?_, ?exec, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    case exec =>
      first
        | change LIR.program.runBlock (dialect code) ⟨.l102501, args, mem⟩ = _
        | change LIR.program.runBlock (dialect code) ⟨.l102961, args, mem⟩ = _
      cfg_eval []
      refine_norm []
      runtime_guards returned
      rfl
    all_goals first
      | rfl
      | (intro hTypes; runtime_typed)
      | (rintro ⟨r, hr⟩ hin; simp only [List.mem_cons, List.not_mem_nil, or_false] at hin;
          rcases hin with rfl | rfl | rfl | rfl | rfl <;> rfl)
      | runtime_finish []

end AesGcm.Proofs.Machine.Core.Decrypt
