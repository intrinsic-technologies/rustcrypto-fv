import AesGcm.Proofs.Machine.LIR
import AesGcm.Proofs.Machine.Runtime.Tactics
namespace AesGcm.Proofs.Machine.CTR
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
theorem_by batchXor128_eval (code : CodeMap) (args : Values Value Reg.count) (mem : Ram) :
    LIR.program.runBlock (dialect code) ⟨.l107315, args, mem⟩ = _ := by
  cfg_eval [LIR.program, LIR.b_l107315, LIR.b_l107315_1, LIR.b_l107315_2, LIR.b_l107315_3, LIR.b_l107315_4, LIR.b_l107315_5, LIR.b_l107315_6, LIR.b_l107315_7, LIR.b_l107315_8, LIR.b_l107315_9, LIR.b_l107315_10, LIR.b_l107315_11, LIR.b_l107315_12, LIR.b_l107315_13, LIR.b_l107315_14, LIR.b_l107315_15]
  cfg_name_stores
  rfl
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
theorem_by batchXor256_eval (code : CodeMap) (args : Values Value Reg.count) (mem : Ram) :
    LIR.program.runBlock (dialect code) ⟨.l1087a5, args, mem⟩ = _ := by
  cfg_eval [LIR.program, LIR.b_l1087a5, LIR.b_l1087a5_1, LIR.b_l1087a5_2, LIR.b_l1087a5_3, LIR.b_l1087a5_4, LIR.b_l1087a5_5, LIR.b_l1087a5_6, LIR.b_l1087a5_7, LIR.b_l1087a5_8, LIR.b_l1087a5_9, LIR.b_l1087a5_10, LIR.b_l1087a5_11, LIR.b_l1087a5_12, LIR.b_l1087a5_13, LIR.b_l1087a5_14, LIR.b_l1087a5_15]
  cfg_name_stores
  rfl
end AesGcm.Proofs.Machine.CTR
