import AesGcm.Proofs.Machine.Runtime.Tactics
import AesGcm.Proofs.Machine.LIR.Program

namespace AesGcm.Proofs.Machine.AES16.KeySchedule

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem_by adjust256_eval (code : CodeMap)
    (args : Values Value Reg.count) (mem : Ram) :
    LIR.program.runBlock (dialect code) ⟨.l10593a, args, mem⟩ = _ := by
  cfg_eval [
    LIR.b_l10593a, LIR.b_l10593a_1, LIR.b_l10593a_2, LIR.b_l10593a_3,
    LIR.b_l10593a_4, LIR.b_l10593a_5, LIR.b_l10593a_6, LIR.b_l10593a_7,
    LIR.b_l10593a_8, LIR.b_l10593a_9, LIR.b_l10593a_10, LIR.b_l10593a_11,
    LIR.b_l10593a_12, LIR.b_l10593a_13, LIR.b_l10593a_14, LIR.b_l10593a_15,
    LIR.b_l10593a_16, LIR.b_l10593a_17, LIR.b_l10593a_18, LIR.b_l10593a_19,
    LIR.b_l10593a_20, LIR.b_l10593a_21, LIR.b_l10593a_22, LIR.b_l10593a_23,
    LIR.b_l10593a_24, LIR.b_l10593a_25, LIR.b_l10593a_26, LIR.b_l10593a_27,
    LIR.b_l10593a_28, LIR.b_l10593a_29, LIR.b_l10593a_30, LIR.b_l10593a_31,
    LIR.b_l10593a_32, LIR.b_l10593a_33, LIR.b_l10593a_34, LIR.b_l10593a_35,
    LIR.b_l10593a_36, LIR.b_l10593a_37, LIR.b_l10593a_38, LIR.b_l10593a_39,
    LIR.b_l10593a_40, LIR.b_l10593a_41, LIR.b_l10593a_42, LIR.b_l10593a_43,
    LIR.b_l10593a_44, LIR.b_l10593a_45, LIR.b_l10593a_46, LIR.b_l10593a_47,
    LIR.b_l10593a_48, LIR.b_l10593a_49, LIR.b_l10593a_50, LIR.b_l10593a_51,
    LIR.b_l10593a_52, LIR.b_l10593a_53, LIR.b_l10593a_54, LIR.b_l10593a_55,
    LIR.b_l10593a_56, LIR.b_l10593a_57, LIR.b_l10593a_58, LIR.b_l10593a_59,
    pushAddr, callMemPtr, callMemLen]
  cfg_name_stores
  rfl

end AesGcm.Proofs.Machine.AES16.KeySchedule
