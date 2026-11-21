import AesGcm.Proofs.Machine.Runtime.Tactics
import AesGcm.Proofs.Machine.LIR.Program

namespace AesGcm.Proofs.Machine.AES16.KeySchedule

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem_by adjust128_eval (code : CodeMap)
    (args : Values Value Reg.count) (mem : Ram) :
    LIR.program.runBlock (dialect code) ⟨.l10446f, args, mem⟩ = _ := by
  cfg_eval [
    LIR.b_l10446f, LIR.b_l10446f_1, LIR.b_l10446f_2, LIR.b_l10446f_3,
    LIR.b_l10446f_4, LIR.b_l10446f_5, LIR.b_l10446f_6, LIR.b_l10446f_7,
    LIR.b_l10446f_8, LIR.b_l10446f_9, LIR.b_l10446f_10, LIR.b_l10446f_11,
    LIR.b_l10446f_12, LIR.b_l10446f_13, LIR.b_l10446f_14, LIR.b_l10446f_15,
    LIR.b_l10446f_16, LIR.b_l10446f_17, LIR.b_l10446f_18, LIR.b_l10446f_19,
    LIR.b_l10446f_20, LIR.b_l10446f_21, LIR.b_l10446f_22, LIR.b_l10446f_23,
    LIR.b_l10446f_24, LIR.b_l10446f_25, LIR.b_l10446f_26, LIR.b_l10446f_27,
    LIR.b_l10446f_28, LIR.b_l10446f_29, LIR.b_l10446f_30, LIR.b_l10446f_31,
    LIR.b_l10446f_32, LIR.b_l10446f_33, LIR.b_l10446f_34, LIR.b_l10446f_35,
    LIR.b_l10446f_36, LIR.b_l10446f_37, LIR.b_l10446f_38, LIR.b_l10446f_39,
    LIR.b_l10446f_40, LIR.b_l10446f_41,
    pushAddr, callMemPtr, callMemLen]
  cfg_name_stores
  rfl

end AesGcm.Proofs.Machine.AES16.KeySchedule
