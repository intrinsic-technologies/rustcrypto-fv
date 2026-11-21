import AesGcm.Proofs.AES16.KeySchedule.Adjust.Evaluation128
import AesGcm.Proofs.AES16.KeySchedule.Adjust.Evaluation256
import AesGcm.Proofs.Machine.Runtime.Tactics

namespace AesGcm.Proofs.Machine.AES16.KeySchedule

runtime_callee_def AesGcm.Proofs.Machine.AES16.KeySchedule.adjust128_callee
  from AesGcm.Proofs.Machine.AES16.KeySchedule.adjust128_eval
runtime_callee_def AesGcm.Proofs.Machine.AES16.KeySchedule.adjust256_callee
  from AesGcm.Proofs.Machine.AES16.KeySchedule.adjust256_eval

end AesGcm.Proofs.Machine.AES16.KeySchedule
