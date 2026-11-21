import P256.Proofs.SHA256.Mathematics.Standard.Schedule
import P256.Proofs.SHA256.Mathematics.Standard.Rounds

set_option autoImplicit false

namespace P256.Proofs.SHA256

theorem compressModel_eq_compress (hash : Array UInt32) (block : Array Bool) :
    compressModel hash block = Reference.compress hash block := by
  exact rounds_toStandard hash (schedule block) _ (schedule_toStandard block)

theorem compress_size (hash : Array UInt32) (block : Array Bool) :
    (Reference.compress hash block).size = 8 := by
  rw [← compressModel_eq_compress]
  rfl

end P256.Proofs.SHA256
