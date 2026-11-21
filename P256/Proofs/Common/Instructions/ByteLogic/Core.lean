import P256.Proofs.Common.Instructions.Setb.Form
import P256.Proofs.Common.Instructions.ByteOps.Effects

set_option autoImplicit false

namespace P256.Proofs.Common.Instructions.ByteLogic

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem readGPR8_run {σ : Type} (s : X86.State σ) (r : BitVec 5) (rex : Bool)
    (h : rex = true ∨ r.toNat < 4) (hmode : In64BitMode s) :
    (Read_GPR8 r rex).run s = (.ok (s.GPR[gprIndex r].setWidth 8), s) := by
  rcases h with rfl | hlow
  · exact readGPR8_run_of_rex s r hmode
  · exact readGPR8_run_of_low s r hlow rex hmode

theorem writeGPR8_run {σ : Type} (s : X86.State σ) (r : BitVec 5) (rex : Bool)
    (v : BitVec 8) (h : rex = true ∨ r.toNat < 4) (hmode : In64BitMode s) :
    (Write_GPR8 r rex v).run s =
      (.ok (), {s with GPR := Vector.set s.GPR (gprIndex r) (mergeGPR 8 v s.GPR[gprIndex r])}) := by
  rcases h with rfl | hlow
  · exact X86Proofs.writeGPR8_run_of_rex s r v hmode
  · exact X86Proofs.writeGPR8_run_of_low s r hlow rex v hmode

end P256.Proofs.Common.Instructions.ByteLogic
