import P256.Proofs.Program.Compare.Instructions.Common
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple

namespace P256.Proofs.Program.Compare

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem readGPR8_run_of_rex_or_low (s : RamState) (r : BitVec 5) (rex : Bool)
    (hmode : In64BitMode s) (hr : rex = true ∨ r.toNat < 4) :
    (Read_GPR8 r rex).run s = (.ok (s.GPR[gprIndex r].setWidth 8), s) := by
  rcases hr with rfl | hr
  · exact readGPR8_run_of_rex s r hmode
  · exact readGPR8_run_of_low s r hr rex hmode

end P256.Proofs.Program.Compare
