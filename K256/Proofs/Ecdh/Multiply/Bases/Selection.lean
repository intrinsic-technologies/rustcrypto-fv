import K256.Proofs.Ecdh.Multiply.Bases.Frame
import K256.Proofs.Generate.Generator.Multiply.Prepare.Bases.Selection

namespace K256.Proofs.Generate.Generator.Multiply.Prepare.Bases

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR K256.Proofs.Common.Field
  Standards.SECG.DomainParameters.Secp256k1 Common.Point.TableWords

theorem peerSelectFrame {fr : Activation} {a : Registers} {d : Nat} {peer : Projective} (e : PeerCoreEntry fr a d peer)
    (m : Ram) (flag : BitVec 8) (mag : Vector Word 4) (x y z : Limbs) :
    RamWriteFrame m (stageSelect m (sp fr) flag mag x y z) (writes fr selectWrites) := by
  unfold stageSelect
  repeat' refine RamWriteFrame.memStore ?_ _ ?_
  exact RamWriteFrame.refl _ _
  all_goals apply peerInSlot e (by decide) <;> decide

end K256.Proofs.Generate.Generator.Multiply.Prepare.Bases
