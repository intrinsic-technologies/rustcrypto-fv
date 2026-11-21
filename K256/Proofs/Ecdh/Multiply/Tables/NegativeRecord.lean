import K256.Proofs.Ecdh.Multiply.Bases.Frame
import K256.Proofs.Generate.Generator.Multiply.Prepare.Tables.NegativeRecord

namespace K256.Proofs.Generate.Generator.Multiply.Prepare.Table

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Tactic K256.Proofs.Generate.LIR
  K256.Proofs.Common.Field Common.Point.TableWords

theorem peerNegativeRecord_frame {fr : Activation} {a : Registers} {d : Nat} {peer : Projective} (e : PeerCoreEntry fr a d peer)
    (m : Ram) (x y z : Limbs) :
    RamWriteFrame m (negativeRecord m (sp fr) x y z) (Bases.writes fr [(808,120)]) := by
  unfold negativeRecord
  refine RamWriteFrame.memStore ?_ _ (Bases.peerInSlot e (xs := [(808,120)]) (i := 880) (size := 8) (by decide) (by decide))
  refine RamWriteFrame.memStore ?_ _ (Bases.peerInSlot e (xs := [(808,120)]) (i := 872) (size := 8) (by decide) (by decide))
  refine RamWriteFrame.memStore ?_ _ (Bases.peerInSlot e (xs := [(808,120)]) (i := 864) (size := 8) (by decide) (by decide))
  refine RamWriteFrame.memStore ?_ _ (Bases.peerInSlot e (xs := [(808,120)]) (i := 856) (size := 8) (by decide) (by decide))
  refine RamWriteFrame.memStore ?_ _ (Bases.peerInSlot e (xs := [(808,120)]) (i := 848) (size := 8) (by decide) (by decide))
  refine RamWriteFrame.memStore ?_ _ (Bases.peerInSlot e (xs := [(808,120)]) (i := 888) (size := 8) (by decide) (by decide))
  refine RamWriteFrame.memStore ?_ _ (Bases.peerInSlot e (xs := [(808,120)]) (i := 896) (size := 8) (by decide) (by decide))
  refine RamWriteFrame.memStore ?_ _ (Bases.peerInSlot e (xs := [(808,120)]) (i := 904) (size := 8) (by decide) (by decide))
  refine RamWriteFrame.memStore ?_ _ (Bases.peerInSlot e (xs := [(808,120)]) (i := 912) (size := 8) (by decide) (by decide))
  refine RamWriteFrame.memStore ?_ _ (Bases.peerInSlot e (xs := [(808,120)]) (i := 920) (size := 8) (by decide) (by decide))
  refine RamWriteFrame.memStore ?_ _ (Bases.peerInSlot e (xs := [(808,120)]) (i := 808) (size := 8) (by decide) (by decide))
  refine RamWriteFrame.memStore ?_ _ (Bases.peerInSlot e (xs := [(808,120)]) (i := 816) (size := 8) (by decide) (by decide))
  refine RamWriteFrame.memStore ?_ _ (Bases.peerInSlot e (xs := [(808,120)]) (i := 824) (size := 8) (by decide) (by decide))
  refine RamWriteFrame.memStore ?_ _ (Bases.peerInSlot e (xs := [(808,120)]) (i := 832) (size := 8) (by decide) (by decide))
  refine RamWriteFrame.memStore ?_ _ (Bases.peerInSlot e (xs := [(808,120)]) (i := 840) (size := 8) (by decide) (by decide))
  exact RamWriteFrame.refl _ _

end K256.Proofs.Generate.Generator.Multiply.Prepare.Table
