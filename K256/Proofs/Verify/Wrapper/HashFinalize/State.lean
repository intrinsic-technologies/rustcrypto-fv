import K256.Proofs.Verify.Wrapper.OperandFrame
import K256.Proofs.Verify.Hash.FinalBlocks.Frame
import K256.Proofs.Verify.Hash.FinalBlocks.Bytes
import K256.Proofs.Verify.Hash.FinalBlocks.Branch
import K256.Proofs.Verify.Hash.Update.Compress

namespace K256.Proofs.Verify.Wrapper.HashFinalize

open K256.Spec K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  CFG Lift Refine Verify.LIR Standards.SECG.ECC

structure State (initial : RamState) (a : Core.Registers) (m : Ram)
    (p : Curve.Point) (r s : Nat) (msg : ByteArray) (hash : Array UInt32) : Prop
    extends Frame initial a m where
  operands : AffineInputs initial m p r s 352
  state : Hash.Compression.StateAt m (localSp initial + 72) hash
  rbx : a[3] = ⟨64, localSp initial + 72⟩
  r14Width : a[14].width = 64
  length : a[15] = ⟨64, bswapSpec (BitVec.ofNat 64 (8 * msg.size))⟩

end K256.Proofs.Verify.Wrapper.HashFinalize
