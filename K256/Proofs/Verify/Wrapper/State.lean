import K256.Proofs.Verify.Wrapper.PublicKey
import K256.Proofs.Verify.Core.State
import K256.Proofs.Verify.Hash.Update.State
import K256.Proofs.Verify.Hash.Padding.Compression

namespace K256.Proofs.Verify.Wrapper

open K256.Spec K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  CFG Lift Refine Verify.LIR Standards.SECG.ECC
open Generate.Generator.Multiply (scalarWords Projective)

structure Frame (initial : RamState) (a : Core.Registers) (m : Ram) : Prop where
  memory : Memory initial m
  rsp : a[4] = ⟨64, localSp initial⟩
  rbp : a[5] = (Reg.ofIndex 5).read initial
  r13 : a[13] = (Reg.ofIndex 13).read initial
  df : a[22] = ⟨1, 0⟩
  r12Width : a[12].width = 64
  mxcsr : a[39].width = 32
  ftw : a[50].width = 16
  fcw : a[51].width = 16

structure AffineInputs (initial : RamState) (m : Ram) (p : Curve.Point) (r s : Nat)
    (rOffset : BitVec 64) : Prop where
  point : Ecdh.Decode.AffinePointAt m (localSp initial + 416) p
  rAt : WordsAt m (localSp initial + rOffset) 64 (scalarWords r)
  sAt : WordsAt m (localSp initial + (rOffset + 32)) 64 (scalarWords s)

structure HashInput (initial : RamState) (a : Core.Registers) (m : Ram)
    (p : Curve.Point) (r s : Nat) : Prop extends Frame initial a m where
  operands : AffineInputs initial m p r s 16
  length : a[3] = ⟨64, initial.regValue .rdx⟩
  source : a[14] = ⟨64, initial.regValue .rsi⟩

structure HashBuffer (initial : RamState) (a : Core.Registers) (m : Ram)
    (p : Curve.Point) (r s : Nat) (msg : ByteArray) : Prop extends Frame initial a m where
  operands : AffineInputs initial m p r s 352
  state : Hash.Compression.StateAt m (localSp initial + 312) (Hash.compressBlocks Hash.initialHash msg)
  bytes : (⟨(localSp initial + 248).toNat, msg.size % 64⟩ : MemoryRegion).HasBytes m
    (Hash.remainderBytes msg)
  pos : memLoad m (localSp initial + 311) 8 = BitVec.ofNat 8 (msg.size % 64)
  count : memLoad m (localSp initial + 344) 64 = BitVec.ofNat 64 (msg.size / 64)

structure HashOutput (initial : RamState) (a : Core.Registers) (m : Ram)
    (p : Curve.Point) (r s : Nat) (msg : ByteArray) : Prop extends Frame initial a m where
  operands : AffineInputs initial m p r s 352
  state : Hash.Compression.StateAt m (localSp initial + 72)
    (Hash.compressBlocks Hash.initialHash (Hash.bytePadding msg))
  r14Width : a[14].width = 64
  r15Width : a[15].width = 64

structure VerificationInput (initial : RamState) (a : Core.Registers) (m : Ram)
    (p : Curve.Point) (r s : Nat) (digest : ByteArray) : Prop extends Frame initial a m where
  keyPtr : a[3] = ⟨64, localSp initial + 8⟩
  peer : ∃ q : Projective, q.Stored m (localSp initial + 8) ∧ q.valid ∧ q.value = p
  hash : (⟨(localSp initial + 128).toNat, 32⟩ : MemoryRegion).HasBytes m digest
  rAt : WordsAt m (localSp initial + 352) 64 (scalarWords r)
  sAt : WordsAt m (localSp initial + 384) 64 (scalarWords s)
  r9Width : a[9].width = 64
  r14Width : a[14].width = 64
  r15Width : a[15].width = 64

end K256.Proofs.Verify.Wrapper
