import K256.Proofs.Sec1.Affine.DecodeCall
import K256.Proofs.Ecdh.Decode.Repr

namespace K256.Proofs.Ecdh.Decode.Affine

open Prelude X86.Machine X86.UserProcess X86Proofs K256.Spec.Program
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine

structure Entry (fr : Activation) (args : Values Value Reg.count) (m : Ram) (bytes : ByteArray) : Prop where
  rsp : args[4] = ⟨64,fr.rsp⟩
  src : args[6] = ⟨64,fr.rsi⟩
  dst : args[7] = ⟨64,fr.rdi⟩
  r8 : args[8].width = 64
  r9 : args[9].width = 64
  df : args[22] = ⟨1,0⟩
  saved : ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15,39,50,51] → args[i] = fr.entryValue i.val
  window : Writable Extracted.programImage m (fr.rsp - 1192) 1192
  low : fr.low.toNat + 1192 ≤ fr.rsp.toNat
  align : fr.rsp.toNat % 16 = 8
  slot : Readable m fr.rsp 8
  ret : memLoad m fr.rsp 64 = fr.ret
  retLow : fr.ret.toNat < 2^32
  input : Readable m fr.rsi 65
  bytesAt : ∀ i < 65, memByte m (fr.rsi + BitVec.ofNat 64 i) = bytes.data[i]?.getD 0
  output : Writable Extracted.programImage m fr.rdi 89
  srcAbove : fr.rsp.toNat + 8 ≤ fr.rsi.toNat
  dstAbove : fr.rsp.toNat + 8 ≤ fr.rdi.toNat
  image : ∀ x ∈ Extracted.programImage, m[x.1]? = some x.2
  text : fr.rsp.toNat - 136 ≤ 0x100000 ∨ 0x12aa00 ≤ fr.rsp.toNat - 1192

end K256.Proofs.Ecdh.Decode.Affine
