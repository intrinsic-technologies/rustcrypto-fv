import Md5.Proofs.Buffered.Finalize.Contracts
import Md5.Proofs.Buffered.Finalize.Algebra

namespace Md5.Proofs.Buffered.Finalize.Digest.Finish

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Post [Bindings] (boundary : ReturnBoundary) (message : ByteArray)
    (buffer : Standards.RFC.MD5.Buffer) (s t : RamState) : Prop where
  advances : ∃ fuel, Advances boundary fuel s t
  ready : ReadyToStep t
  code : CodeIn Extracted.programImage t
  rip : t.RIP = 0x100260
  rsp : stackPtr t = stackPtr s
  output : (⟨(stackPtr s + 8).toNat, 16⟩ : MemoryRegion).HasBytes t.external
    ⟨(Standards.RFC.MD5.processBlocks buffer (Standards.RFC.MD5.wordsOfBytes (lastBlock message))).toBytes.toArray⟩
  agrees : AgreesExcept (Kind.digest.changes s) s t

end Md5.Proofs.Buffered.Finalize.Digest.Finish
