import Hkdf.Proofs.Standard.Finalize.Frame

set_option autoImplicit false

namespace Hkdf.Proofs.Standard.Finalize

open Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.CallFrame Hkdf.Proofs.Common.Machine

structure DigestReady [Bindings] (initial s : RamState) (digest : ByteArray) : Prop
    extends State initial s where
  rip : s.RIP = 0x10174c
  rsp : stackPtr s = frameBase initial
  outputPointer : memLoad s.external (frameBase initial + 96) 64 = initial.regValue .r9
  bytes : (⟨(hmacBase initial).toNat, 32⟩ : MemoryRegion).HasBytes s.external digest

variable [Bindings] {initial s t : RamState} {salt : Option ByteArray}
  {inputs : Array Input} {digest : ByteArray}

theorem digest_ready_of_callee (ctx : Context initial salt inputs) (state : State initial s)
    (result : CalleeResult s t (returnBoundary initial) 176 1264)
    (rsp : stackPtr s = stackPtr initial - 528)
    (output : s.regValue .rdi = stackPtr initial - 400)
    (boundary : returnBoundary s = ⟨0x10174c, frameBase initial⟩)
    (pointer : memLoad s.external (frameBase initial + 96) 64 = initial.regValue .r9)
    (bytes : (registerRegion s .rdi 32).HasBytes t.external digest) :
    DigestReady initial t digest := by
  have target : s.regValue .rdi = hmacBase initial := by
    rw [output]
    change stackPtr initial - 400 = stackPtr initial - 520 + 120
    bv_omega
  have persistent := finalizer_persistent ctx result.frame rsp output 96 (by simp)
  refine ⟨finalizer_state ctx state result rsp output, ?_, ?_, ?_, ?_⟩
  · exact result.rip.trans (congrArg ReturnBoundary.rip boundary)
  · exact result.rsp.trans (congrArg ReturnBoundary.rsp boundary)
  · exact (agrees_memLoad persistent).trans pointer
  · simpa only [registerRegion, target] using bytes

end Hkdf.Proofs.Standard.Finalize
