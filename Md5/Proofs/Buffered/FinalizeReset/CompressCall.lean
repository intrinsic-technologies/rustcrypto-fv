import Md5.Proofs.Buffered.FinalizeReset.CompressCall.Frame

namespace Md5.Proofs.Buffered.FinalizeReset.CompressCall

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem run_of_step [Bindings] {boundary : ReturnBoundary}
    {ret : BitVec 64} {target : RamState → BitVec 64}
    {buffer : Standards.RFC.MD5.Buffer} {input : ByteArray} {s : RamState}
    {pre : RamState → Prop} {code : CodeMap}
    (hstep : StepEffect pre code (callEffect target ret))
    (hready : ReadyToStep s) (hcode : CodeIn Extracted.programImage s)
    (hbytes : CodeIn code s) (hpre : pre s) (hp : Pre buffer input s)
    (htarget : target s = 0x101ba0) (hretLow : ret.toNat < userAddressLimit)
    (hretOutside : Block.OutsideCompression ret)
    (hOutside : ¬ InProgram boundary.rip) (hretNe : ret ≠ boundary.rip) :
    ∃ t, Post boundary ret buffer input s t := by
  have hentryNe : (0x101ba0 : BitVec 64) ≠ boundary.rip :=
    Block.text_address_ne_return hOutside 0x1ba0 (by decide +kernel)
  obtain ⟨u, hcall, hu, he⟩ :=
    hstep.advances hready hbytes hpre (htarget ▸ hentryNe)
  have hreturn := callEffect_returnBoundary he
  obtain ⟨hInput, hBuffer, hStack, hSeparation⟩ := hp.after_call he
  obtain ⟨fuel, t, hbody, hrip, hrsp, hready', hcode', hagrees, houtput⟩ :=
    Block.compress_subroutine_advance boundary hu (callEffect_code he hcode hp.pushCode)
      (he.rip.trans htarget) hInput hBuffer hStack hSeparation
      (by rw [hreturn]; exact hretLow) (by rw [hreturn]; exact hretOutside)
      (Block.outsideCompression_of_not_inProgram hOutside)
      (by rw [hreturn]; exact Ne.symm hretNe)
  rw [hreturn] at hrip hrsp
  have hdi : u.regValue .rdi = s.regValue .rdi := callEffect_read he (r := 7) (by decide)
  refine ⟨t, ⟨⟨1 + fuel, hcall.trans hbody⟩, hready', hcode', hrip, hrsp, ?_,
    call_return_agrees hp he hagrees hrsp⟩⟩
  have hout := Block.readOutput_eq_ok_iff.mp houtput
  simpa only [Compress.outputRegion, registerRegion, hdi] using hout

end Md5.Proofs.Buffered.FinalizeReset.CompressCall
