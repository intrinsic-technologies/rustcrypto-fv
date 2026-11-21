import P256.Proofs.Signing.Wrapper.Entry.Decode.Finish
import P256.Proofs.ReadBe.Correct

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Entry

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem decode_correct : DecodeContract := by
  intro bindings initial s secret message context guarded
  obtain ⟨n,a,ha,entry⟩ := Decode.enter_decoder context guarded
  obtain ⟨b,result⟩ := ReadBe.read_be_correct entry.pre entry.bytes
  obtain ⟨m,hb⟩ := result.execution
  have read := Decode.read_result context entry result
  obtain ⟨k,c,hc,range⟩ := Decode.scalar_range context read
  obtain ⟨d,hd,valid⟩ := Decode.valid_branch context range
  obtain ⟨l,e,he,equalEntry⟩ := Decode.equal_entry context valid
  obtain ⟨o,f,hf,equal⟩ := Decode.equal_call context equalEntry
  obtain ⟨g,hg,nonzero⟩ := Decode.check_zero context equal
  obtain ⟨p,t,ht,decoded⟩ := Decode.finish context nonzero
  exact ⟨n+m+k+8+l+o+10+p,t,
    ((((((ha.trans hb).trans hc).trans hd).trans he).trans hf).trans hg).trans ht,decoded⟩

end P256.Proofs.Signing.Wrapper.Entry
