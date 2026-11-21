import P256.Proofs.Verifying.Wrapper.KeyCall

set_option autoImplicit false

namespace P256.Proofs.Verifying.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem key_decoder_entry [bindings : Bindings] {initial : RamState}
    {key signature message : ByteArray} {slices : Array Input}
    (hb : MachineRamUnitStrideDecodable bindings initial)
    (hm : SupportedIntegerMachineState bindings.processor initial)
    (call : ValidCallWithSlices verifyingKeyVerify initial [key, signature, message] slices) :
    ∃ s t, KeyCopied initial s key ∧ Sec1.DecodePre t (returnBoundary initial) key ∧
      t.regValue .rdi = stackPtr initial-208 ∧ stackPtr t = stackPtr initial-288 ∧
      (returnBoundary t).rip = 0x1030f8 ∧
      AgreesExcept (keyCallComponents initial) s t ∧
      ∃ fuel, Advances (returnBoundary initial) fuel initial t := by
  obtain ⟨s,state⟩ := copy_key hb hm call
  obtain ⟨t,pre,output,sp,ret,frame,n,run⟩ :=
    enter_key_decoder call state (outer_boundary call hm hb)
  obtain ⟨nf,first⟩ := state.execution
  exact ⟨s,t,state,pre,output,sp,ret,frame,nf+n,first.trans run⟩

end P256.Proofs.Verifying.Wrapper
