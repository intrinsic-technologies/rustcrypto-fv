import Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Compression

namespace Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Padding

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Block

def longCall : Variant → BitVec 64
  | .original => 0x100b82
  | .finalize => 0x101212
  | .discard => 0x1016fe

def clearEntry : Variant → BitVec 64
  | .original => 0x100b87
  | .finalize => 0x101217
  | .discard => 0x101703

theorem compress [Bindings] {variant : Variant} {boundary : ReturnBoundary} {s : RamState}
    {buffer : Standards.RFC.MD5.Buffer} {input : ByteArray}
    (hp : FinalizeReset.CompressCall.Pre buffer input s) (hr : ReadyToStep s)
    (hc : CodeIn Extracted.programImage s) (hout : ¬ InProgram boundary.rip)
    (hip : s.RIP = longCall variant) :
    ∃ t, FinalizeReset.CompressCall.Post boundary (clearEntry variant) buffer input s t := by
  cases variant
  case original =>
    exact FinalizeReset.CompressCall.run_of_step
      (Buffered.Stack.call_rel32_effect_step 0x100b82 0x1019 (by decide +kernel)) hr hc
      (program_text_slice hc 0xb82 5 (by decide +kernel)) ⟨hip, hp.pushWritable⟩ hp
      (by decide +kernel) (by decide) (Or.inl (by decide)) hout
      (text_address_ne_return hout 0xb87 (by decide +kernel))
  case finalize =>
    exact FinalizeReset.CompressCall.run_of_step
      (Buffered.Stack.call_rel32_effect_step 0x101212 0x989 (by decide +kernel)) hr hc
      (program_text_slice hc 0x1212 5 (by decide +kernel)) ⟨hip, hp.pushWritable⟩ hp
      (by decide +kernel) (by decide) (Or.inl (by decide)) hout
      (text_address_ne_return hout 0x1217 (by decide +kernel))
  case discard =>
    exact FinalizeReset.CompressCall.run_of_step
      (Buffered.Stack.call_rel32_effect_step 0x1016fe 0x49d (by decide +kernel)) hr hc
      (program_text_slice hc 0x16fe 5 (by decide +kernel)) ⟨hip, hp.pushWritable⟩ hp
      (by decide +kernel) (by decide) (Or.inl (by decide)) hout
      (text_address_ne_return hout 0x1703 (by decide +kernel))

end Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Padding
