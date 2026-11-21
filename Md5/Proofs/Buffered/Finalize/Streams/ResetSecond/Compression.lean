import Md5.Proofs.Buffered.Finalize.Compression
import Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Contracts

namespace Md5.Proofs.Buffered.Finalize.Streams.ResetSecond

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Block

namespace Compression

theorem run [Bindings] {variant : Variant} {boundary : ReturnBoundary} {s : RamState}
    {buffer : Standards.RFC.MD5.Buffer} {input : ByteArray}
    (hp : FinalizeReset.CompressCall.Pre buffer input s) (hr : ReadyToStep s)
    (hc : CodeIn Extracted.programImage s) (hout : ¬ InProgram boundary.rip)
    (hip : s.RIP = variant.finalCall) :
    ∃ t, FinalizeReset.CompressCall.Post boundary variant.toKind.exit buffer input s t := by
  cases variant
  case original =>
    exact FinalizeReset.CompressCall.run_of_step
      (Buffered.Stack.call_rel32_effect_step 0x100c63 0xf38 (by decide +kernel)) hr hc
      (program_text_slice hc 0xc63 5 (by decide +kernel)) ⟨hip, hp.pushWritable⟩ hp
      (by decide +kernel) (by decide) (Or.inl (by decide)) hout
      (text_address_ne_return hout 0xc68 (by decide +kernel))
  case finalize =>
    exact FinalizeReset.CompressCall.run_of_step
      (Buffered.Stack.call_rel32_effect_step 0x1012f3 0x8a8 (by decide +kernel)) hr hc
      (program_text_slice hc 0x12f3 5 (by decide +kernel)) ⟨hip, hp.pushWritable⟩ hp
      (by decide +kernel) (by decide) (Or.inl (by decide)) hout
      (text_address_ne_return hout 0x12f8 (by decide +kernel))
  case discard =>
    exact FinalizeReset.CompressCall.run_of_step
      (Buffered.Stack.call_rel32_effect_step 0x1017f4 0x3a7 (by decide +kernel)) hr hc
      (program_text_slice hc 0x17f4 5 (by decide +kernel)) ⟨hip, hp.pushWritable⟩ hp
      (by decide +kernel) (by decide) (Or.inl (by decide)) hout
      (text_address_ne_return hout 0x17f9 (by decide +kernel))

theorem agrees {variant : Variant} {s t : RamState} (hdi : s.regValue .rdi = stackPtr s + BitVec.ofNat 64 variant.resultOffset)
    (ha : AgreesExcept (FinalizeReset.CompressCall.changes s) s t) :
    AgreesExcept (variant.toKind.changes s) s t := by
  apply ha.widen
  · intro c hc hm
    simp only [FinalizeReset.CompressCall.changes, hdi, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals cases variant <;> simp_all [Variant.toKind, Variant.resultOffset, Component.isMem, Kind.changes, Kind.workRegisters, Kind.localChanges]
  · intro address c hc ha
    simp only [FinalizeReset.CompressCall.changes, hdi, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    · obtain ⟨i, hi, he⟩ := ha
      cases variant with
      | original | finalize =>
        exact ⟨.mem (stackPtr s + 216) 80,
          by simp [Variant.toKind, Kind.changes, Kind.localChanges], i, by omega, he⟩
      | discard =>
        exact ⟨.mem (stackPtr s + 120) 168,
          by simp [Variant.toKind, Kind.changes, Kind.localChanges], i, by omega, he⟩
    · exact ⟨.mem (stackPtr s - 320) 320, by simp [Kind.changes], ha⟩

end Compression

end Md5.Proofs.Buffered.Finalize.Streams.ResetSecond
