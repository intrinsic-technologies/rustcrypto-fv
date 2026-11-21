import P256.Proofs.Sec1.Decompress.Input.ConvertEntry
import P256.Proofs.Sec1.Decompress.Convert

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decompress.Input

open P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Standards.SECG.ECC

structure Converted [Bindings] (s t : RamState) (x : Nat) (odd : Bool) : Prop
    extends Frame s t where
  rip : t.RIP = 0x10fcf4
  parity : memLoad t.external (stackPtr s - 332) 32 = BitVec.ofNat 32 odd.toNat
  output : memLoad t.external (stackPtr s - 224) 64 = s.regValue .rdi
  valid : t.regValue .rbx = if x < P256.Spec.Operations.domain.p then 1 else 0
  r14 : t.regValue .r14 = 0xffffffff00000001
  r15 : t.regValue .r15 = stackPtr s - 408
  value : Field.MontgomeryAt t (stackPtr s - 408) (x % P256.Spec.Operations.domain.p)

theorem conversion_result [Bindings] {s entry : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} {odd : Bool} (pre : Pre s boundary bytes odd)
    (state : ConversionEntry s entry boundary (Encoding.octetsToNat bytes) odd) :
    ∃ fuel t, Advances boundary fuel entry t ∧
      Converted s t (Encoding.octetsToNat bytes) odd := by
  obtain ⟨t, result, value⟩ := Convert.convert_correct state.pre state.raw
  obtain ⟨fuel, run⟩ := result.execution
  refine ⟨fuel, t, run, ⟨stack_result_frame pre state.toFrameState state.output
    (by decide) (by decide) (by decide) result, result.rip.trans state.ret,
    ?_, ?_, (result.calleeSaved .rbx (by simp)).trans state.valid,
    (result.calleeSaved .r14 (by simp)).trans state.r14,
    (result.calleeSaved .r15 (by simp)).trans state.r15, ?_⟩⟩
  · exact (stack_result_read pre state.rsp state.output result (offset := 332) (n := 32)
      (by decide) (by decide) (by decide) (.inl (by decide))).trans state.parity
  · exact (stack_result_read pre state.rsp state.output result (offset := 224) (n := 64)
      (by decide) (by decide) (by decide) (.inl (by decide))).trans state.savedOutput
  · simpa only [state.output] using value

end P256.Proofs.Sec1.Decompress.Input
