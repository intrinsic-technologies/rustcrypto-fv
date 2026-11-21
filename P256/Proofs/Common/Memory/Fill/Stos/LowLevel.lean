import P256.Proofs.Common.Memory.Fill.Stos.LowLevel.Decode
import P256.Proofs.Common.Memory.Fill.Stos.LowLevel.Form
import P256.Proofs.Common.Memory.Fill.Stos.LowLevel.Step
import P256.Proofs.Common.Memory.Fill.Stos.Loop

namespace P256.Proofs.Common.Memory.Fill.Stos

open X86Proofs X86 X86.Machine X86.UserProcess

theorem rep_stosb_instruction [inst : Bindings] (hstride : Prelude.UnitStringStride inst) :
    StosInstruction 1 [0xf3, 0xaa] := by
  refine ⟨by decide, by decide, by decide, by decide, ?_, ?_⟩
  · intro s h hdf hcode hlow hcount hdst _ hmem
    exact rep_stosb_step hstride s h hdf hcode hlow hcount hdst hmem
  · exact rep_stosb_step_zero

theorem rep_stosq_instruction [inst : Bindings] (hstride : Prelude.UnitStringStride inst) :
    StosInstruction 8 [0xf3, 0x48, 0xab] := by
  refine ⟨by decide, by decide, by decide, by decide, ?_, ?_⟩
  · intro s h hdf hcode hlow hcount hdst halign hmem
    exact rep_stosq_step hstride s h hdf hcode hlow hcount hdst (by omega) hmem
  · exact rep_stosq_step_zero

end P256.Proofs.Common.Memory.Fill.Stos
