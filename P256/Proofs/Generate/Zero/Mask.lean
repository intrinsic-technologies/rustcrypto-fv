import P256.Proofs.Common.Instructions.ByteOps.Effects
import P256.Proofs.Common.Instructions.MovzxByte
import P256.Proofs.Program.Code
import X86Proofs.Program.Execution

set_option autoImplicit false

namespace P256.Proofs.Generate.Zero

open P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions.ByteOps.ByteOps
open P256.Proofs.Common.Instructions.MovzxByte

def maskBytes : List UInt8 := [0x24, 1, 0x0f, 0xb6, 0xf8]

theorem mask_arguments [Bindings] {s : RamState} (boundary : ReturnBoundary)
    (pc : BitVec 64) (ready : ReadyToStep s)
    (code : CodeIn (codeRange pc maskBytes) s) (rip : s.RIP = pc)
    (outside2 : pc + 2#64 ≠ boundary.rip) (outside5 : pc + 5#64 ≠ boundary.rip) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧
      AgreesExcept [.reg 0, .reg 7, .flags, .rip] s t ∧ t.RIP = pc+5#64 ∧
      t.regValue .rdi = (((s.regValue .rax).setWidth 8 &&& 1).setWidth 64) := by
  obtain ⟨u, runU, readyU, effectU⟩ := (and_al_imm8_effect_step pc 1).advances ready
    (code.mono (codeRange_mem_of_take (by decide +kernel))) rip outside2
  have codeU : CodeIn (codeRange pc maskBytes) u :=
    effectU.codeIn (andAlImm8Effect_avoids _ _ _ _) code
  have pc2 : u.RIP = pc+2#64 := effectU.rip
  obtain ⟨t, runT, readyT, effectT⟩ :=
    (movzx_r32_r8_effect_step (pc+2#64) 0xf8 rfl (by decide)).advances readyU
      (codeU.mono (codeRange_slice_subset pc maskBytes 2 3)) pc2
      (by simpa only [movzxR32R8Effect, BitVec.add_assoc, BitVec.reduceAdd] using outside5)
  refine ⟨t, runU.trans runT, readyT, ?_, ?_, ?_⟩
  · exact (effectU.agrees.trans effectT.agrees).mono (by
      simp [andAlImm8Effect, movzxR32R8Effect, Effect.components]
      decide)
  · simpa only [movzxR32R8Effect, BitVec.add_assoc, BitVec.reduceAdd] using effectT.rip
  · have hv := effectT.writes
    change t.regValue .rdi = (((Operand.reg 0 : Operand 64).read u).setWidth 8).setWidth 64 at hv
    rw [effectU.writes, mergeGPR_low8] at hv
    exact hv

end P256.Proofs.Generate.Zero
