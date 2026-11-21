import Sha3.Proofs.Permutation.Layout
import Sha3.Proofs.X86.Instructions.Add.Imm8.Triple
import Sha3.Proofs.X86.Instructions.Cmp.Imm32.Triple
import X86Proofs.Instructions.Branch.Triple

namespace Sha3.Proofs.Permutation.RoundMachine

open X86 X86.Machine X86.UserProcess X86Proofs Prelude

theorem control_add_step [Bindings] (copy : Copy) :
    StepEffect (fun s ↦ s.RIP = (entryAddress copy + 0x4fa : BitVec 64))
      (codeRange (entryAddress copy + 0x4fa) [0x48, 0x83, 0xc2, 0x08])
      (addR64Imm8Effect (entryAddress copy + 0x4fa) 2 0x8) := by
  exact add_r64_imm8_effect_step (entryAddress copy + 0x4fa) 0x48 0xc2 0x8
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem control_cmp_step [Bindings] (copy : Copy) :
    StepEffect (fun s ↦ s.RIP = (entryAddress copy + 0x4fe : BitVec 64))
      (codeRange (entryAddress copy + 0x4fe) [0x48, 0x81, 0xfa, 0xc0, 0x00, 0x00, 0x00])
      (cmpR64Imm32Effect (entryAddress copy + 0x4fe) 2 0xc0) := by
  exact cmp_r64_imm32_effect_step (entryAddress copy + 0x4fe) 0x48 0xfa 0xc0
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem control_jne_step [Bindings] (copy : Copy) :
    StepEffect (fun s ↦ s.RIP = (entryAddress copy + 0x505 : BitVec 64))
      (codeRange (entryAddress copy + 0x505) [0x0f, 0x85, 0xe5, 0xfb, 0xff, 0xff])
      (jccEffect (entryAddress copy + 0x505) 6 5 0xfffffffffffffbe5) := by
  exact (jcc_rel32_effect_step (entryAddress copy + 0x505) 5 0xfffffbe5).mono_pre
    (fun _ hp ↦ ⟨hp, fun _ ↦ by cases copy <;> decide +kernel⟩)

end Sha3.Proofs.Permutation.RoundMachine
