import X86Proofs.Instructions.Mov.Triple
import Sha3.Proofs.X86.Instructions.Xor.Triple
import Sha3.Proofs.X86.Instructions.And.Triple
import Sha3.Proofs.X86.Instructions.Not.Triple
import Sha3.Proofs.X86.Instructions.Rol.Triple

namespace Sha3.Proofs.Permutation.RoundMachine

open X86 X86.Machine X86.UserProcess X86Proofs

theorem step_10010c [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x49, 0x89, 0xe8])
      (movR64R64Effect pc 8 5) := by
  exact mov_r64_r64_effect_step pc 0x49 0xe8
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_10010f [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x49, 0x31, 0xc0])
      (xorR64R64Effect pc 8 0) := by
  exact xor_r64_r64_effect_step pc 0x49 0xc0
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_100112 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x49, 0x31, 0xd0])
      (xorR64R64Effect pc 8 2) := by
  exact xor_r64_r64_effect_step pc 0x49 0xd0
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_10011d [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x4c, 0x31, 0xca])
      (xorR64R64Effect pc 2 9) := by
  exact xor_r64_r64_effect_step pc 0x4c 0xca
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_100120 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x4c, 0x89, 0xfe])
      (movR64R64Effect pc 6 15) := by
  exact mov_r64_r64_effect_step pc 0x4c 0xfe
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_10012d [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x49, 0x31, 0xcf])
      (xorR64R64Effect pc 15 1) := by
  exact xor_r64_r64_effect_step pc 0x49 0xcf
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_100130 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x49, 0x31, 0xd7])
      (xorR64R64Effect pc 15 2) := by
  exact xor_r64_r64_effect_step pc 0x49 0xd7
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_100133 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x48, 0x89, 0xf2])
      (movR64R64Effect pc 2 6) := by
  exact mov_r64_r64_effect_step pc 0x48 0xf2
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_10013b [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x4c, 0x89, 0xe6])
      (movR64R64Effect pc 6 12) := by
  exact mov_r64_r64_effect_step pc 0x4c 0xe6
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_100143 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x48, 0x31, 0xd6])
      (xorR64R64Effect pc 6 2) := by
  exact xor_r64_r64_effect_step pc 0x48 0xd6
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_100146 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x48, 0x89, 0xdf])
      (movR64R64Effect pc 7 3) := by
  exact mov_r64_r64_effect_step pc 0x48 0xdf
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_100151 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x4c, 0x89, 0xf3])
      (movR64R64Effect pc 3 14) := by
  exact mov_r64_r64_effect_step pc 0x4c 0xf3
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_10015e [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x49, 0x89, 0xc5])
      (movR64R64Effect pc 13 0) := by
  exact mov_r64_r64_effect_step pc 0x49 0xc5
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_100161 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x48, 0x89, 0xd0])
      (movR64R64Effect pc 0 2) := by
  exact mov_r64_r64_effect_step pc 0x48 0xd0
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_100169 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x48, 0x31, 0xd8])
      (xorR64R64Effect pc 0 3) := by
  exact xor_r64_r64_effect_step pc 0x48 0xd8
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_10016c [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x48, 0x89, 0xfb])
      (movR64R64Effect pc 3 7) := by
  exact mov_r64_r64_effect_step pc 0x48 0xfb
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_10017d [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x48, 0x31, 0xdf])
      (xorR64R64Effect pc 7 3) := by
  exact xor_r64_r64_effect_step pc 0x48 0xdf
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_100185 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x49, 0x31, 0xd8])
      (xorR64R64Effect pc 8 3) := by
  exact xor_r64_r64_effect_step pc 0x49 0xd8
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_100188 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x49, 0x89, 0xca])
      (movR64R64Effect pc 10 1) := by
  exact mov_r64_r64_effect_step pc 0x49 0xca
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_100190 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x49, 0x31, 0xcf])
      (xorR64R64Effect pc 15 1) := by
  exact xor_r64_r64_effect_step pc 0x49 0xcf
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_100193 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x4c, 0x31, 0xd8])
      (xorR64R64Effect pc 0 11) := by
  exact xor_r64_r64_effect_step pc 0x4c 0xd8
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_100196 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x48, 0x89, 0xc2])
      (movR64R64Effect pc 2 0) := by
  exact mov_r64_r64_effect_step pc 0x48 0xc2
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_100199 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x48, 0xd1, 0xc2])
      (rolR64Effect pc 3 2 1) := by
  exact rol_r64_one_effect_step pc 0x48 0xc2
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_10019c [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x4c, 0x31, 0xfa])
      (xorR64R64Effect pc 2 15) := by
  exact xor_r64_r64_effect_step pc 0x4c 0xfa
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_10019f [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x49, 0xd1, 0xc7])
      (rolR64Effect pc 3 15 1) := by
  exact rol_r64_one_effect_step pc 0x49 0xc7
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_1001a7 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x4c, 0x31, 0xf7])
      (xorR64R64Effect pc 7 14) := by
  exact xor_r64_r64_effect_step pc 0x4c 0xf7
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_1001aa [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x49, 0x31, 0xff])
      (xorR64R64Effect pc 15 7) := by
  exact xor_r64_r64_effect_step pc 0x49 0xff
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_1001ad [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x4c, 0x31, 0xfb])
      (xorR64R64Effect pc 3 15) := by
  exact xor_r64_r64_effect_step pc 0x4c 0xfb
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_1001bd [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x4d, 0x31, 0xfd])
      (xorR64R64Effect pc 13 15) := by
  exact xor_r64_r64_effect_step pc 0x4d 0xfd
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_1001c8 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x4c, 0x31, 0xfd])
      (xorR64R64Effect pc 5 15) := by
  exact xor_r64_r64_effect_step pc 0x4c 0xfd
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_1001e0 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x4c, 0x31, 0xfe])
      (xorR64R64Effect pc 6 15) := by
  exact xor_r64_r64_effect_step pc 0x4c 0xfe
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_1001e3 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x48, 0xd1, 0xc7])
      (rolR64Effect pc 3 7 1) := by
  exact rol_r64_one_effect_step pc 0x48 0xc7
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_1001e6 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x48, 0x31, 0xf7])
      (xorR64R64Effect pc 7 6) := by
  exact xor_r64_r64_effect_step pc 0x48 0xf7
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_1001e9 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x48, 0xd1, 0xc6])
      (rolR64Effect pc 3 6 1) := by
  exact rol_r64_one_effect_step pc 0x48 0xc6
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_1001ec [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x4c, 0x31, 0xc6])
      (xorR64R64Effect pc 6 8) := by
  exact xor_r64_r64_effect_step pc 0x4c 0xc6
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_1001f7 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x48, 0x31, 0xf3])
      (xorR64R64Effect pc 3 6) := by
  exact xor_r64_r64_effect_step pc 0x48 0xf3
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_1001fa [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x49, 0x31, 0xf1])
      (xorR64R64Effect pc 9 6) := by
  exact xor_r64_r64_effect_step pc 0x49 0xf1
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_1001fd [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x48, 0x31, 0xf1])
      (xorR64R64Effect pc 1 6) := by
  exact xor_r64_r64_effect_step pc 0x48 0xf1
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_100205 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x49, 0x31, 0xf2])
      (xorR64R64Effect pc 10 6) := by
  exact xor_r64_r64_effect_step pc 0x49 0xf2
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_100215 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x49, 0x31, 0xd7])
      (xorR64R64Effect pc 15 2) := by
  exact xor_r64_r64_effect_step pc 0x49 0xd7
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_10021d [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x49, 0x31, 0xd4])
      (xorR64R64Effect pc 12 2) := by
  exact xor_r64_r64_effect_step pc 0x49 0xd4
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_10022a [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x49, 0x89, 0xd5])
      (movR64R64Effect pc 13 2) := by
  exact mov_r64_r64_effect_step pc 0x49 0xd5
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_100232 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x49, 0x31, 0xfa])
      (xorR64R64Effect pc 10 7) := by
  exact xor_r64_r64_effect_step pc 0x49 0xfa
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_100235 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x49, 0x31, 0xfb])
      (xorR64R64Effect pc 11 7) := by
  exact xor_r64_r64_effect_step pc 0x49 0xfb
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_100242 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x48, 0x31, 0xfa])
      (xorR64R64Effect pc 2 7) := by
  exact xor_r64_r64_effect_step pc 0x48 0xfa
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_100245 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x49, 0xd1, 0xc0])
      (rolR64Effect pc 3 8 1) := by
  exact rol_r64_one_effect_step pc 0x49 0xc0
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_100252 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x49, 0x31, 0xc0])
      (xorR64R64Effect pc 8 0) := by
  exact xor_r64_r64_effect_step pc 0x49 0xc0
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_10025a [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x4c, 0x31, 0xc0])
      (xorR64R64Effect pc 0 8) := by
  exact xor_r64_r64_effect_step pc 0x4c 0xc0
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_10025d [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x4d, 0x31, 0xc6])
      (xorR64R64Effect pc 14 8) := by
  exact xor_r64_r64_effect_step pc 0x4d 0xc6
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_10026a [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x4c, 0x31, 0xc7])
      (xorR64R64Effect pc 7 8) := by
  exact xor_r64_r64_effect_step pc 0x4c 0xc7
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_100275 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x48, 0xc1, 0xc2, 0x15])
      (rolR64Effect pc 4 2 21) := by
  exact rol_r64_imm8_effect_step pc 0x48 0xc2 0x15
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_10027d [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x49, 0xc1, 0xc3, 0x37])
      (rolR64Effect pc 4 11 55) := by
  exact rol_r64_imm8_effect_step pc 0x49 0xc3 0x37
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_100281 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x48, 0xc1, 0xc6, 0x02])
      (rolR64Effect pc 4 6 2) := by
  exact rol_r64_imm8_effect_step pc 0x48 0xc6 0x02
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_100285 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x49, 0xc1, 0xc0, 0x0e])
      (rolR64Effect pc 4 8 14) := by
  exact rol_r64_imm8_effect_step pc 0x49 0xc0 0x0e
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_100289 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x48, 0xc1, 0xc5, 0x29])
      (rolR64Effect pc 4 5 41) := by
  exact rol_r64_imm8_effect_step pc 0x48 0xc5 0x29
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_100292 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x49, 0xc1, 0xc4, 0x2b])
      (rolR64Effect pc 4 12 43) := by
  exact rol_r64_imm8_effect_step pc 0x49 0xc4 0x2b
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_100296 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x4c, 0x89, 0xf9])
      (movR64R64Effect pc 1 15) := by
  exact mov_r64_r64_effect_step pc 0x4c 0xf9
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_100299 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x48, 0xc1, 0xc1, 0x3e])
      (rolR64Effect pc 4 1 62) := by
  exact rol_r64_imm8_effect_step pc 0x48 0xc1 0x3e
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_10029d [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x48, 0xc1, 0xc7, 0x27])
      (rolR64Effect pc 4 7 39) := by
  exact rol_r64_imm8_effect_step pc 0x48 0xc7 0x27
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_1002a9 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x49, 0xc1, 0xc1, 0x2c])
      (rolR64Effect pc 4 9 44) := by
  exact rol_r64_imm8_effect_step pc 0x49 0xc1 0x2c
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_1002ad [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x4c, 0x89, 0xc8])
      (movR64R64Effect pc 0 9) := by
  exact mov_r64_r64_effect_step pc 0x4c 0xc8
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_1002b0 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x48, 0xf7, 0xd0])
      (notR64Effect pc 0) := by
  exact not_r64_effect_step pc 0x48 0xd0
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_1002b3 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x4c, 0x21, 0xe0])
      (andR64R64Effect pc 0 12) := by
  exact and_r64_r64_effect_step pc 0x4c 0xe0
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_1002bb [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x48, 0x89, 0xd0])
      (movR64R64Effect pc 0 2) := by
  exact mov_r64_r64_effect_step pc 0x48 0xd0
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_1002be [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x48, 0xf7, 0xd2])
      (notR64Effect pc 2) := by
  exact not_r64_effect_step pc 0x48 0xd2
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_1002c1 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x4c, 0x21, 0xc2])
      (andR64R64Effect pc 2 8) := by
  exact and_r64_r64_effect_step pc 0x4c 0xc2
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_1002c4 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x4c, 0x31, 0xe2])
      (xorR64R64Effect pc 2 12) := by
  exact xor_r64_r64_effect_step pc 0x4c 0xe2
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_1002cf [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x49, 0xf7, 0xd4])
      (notR64Effect pc 12) := by
  exact not_r64_effect_step pc 0x49 0xd4
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_1002d2 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x49, 0x21, 0xc4])
      (andR64R64Effect pc 12 0) := by
  exact and_r64_r64_effect_step pc 0x49 0xc4
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_1002d5 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x49, 0x89, 0xc6])
      (movR64R64Effect pc 14 0) := by
  exact mov_r64_r64_effect_step pc 0x49 0xc6
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_1002d8 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x4d, 0x31, 0xcc])
      (xorR64R64Effect pc 12 9) := by
  exact xor_r64_r64_effect_step pc 0x4d 0xcc
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_1002eb [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x4c, 0x89, 0xe3])
      (movR64R64Effect pc 3 12) := by
  exact mov_r64_r64_effect_step pc 0x4c 0xe3
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_1002ee [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x48, 0xf7, 0xd3])
      (notR64Effect pc 3) := by
  exact not_r64_effect_step pc 0x48 0xd3
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_1002f1 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x4c, 0x21, 0xcb])
      (andR64R64Effect pc 3 9) := by
  exact and_r64_r64_effect_step pc 0x4c 0xcb
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_1002f4 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x4c, 0x89, 0xda])
      (movR64R64Effect pc 2 11) := by
  exact mov_r64_r64_effect_step pc 0x4c 0xda
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_1002f7 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x48, 0xf7, 0xd2])
      (notR64Effect pc 2) := by
  exact not_r64_effect_step pc 0x48 0xd2
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_1002fa [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x48, 0x21, 0xfa])
      (andR64R64Effect pc 2 7) := by
  exact and_r64_r64_effect_step pc 0x48 0xfa
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_1002fd [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x48, 0x31, 0xca])
      (xorR64R64Effect pc 2 1) := by
  exact xor_r64_r64_effect_step pc 0x48 0xca
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_100305 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x48, 0x89, 0xea])
      (movR64R64Effect pc 2 5) := by
  exact mov_r64_r64_effect_step pc 0x48 0xea
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_100308 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x48, 0xf7, 0xd2])
      (notR64Effect pc 2) := by
  exact not_r64_effect_step pc 0x48 0xd2
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_100313 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x48, 0x21, 0xf2])
      (andR64R64Effect pc 2 6) := by
  exact and_r64_r64_effect_step pc 0x48 0xf2
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_100316 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x48, 0x31, 0xfa])
      (xorR64R64Effect pc 2 7) := by
  exact xor_r64_r64_effect_step pc 0x48 0xfa
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_10031e [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x49, 0x89, 0xff])
      (movR64R64Effect pc 15 7) := by
  exact mov_r64_r64_effect_step pc 0x49 0xff
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_100321 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x49, 0xf7, 0xd7])
      (notR64Effect pc 15) := by
  exact not_r64_effect_step pc 0x49 0xd7
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_100324 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x49, 0x21, 0xef])
      (andR64R64Effect pc 15 5) := by
  exact and_r64_r64_effect_step pc 0x49 0xef
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_100327 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x4d, 0x31, 0xdf])
      (xorR64R64Effect pc 15 11) := by
  exact xor_r64_r64_effect_step pc 0x4d 0xdf
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_10032f [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x48, 0x89, 0xf7])
      (movR64R64Effect pc 7 6) := by
  exact mov_r64_r64_effect_step pc 0x48 0xf7
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_100332 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x48, 0xf7, 0xd7])
      (notR64Effect pc 7) := by
  exact not_r64_effect_step pc 0x48 0xd7
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_100335 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x48, 0x21, 0xcf])
      (andR64R64Effect pc 7 1) := by
  exact and_r64_r64_effect_step pc 0x48 0xcf
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_100338 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x48, 0xf7, 0xd1])
      (notR64Effect pc 1) := by
  exact not_r64_effect_step pc 0x48 0xd1
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_10033b [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x4c, 0x21, 0xd9])
      (andR64R64Effect pc 1 11) := by
  exact and_r64_r64_effect_step pc 0x4c 0xd9
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_10034a [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x48, 0xc1, 0xc0, 0x03])
      (rolR64Effect pc 4 0 3) := by
  exact rol_r64_imm8_effect_step pc 0x48 0xc0 0x03
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_10034e [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x4c, 0x89, 0xd6])
      (movR64R64Effect pc 6 10) := by
  exact mov_r64_r64_effect_step pc 0x4c 0xd6
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_100351 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x48, 0xc1, 0xc6, 0x1c])
      (rolR64Effect pc 4 6 28) := by
  exact rol_r64_imm8_effect_step pc 0x48 0xc6 0x1c
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_100362 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x49, 0xc1, 0xc2, 0x2d])
      (rolR64Effect pc 4 10 45) := by
  exact rol_r64_imm8_effect_step pc 0x49 0xc2 0x2d
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_100366 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x49, 0xc1, 0xc5, 0x3d])
      (rolR64Effect pc 4 13 61) := by
  exact rol_r64_imm8_effect_step pc 0x49 0xc5 0x3d
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_10036f [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x49, 0xc1, 0xc7, 0x14])
      (rolR64Effect pc 4 15 20) := by
  exact rol_r64_imm8_effect_step pc 0x49 0xc7 0x14
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_100373 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x4d, 0x89, 0xf9])
      (movR64R64Effect pc 9 15) := by
  exact mov_r64_r64_effect_step pc 0x4d 0xf9
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_100376 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x49, 0xf7, 0xd1])
      (notR64Effect pc 9) := by
  exact not_r64_effect_step pc 0x49 0xd1
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_100379 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x49, 0x21, 0xc1])
      (andR64R64Effect pc 9 0) := by
  exact and_r64_r64_effect_step pc 0x49 0xc1
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_10037c [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x49, 0x31, 0xf1])
      (xorR64R64Effect pc 9 6) := by
  exact xor_r64_r64_effect_step pc 0x49 0xf1
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_100384 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x49, 0x89, 0xc1])
      (movR64R64Effect pc 9 0) := by
  exact mov_r64_r64_effect_step pc 0x49 0xc1
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_100387 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x49, 0xf7, 0xd1])
      (notR64Effect pc 9) := by
  exact not_r64_effect_step pc 0x49 0xd1
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_10038a [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x4d, 0x21, 0xd1])
      (andR64R64Effect pc 9 10) := by
  exact and_r64_r64_effect_step pc 0x4d 0xd1
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_10038d [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x4d, 0x31, 0xf9])
      (xorR64R64Effect pc 9 15) := by
  exact xor_r64_r64_effect_step pc 0x4d 0xf9
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_100390 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x4d, 0x89, 0xeb])
      (movR64R64Effect pc 11 13) := by
  exact mov_r64_r64_effect_step pc 0x4d 0xeb
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_100393 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x49, 0xf7, 0xd3])
      (notR64Effect pc 11) := by
  exact not_r64_effect_step pc 0x49 0xd3
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_100396 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x49, 0x21, 0xf3])
      (andR64R64Effect pc 11 6) := by
  exact and_r64_r64_effect_step pc 0x49 0xf3
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_100399 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x48, 0xf7, 0xd6])
      (notR64Effect pc 6) := by
  exact not_r64_effect_step pc 0x48 0xd6
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_10039c [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x49, 0x21, 0xf7])
      (andR64R64Effect pc 15 6) := by
  exact and_r64_r64_effect_step pc 0x49 0xf7
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_10039f [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x4c, 0x89, 0xc6])
      (movR64R64Effect pc 6 8) := by
  exact mov_r64_r64_effect_step pc 0x4c 0xc6
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_1003a2 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x48, 0xf7, 0xd6])
      (notR64Effect pc 6) := by
  exact not_r64_effect_step pc 0x48 0xd6
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_1003a5 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x4c, 0x21, 0xe6])
      (andR64R64Effect pc 6 12) := by
  exact and_r64_r64_effect_step pc 0x4c 0xe6
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_1003a8 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x4c, 0x31, 0xf6])
      (xorR64R64Effect pc 6 14) := by
  exact xor_r64_r64_effect_step pc 0x4c 0xf6
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_1003b0 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x4c, 0x31, 0xc3])
      (xorR64R64Effect pc 3 8) := by
  exact xor_r64_r64_effect_step pc 0x4c 0xc3
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_1003bd [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x4c, 0x89, 0xd3])
      (movR64R64Effect pc 3 10) := by
  exact mov_r64_r64_effect_step pc 0x4c 0xd3
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_1003c0 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x48, 0xf7, 0xd3])
      (notR64Effect pc 3) := by
  exact not_r64_effect_step pc 0x48 0xd3
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_1003c3 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x4c, 0x21, 0xeb])
      (andR64R64Effect pc 3 13) := by
  exact and_r64_r64_effect_step pc 0x4c 0xeb
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_1003c6 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x48, 0x31, 0xc3])
      (xorR64R64Effect pc 3 0) := by
  exact xor_r64_r64_effect_step pc 0x48 0xc3
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_1003ce [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x4d, 0x31, 0xd3])
      (xorR64R64Effect pc 11 10) := by
  exact xor_r64_r64_effect_step pc 0x4d 0xd3
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_1003d1 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x4d, 0x31, 0xef])
      (xorR64R64Effect pc 15 13) := by
  exact xor_r64_r64_effect_step pc 0x4d 0xef
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_1003d9 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x48, 0x31, 0xef])
      (xorR64R64Effect pc 7 5) := by
  exact xor_r64_r64_effect_step pc 0x48 0xef
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_1003e6 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x48, 0xc1, 0xc0, 0x0a])
      (rolR64Effect pc 4 0 10) := by
  exact rol_r64_imm8_effect_step pc 0x48 0xc0 0x0a
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_1003ef [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x48, 0xc1, 0xc3, 0x0f])
      (rolR64Effect pc 4 3 15) := by
  exact rol_r64_imm8_effect_step pc 0x48 0xc3 0x0f
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_1003f3 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x48, 0x89, 0xcd])
      (movR64R64Effect pc 5 1) := by
  exact mov_r64_r64_effect_step pc 0x48 0xcd
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_1003f6 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x48, 0xc1, 0xc5, 0x24])
      (rolR64Effect pc 4 5 36) := by
  exact rol_r64_imm8_effect_step pc 0x48 0xc5 0x24
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_100407 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x49, 0xc1, 0xc0, 0x1b])
      (rolR64Effect pc 4 8 27) := by
  exact rol_r64_imm8_effect_step pc 0x49 0xc0 0x1b
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_100410 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x48, 0xc1, 0xc2, 0x38])
      (rolR64Effect pc 4 2 56) := by
  exact rol_r64_imm8_effect_step pc 0x48 0xc2 0x38
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_100419 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x48, 0xf7, 0xd5])
      (notR64Effect pc 5) := by
  exact not_r64_effect_step pc 0x48 0xd5
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_10041c [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x48, 0x21, 0xc5])
      (andR64R64Effect pc 5 0) := by
  exact and_r64_r64_effect_step pc 0x48 0xc5
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_10041f [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x48, 0x89, 0xc1])
      (movR64R64Effect pc 1 0) := by
  exact mov_r64_r64_effect_step pc 0x48 0xc1
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_100422 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x48, 0xf7, 0xd1])
      (notR64Effect pc 1) := by
  exact not_r64_effect_step pc 0x48 0xd1
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_100425 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x48, 0x21, 0xd9])
      (andR64R64Effect pc 1 3) := by
  exact and_r64_r64_effect_step pc 0x48 0xd9
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_100428 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x49, 0x89, 0xd6])
      (movR64R64Effect pc 14 2) := by
  exact mov_r64_r64_effect_step pc 0x49 0xd6
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_10042b [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x49, 0xf7, 0xd6])
      (notR64Effect pc 14) := by
  exact not_r64_effect_step pc 0x49 0xd6
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_10042e [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x4d, 0x21, 0xc6])
      (andR64R64Effect pc 14 8) := by
  exact and_r64_r64_effect_step pc 0x4d 0xc6
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_100431 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x49, 0x31, 0xde])
      (xorR64R64Effect pc 14 3) := by
  exact xor_r64_r64_effect_step pc 0x49 0xde
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_100434 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x49, 0x89, 0xdf])
      (movR64R64Effect pc 15 3) := by
  exact mov_r64_r64_effect_step pc 0x49 0xdf
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_100437 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x49, 0xf7, 0xd7])
      (notR64Effect pc 15) := by
  exact not_r64_effect_step pc 0x49 0xd7
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_10043a [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x49, 0x21, 0xd7])
      (andR64R64Effect pc 15 2) := by
  exact and_r64_r64_effect_step pc 0x49 0xd7
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_10043d [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x49, 0x31, 0xc7])
      (xorR64R64Effect pc 15 0) := by
  exact xor_r64_r64_effect_step pc 0x49 0xc7
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_100445 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x48, 0xd1, 0xc2])
      (rolR64Effect pc 3 2 1) := by
  exact rol_r64_one_effect_step pc 0x48 0xc2
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_100448 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x48, 0xc1, 0xc6, 0x06])
      (rolR64Effect pc 4 6 6) := by
  exact rol_r64_imm8_effect_step pc 0x48 0xc6 0x06
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_100454 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x48, 0xc1, 0xc7, 0x08])
      (rolR64Effect pc 4 7 8) := by
  exact rol_r64_imm8_effect_step pc 0x48 0xc7 0x08
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_10045d [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x48, 0xc1, 0xc3, 0x19])
      (rolR64Effect pc 4 3 25) := by
  exact rol_r64_imm8_effect_step pc 0x48 0xc3 0x19
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_100469 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x49, 0xc1, 0xc2, 0x12])
      (rolR64Effect pc 4 10 18) := by
  exact rol_r64_imm8_effect_step pc 0x49 0xc2 0x12
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_10046d [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x48, 0x89, 0xf0])
      (movR64R64Effect pc 0 6) := by
  exact mov_r64_r64_effect_step pc 0x48 0xf0
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_100470 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x48, 0xf7, 0xd0])
      (notR64Effect pc 0) := by
  exact not_r64_effect_step pc 0x48 0xd0
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_100473 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x48, 0x21, 0xd8])
      (andR64R64Effect pc 0 3) := by
  exact and_r64_r64_effect_step pc 0x48 0xd8
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_100476 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x49, 0x89, 0xfc])
      (movR64R64Effect pc 12 7) := by
  exact mov_r64_r64_effect_step pc 0x49 0xfc
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_100479 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x49, 0xf7, 0xd4])
      (notR64Effect pc 12) := by
  exact not_r64_effect_step pc 0x49 0xd4
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_10047c [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x4d, 0x21, 0xd4])
      (andR64R64Effect pc 12 10) := by
  exact and_r64_r64_effect_step pc 0x4d 0xd4
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_10047f [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x49, 0x31, 0xdc])
      (xorR64R64Effect pc 12 3) := by
  exact xor_r64_r64_effect_step pc 0x49 0xdc
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_100482 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x48, 0xf7, 0xd3])
      (notR64Effect pc 3) := by
  exact not_r64_effect_step pc 0x48 0xd3
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_100485 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x48, 0x21, 0xfb])
      (andR64R64Effect pc 3 7) := by
  exact and_r64_r64_effect_step pc 0x48 0xfb
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_100488 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x4d, 0x89, 0xd5])
      (movR64R64Effect pc 13 10) := by
  exact mov_r64_r64_effect_step pc 0x4d 0xd5
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_10048b [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x49, 0xf7, 0xd5])
      (notR64Effect pc 13) := by
  exact not_r64_effect_step pc 0x49 0xd5
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_10048e [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x49, 0x21, 0xd5])
      (andR64R64Effect pc 13 2) := by
  exact and_r64_r64_effect_step pc 0x49 0xd5
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_100491 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x49, 0x31, 0xfd])
      (xorR64R64Effect pc 13 7) := by
  exact xor_r64_r64_effect_step pc 0x49 0xfd
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_100499 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x48, 0x31, 0xd0])
      (xorR64R64Effect pc 0 2) := by
  exact xor_r64_r64_effect_step pc 0x48 0xd0
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_10049c [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x48, 0x31, 0xf3])
      (xorR64R64Effect pc 3 6) := by
  exact xor_r64_r64_effect_step pc 0x48 0xf3
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_1004a4 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x48, 0xf7, 0xd2])
      (notR64Effect pc 2) := by
  exact not_r64_effect_step pc 0x48 0xd2
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_1004a7 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x48, 0x21, 0xf2])
      (andR64R64Effect pc 2 6) := by
  exact and_r64_r64_effect_step pc 0x48 0xf2
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_1004aa [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x49, 0x89, 0xd5])
      (movR64R64Effect pc 13 2) := by
  exact mov_r64_r64_effect_step pc 0x49 0xd5
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_1004ad [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x4d, 0x31, 0xd5])
      (xorR64R64Effect pc 13 10) := by
  exact xor_r64_r64_effect_step pc 0x4d 0xd5
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_1004b0 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x4c, 0x31, 0xc5])
      (xorR64R64Effect pc 5 8) := by
  exact xor_r64_r64_effect_step pc 0x4c 0xc5
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_1004b8 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x48, 0x31, 0xd1])
      (xorR64R64Effect pc 1 2) := by
  exact xor_r64_r64_effect_step pc 0x48 0xd1
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_1004bb [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x49, 0xf7, 0xd0])
      (notR64Effect pc 8) := by
  exact not_r64_effect_step pc 0x49 0xd0
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_1004be [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x49, 0x21, 0xd0])
      (andR64R64Effect pc 8 2) := by
  exact and_r64_r64_effect_step pc 0x49 0xd0
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

theorem step_1004c9 [Bindings] (pc : BitVec 64) :
    StepEffect (fun s ↦ s.RIP = pc)
      (codeRange pc [0x4c, 0x89, 0xc3])
      (movR64R64Effect pc 3 8) := by
  exact mov_r64_r64_effect_step pc 0x4c 0xc3
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel)

end Sha3.Proofs.Permutation.RoundMachine
