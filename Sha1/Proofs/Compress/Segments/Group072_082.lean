import Sha1.Proofs.Compress.Segments.Group078_082
import Sha1.Proofs.Compress.Machine.Run
import Sha1.Proofs.Compress.Rounds.Scalar
import Sha1.Proofs.Common.Instructions.MovStore.Triple
import X86Proofs.Instructions.Mov.Generated.RM.Triple
import X86Proofs.Instructions.Lea.Generated.RM.Triple
import X86Proofs.Instructions.Add.Generated.AccImm32.Triple
import X86Proofs.Instructions.Add.Generated.Imm32.Triple
import X86Proofs.Instructions.Add.Generated.RM.Triple
import X86Proofs.Instructions.Xor.Generated.RM.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Rol.Generated.R.Triple

namespace Sha1.Proofs.Compress.Machine
open Prelude X86 X86.Machine X86.UserProcess X86Proofs Sha1.Spec.Program
open Standards.NIST.SHA1 Sha1.Proofs.Compress.Rounds
attribute [local irreducible] workingAfter scheduleWord messageSchedule

def bytes072 : List UInt8 :=
  [0x31, 0xc5, 0x1, 0xc2, 0x89, 0x54, 0x24, 0x10, 0x31, 0xc8, 0x31, 0xd8, 0x89, 0xda, 0xc1, 0xc2,
    0x5, 0x46, 0x8d, 0xc, 0x2, 0x41, 0x81, 0xc1, 0xd6, 0xc1, 0x62, 0xca, 0x44, 0x89, 0xd2, 0x44,
    0x31, 0xfa, 0x44, 0x31, 0xda, 0xd1, 0xc2, 0x45, 0x89, 0xc8, 0x41, 0xc1, 0xc0, 0x5, 0x1, 0xd6,
    0x89, 0x54, 0x24, 0x8, 0x1, 0xc6, 0x41, 0x8d, 0x4, 0x30, 0x5, 0xd6, 0xc1, 0x62, 0xca]

def effect072 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    (Effect.seq (Effect.seq (Effect.seq ((xorR32R32Effect 0x103428 2 5 0)) (addR32R32Effect 0x10342a
    2 2 0)) (movM32R32LowEffect 0x10342c 2 (.sib 4 none 0 (.d8 0x10)))) (xorR32R32Effect 0x103430 2
    0 1)) (xorR32R32Effect 0x103432 2 0 3)) (movR32R32Effect 0x103434 2 2 3)) (rolR32Effect 0x103436
    3 2 5)) (leaR32Effect 0x103439 4 9 (.sib 2 (some 8) 0 .none))) (addR32Imm32Effect 0x10343d 7 9
    0xca62c1d6)) (movR32R32Effect 0x103444 3 2 10)) (xorR32R32Effect 0x103447 3 2 15))
    (xorR32R32Effect 0x10344a 3 2 11)) (rolR32Effect 0x10344d 2 2 1)) (movR32R32Effect 0x10344f 3 8
    9)) (rolR32Effect 0x103452 4 8 5)) (addR32R32Effect 0x103456 2 6 2)) (movM32R32LowEffect
    0x103458 2 (.sib 4 none 0 (.d8 0x8)))) (addR32R32Effect 0x10345c 2 6 0)) (leaR32Effect 0x10345e
    4 0 (.sib 8 (some 6) 0 .none))) (addEaxImm32Effect 0x103462 0xca62c1d6)

set_option maxHeartbeats 1200000 in
theorem block072 [Bindings] (boundary : ReturnBoundary) (stack input : BitVec 64)
    (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes072.length →
      0x103428 + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x103428 ∧ FrameData stack input M s ∧
        Write.AllHold s (cut072 stack input H M))
      (codeRange 0x103428 bytes072) effect072 := by
  unfold bytes072 at hout ⊢
  sha1_run_begin (xor_r32_r32_effect_step 0x103428 0xc5 (by decide +kernel))
  sha1_run_then (add_r32_r32_effect_step 0x10342a 0xc2 (by decide +kernel))
  sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m32_r32_low_effect_step 0x10342c 2
    (.sib 4 none 0 (.d8 0x10)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x103430 0xc8 (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x103432 0xd8 (by decide +kernel))
  sha1_run_then (mov_r32_r32_effect_step 0x103434 0xda (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x103436 0xc2 0x5 (by decide +kernel) (by decide +kernel))
  sha1_run_then (lea_r32_rex_effect_step 0x103439 0x46 (by unfold RexNoWPrefix; decide +kernel) 1
    (.sib 2 (some 8) 0 .none) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_imm32_rex_effect_step 0x10343d 0x41 0xc1 0xca62c1d6
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x103444 0x44 0xd2
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x103447 0x44 0xfa
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x10344a 0x44 0xda
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_one_effect_step 0x10344d 0xc2 (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x10344f 0x45 0xc8
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_imm8_rex_effect_step 0x103452 0x41 0xc0 0x5
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_effect_step 0x103456 0xd6 (by decide +kernel))
  sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m32_r32_low_effect_step 0x103458 2
    (.sib 4 none 0 (.d8 0x8)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_effect_step 0x10345c 0xc6 (by decide +kernel))
  sha1_run_then (lea_r32_rex_effect_step 0x10345e 0x41 (by unfold RexNoWPrefix; decide +kernel) 0
    (.sib 8 (some 6) 0 .none) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_eax_imm32_effect_step 0x103462 0xca62c1d6)
  sha1_run_finish [effect072]

def bytes073 : List UInt8 :=
  [0x8b, 0x74, 0x24, 0x4, 0x4c, 0x8b, 0x54, 0x24, 0x28, 0x44, 0x31, 0xd6, 0x44, 0x31, 0xee, 0x48,
    0x8b, 0x5c, 0x24, 0x58, 0x31, 0xde, 0xd1, 0xc6, 0x89, 0x74, 0x24, 0x4, 0x44, 0x31, 0xcd, 0x1,
    0xf1, 0x1, 0xe9, 0x44, 0x33, 0x14, 0x24, 0x44, 0x33, 0x54, 0x24, 0x30, 0x41, 0x31, 0xd2, 0x41,
    0xd1, 0xc2, 0x89, 0xc6, 0xc1, 0xc6, 0x5, 0x41, 0xc1, 0xc1, 0x1e, 0x1, 0xf1, 0x81, 0xc1, 0xd6,
    0xc1, 0x62, 0xca]

def effect073 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    (Effect.seq (Effect.seq (Effect.seq ((movR32M32LowEffect 0x103467 6 (.sib 4 none 0 (.d8 0x4))))
    (movR64M64Effect 0x10346b 10 (.sib 4 none 0 (.d8 0x28)))) (xorR32R32Effect 0x103470 3 6 10))
    (xorR32R32Effect 0x103473 3 6 13)) (movR64M64Effect 0x103476 3 (.sib 4 none 0 (.d8 0x58))))
    (xorR32R32Effect 0x10347b 2 6 3)) (rolR32Effect 0x10347d 2 6 1)) (movM32R32LowEffect 0x10347f 6
    (.sib 4 none 0 (.d8 0x4)))) (xorR32R32Effect 0x103483 3 5 9)) (addR32R32Effect 0x103486 2 1 6))
    (addR32R32Effect 0x103488 2 1 5)) (xorR32M32Effect 0x10348a 10 (.sib 4 none 0 .none)))
    (xorR32M32Effect 0x10348e 10 (.sib 4 none 0 (.d8 0x30)))) (xorR32R32Effect 0x103493 3 10 2))
    (rolR32Effect 0x103496 3 10 1)) (movR32R32Effect 0x103499 2 6 0)) (rolR32Effect 0x10349b 3 6 5))
    (rolR32Effect 0x10349e 4 9 30)) (addR32R32Effect 0x1034a2 2 1 6)) (addR32Imm32Effect 0x1034a4 6
    1 0xca62c1d6)

set_option maxHeartbeats 1200000 in
theorem block073 [Bindings] (boundary : ReturnBoundary) (stack input : BitVec 64)
    (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes073.length →
      0x103467 + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x103467 ∧ FrameData stack input M s ∧
        Write.AllHold s (cut073 stack input H M))
      (codeRange 0x103467 bytes073) effect073 := by
  unfold bytes073 at hout ⊢
  sha1_run_begin (mov_r32_m32_low_effect_step 0x103467 6 (.sib 4 none 0 (.d8 0x4))
    (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r64_m64_effect_step 0x10346b 0x4c (by unfold RexWPrefix; decide +kernel) 2
    (.sib 4 none 0 (.d8 0x28)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x103470 0x44 0xd6
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x103473 0x44 0xee
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r64_m64_effect_step 0x103476 0x48 (by unfold RexWPrefix; decide +kernel) 3
    (.sib 4 none 0 (.d8 0x58)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x10347b 0xde (by decide +kernel))
  sha1_run_then (rol_r32_one_effect_step 0x10347d 0xc6 (by decide +kernel) (by decide +kernel))
  sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m32_r32_low_effect_step 0x10347f 6
    (.sib 4 none 0 (.d8 0x4)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x103483 0x44 0xcd
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_effect_step 0x103486 0xf1 (by decide +kernel))
  sha1_run_then (add_r32_r32_effect_step 0x103488 0xe9 (by decide +kernel))
  sha1_run_then (xor_r32_m32_effect_step 0x10348a 0x44 (by unfold RexNoWPrefix; decide +kernel) 2
    (.sib 4 none 0 .none) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_m32_effect_step 0x10348e 0x44 (by unfold RexNoWPrefix; decide +kernel) 2
    (.sib 4 none 0 (.d8 0x30)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x103493 0x41 0xd2
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_one_rex_effect_step 0x103496 0x41 0xc2
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_effect_step 0x103499 0xc6 (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x10349b 0xc6 0x5 (by decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_imm8_rex_effect_step 0x10349e 0x41 0xc1 0x1e
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_effect_step 0x1034a2 0xf1 (by decide +kernel))
  sha1_run_then (add_r32_imm32_effect_step 0x1034a4 0xc1 0xca62c1d6 (by decide +kernel)
    (by decide +kernel))
  sha1_run_finish [effect073]

def bytes074 : List UInt8 :=
  [0x89, 0xce, 0xc1, 0xc6, 0x5, 0x45, 0x8d, 0x4, 0x3a, 0x4c, 0x89, 0xd2, 0x4c, 0x89, 0x54, 0x24,
    0x28, 0x44, 0x31, 0xcf, 0x31, 0xc7, 0x3, 0x7c, 0x24, 0x10, 0x1, 0xfe, 0x81, 0xc6, 0xd6, 0xc1,
    0x62, 0xca, 0xc1, 0xc0, 0x1e, 0x89, 0xc7, 0x44, 0x31, 0xcf, 0x31, 0xcf, 0x44, 0x1, 0xc7, 0xc1,
    0xc1, 0x1e]

def effect074 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    ((movR32R32Effect 0x1034aa 2 6 1)) (rolR32Effect 0x1034ac 3 6 5)) (leaR32Effect 0x1034af 4 8
    (.sib 10 (some 7) 0 .none))) (movR64R64Effect 0x1034b3 2 10)) (movM64R64Effect 0x1034b6 10 (.sib
    4 none 0 (.d8 0x28)))) (xorR32R32Effect 0x1034bb 3 7 9)) (xorR32R32Effect 0x1034be 2 7 0))
    (addR32M32Effect 0x1034c0 4 7 (.sib 4 none 0 (.d8 0x10)))) (addR32R32Effect 0x1034c4 2 6 7))
    (addR32Imm32Effect 0x1034c6 6 6 0xca62c1d6)) (rolR32Effect 0x1034cc 3 0 30)) (movR32R32Effect
    0x1034cf 2 7 0)) (xorR32R32Effect 0x1034d1 3 7 9)) (xorR32R32Effect 0x1034d4 2 7 1))
    (addR32R32Effect 0x1034d6 3 7 8)) (rolR32Effect 0x1034d9 3 1 30)

set_option maxHeartbeats 1200000 in
theorem block074 [Bindings] (boundary : ReturnBoundary) (stack input : BitVec 64)
    (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes074.length →
      0x1034aa + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x1034aa ∧ FrameData stack input M s ∧
        Write.AllHold s (cut074 stack input H M))
      (codeRange 0x1034aa bytes074) effect074 := by
  unfold bytes074 at hout ⊢
  sha1_run_begin (mov_r32_r32_effect_step 0x1034aa 0xce (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x1034ac 0xc6 0x5 (by decide +kernel) (by decide +kernel))
  sha1_run_then (lea_r32_rex_effect_step 0x1034af 0x45 (by unfold RexNoWPrefix; decide +kernel) 0
    (.sib 10 (some 7) 0 .none) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r64_r64_effect_step 0x1034b3 0x4c 0xd2 (by unfold RexWPrefix; decide +kernel)
    (by decide +kernel))
  sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m64_r64_effect_step 0x1034b6 0x4c
    (by unfold RexWPrefix; decide +kernel) 2 (.sib 4 none 0 (.d8 0x28)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x1034bb 0x44 0xcf
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x1034be 0xc7 (by decide +kernel))
  sha1_run_then (add_r32_m32_effect_step 0x1034c0 7 (.sib 4 none 0 (.d8 0x10)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_effect_step 0x1034c4 0xfe (by decide +kernel))
  sha1_run_then (add_r32_imm32_effect_step 0x1034c6 0xc6 0xca62c1d6 (by decide +kernel)
    (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x1034cc 0xc0 0x1e (by decide +kernel)
    (by decide +kernel))
  sha1_run_then (mov_r32_r32_effect_step 0x1034cf 0xc7 (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x1034d1 0x44 0xcf
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x1034d4 0xcf (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x1034d6 0x44 0xc7
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x1034d9 0xc1 0x1e (by decide +kernel)
    (by decide +kernel))
  sha1_run_finish [effect074]

def bytes075 : List UInt8 :=
  [0x4c, 0x8b, 0x54, 0x24, 0x18, 0x45, 0x31, 0xd6, 0x45, 0x31, 0xfa, 0x41, 0x31, 0xda, 0x41, 0x31,
    0xd2, 0x41, 0xd1, 0xc2, 0x4c, 0x89, 0x54, 0x24, 0x18, 0x41, 0x89, 0xf0, 0x41, 0xc1, 0xc0, 0x1e,
    0x44, 0x89, 0xc5, 0x31, 0xcd, 0x41, 0x8d, 0x14, 0xa, 0x89, 0x54, 0x24, 0x10, 0x31, 0xc1, 0x31,
    0xf1, 0xc1, 0xc6, 0x5, 0x1, 0xfe, 0x81, 0xc6, 0xd6, 0xc1, 0x62, 0xca]

def effect075 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    (Effect.seq ((movR64M64Effect 0x1034dc 10 (.sib 4 none 0 (.d8 0x18)))) (xorR32R32Effect 0x1034e1
    3 14 10)) (xorR32R32Effect 0x1034e4 3 10 15)) (xorR32R32Effect 0x1034e7 3 10 3))
    (xorR32R32Effect 0x1034ea 3 10 2)) (rolR32Effect 0x1034ed 3 10 1)) (movM64R64Effect 0x1034f0 10
    (.sib 4 none 0 (.d8 0x18)))) (movR32R32Effect 0x1034f5 3 8 6)) (rolR32Effect 0x1034f8 4 8 30))
    (movR32R32Effect 0x1034fc 3 5 8)) (xorR32R32Effect 0x1034ff 2 5 1)) (leaR32Effect 0x103501 4 2
    (.sib 10 (some 1) 0 .none))) (movM32R32LowEffect 0x103505 2 (.sib 4 none 0 (.d8 0x10))))
    (xorR32R32Effect 0x103509 2 1 0)) (xorR32R32Effect 0x10350b 2 1 6)) (rolR32Effect 0x10350d 3 6
    5)) (addR32R32Effect 0x103510 2 6 7)) (addR32Imm32Effect 0x103512 6 6 0xca62c1d6)

set_option maxHeartbeats 1200000 in
theorem block075 [Bindings] (boundary : ReturnBoundary) (stack input : BitVec 64)
    (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes075.length →
      0x1034dc + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x1034dc ∧ FrameData stack input M s ∧
        Write.AllHold s (cut075 stack input H M))
      (codeRange 0x1034dc bytes075) effect075 := by
  unfold bytes075 at hout ⊢
  sha1_run_begin (mov_r64_m64_effect_step 0x1034dc 0x4c (by unfold RexWPrefix; decide +kernel) 2
    (.sib 4 none 0 (.d8 0x18)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x1034e1 0x45 0xd6
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x1034e4 0x45 0xfa
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x1034e7 0x41 0xda
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x1034ea 0x41 0xd2
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_one_rex_effect_step 0x1034ed 0x41 0xc2
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m64_r64_effect_step 0x1034f0 0x4c
    (by unfold RexWPrefix; decide +kernel) 2 (.sib 4 none 0 (.d8 0x18)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x1034f5 0x41 0xf0
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_imm8_rex_effect_step 0x1034f8 0x41 0xc0 0x1e
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x1034fc 0x44 0xc5
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x1034ff 0xcd (by decide +kernel))
  sha1_run_then (lea_r32_rex_effect_step 0x103501 0x41 (by unfold RexNoWPrefix; decide +kernel) 2
    (.sib 10 (some 1) 0 .none) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m32_r32_low_effect_step 0x103505 2
    (.sib 4 none 0 (.d8 0x10)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x103509 0xc1 (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x10350b 0xf1 (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x10350d 0xc6 0x5 (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_effect_step 0x103510 0xfe (by decide +kernel))
  sha1_run_then (add_r32_imm32_effect_step 0x103512 0xc6 0xca62c1d6 (by decide +kernel)
    (by decide +kernel))
  sha1_run_finish [effect075]

def bytes076 : List UInt8 :=
  [0x8b, 0x3c, 0x24, 0x48, 0x8b, 0x5c, 0x24, 0x50, 0x31, 0xdf, 0x44, 0x31, 0xeb, 0x33, 0x5c, 0x24,
    0x38, 0x45, 0x31, 0xe6, 0x44, 0x8b, 0x54, 0x24, 0x4, 0x45, 0x31, 0xd6, 0x41, 0xd1, 0xc6, 0x44,
    0x31, 0xf3, 0x45, 0x1, 0xce, 0x89, 0xf2, 0xc1, 0xc2, 0x5, 0x41, 0x1, 0xce, 0x44, 0x1, 0xf2,
    0x81, 0xc2, 0xd6, 0xc1, 0x62, 0xca]

def effect076 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    ((movR32M32LowEffect 0x103518 7 (.sib 4 none 0 .none))) (movR64M64Effect 0x10351b 3 (.sib 4 none
    0 (.d8 0x50)))) (xorR32R32Effect 0x103520 2 7 3)) (xorR32R32Effect 0x103522 3 3 13))
    (xorR32M32LowEffect 0x103525 3 (.sib 4 none 0 (.d8 0x38)))) (xorR32R32Effect 0x103529 3 14 12))
    (movR32M32Effect 0x10352c 10 (.sib 4 none 0 (.d8 0x4)))) (xorR32R32Effect 0x103531 3 14 10))
    (rolR32Effect 0x103534 3 14 1)) (xorR32R32Effect 0x103537 3 3 14)) (addR32R32Effect 0x10353a 3
    14 9)) (movR32R32Effect 0x10353d 2 2 6)) (rolR32Effect 0x10353f 3 2 5)) (addR32R32Effect
    0x103542 3 14 1)) (addR32R32Effect 0x103545 3 2 14)) (addR32Imm32Effect 0x103548 6 2 0xca62c1d6)

set_option maxHeartbeats 1200000 in
theorem block076 [Bindings] (boundary : ReturnBoundary) (stack input : BitVec 64)
    (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes076.length →
      0x103518 + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x103518 ∧ FrameData stack input M s ∧
        Write.AllHold s (cut076 stack input H M))
      (codeRange 0x103518 bytes076) effect076 := by
  unfold bytes076 at hout ⊢
  sha1_run_begin (mov_r32_m32_low_effect_step 0x103518 7 (.sib 4 none 0 .none) (by decide +kernel)
    (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r64_m64_effect_step 0x10351b 0x48 (by unfold RexWPrefix; decide +kernel) 3
    (.sib 4 none 0 (.d8 0x50)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x103520 0xdf (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x103522 0x44 0xeb
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_m32_low_effect_step 0x103525 3 (.sib 4 none 0 (.d8 0x38))
    (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x103529 0x45 0xe6
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_m32_effect_step 0x10352c 0x44 (by unfold RexNoWPrefix; decide +kernel) 2
    (.sib 4 none 0 (.d8 0x4)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x103531 0x45 0xd6
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_one_rex_effect_step 0x103534 0x41 0xc6
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x103537 0x44 0xf3
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x10353a 0x45 0xce
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_effect_step 0x10353d 0xf2 (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x10353f 0xc2 0x5 (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x103542 0x41 0xce
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x103545 0x44 0xf2
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_imm32_effect_step 0x103548 0xc2 0xca62c1d6 (by decide +kernel)
    (by decide +kernel))
  sha1_run_finish [effect076]

def bytes077 : List UInt8 :=
  [0x41, 0x89, 0xfe, 0x45, 0x31, 0xde, 0x4c, 0x8b, 0x4c, 0x24, 0x20, 0x45, 0x31, 0xce, 0x41, 0xd1,
    0xc6, 0x31, 0xf5, 0x44, 0x1, 0xf0, 0x1, 0xe8, 0xd1, 0xc3, 0x89, 0xd1, 0xc1, 0xc1, 0x5, 0xc1,
    0xc6, 0x1e, 0x8d, 0x3c, 0x1, 0x81, 0xc7, 0xd6, 0xc1, 0x62, 0xca]

def effect077 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq ((movR32R32Effect 0x10354e 3 14 7))
    (xorR32R32Effect 0x103551 3 14 11)) (movR64M64Effect 0x103554 9 (.sib 4 none 0 (.d8 0x20))))
    (xorR32R32Effect 0x103559 3 14 9)) (rolR32Effect 0x10355c 3 14 1)) (xorR32R32Effect 0x10355f 2 5
    6)) (addR32R32Effect 0x103561 3 0 14)) (addR32R32Effect 0x103564 2 0 5)) (rolR32Effect 0x103566
    2 3 1)) (movR32R32Effect 0x103568 2 1 2)) (rolR32Effect 0x10356a 3 1 5)) (rolR32Effect 0x10356d
    3 6 30)) (leaR32Effect 0x103570 3 7 (.sib 1 (some 0) 0 .none))) (addR32Imm32Effect 0x103573 6 7
    0xca62c1d6)

set_option maxHeartbeats 1200000 in
theorem block077 [Bindings] (boundary : ReturnBoundary) (stack input : BitVec 64)
    (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes077.length →
      0x10354e + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x10354e ∧ FrameData stack input M s ∧
        Write.AllHold s (cut077 stack input H M))
      (codeRange 0x10354e bytes077) effect077 := by
  unfold bytes077 at hout ⊢
  sha1_run_begin (mov_r32_r32_rex_effect_step 0x10354e 0x41 0xfe
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x103551 0x45 0xde
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r64_m64_effect_step 0x103554 0x4c (by unfold RexWPrefix; decide +kernel) 1
    (.sib 4 none 0 (.d8 0x20)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x103559 0x45 0xce
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_one_rex_effect_step 0x10355c 0x41 0xc6
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x10355f 0xf5 (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x103561 0x44 0xf0
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_effect_step 0x103564 0xe8 (by decide +kernel))
  sha1_run_then (rol_r32_one_effect_step 0x103566 0xc3 (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_effect_step 0x103568 0xd1 (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x10356a 0xc1 0x5 (by decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x10356d 0xc6 0x1e (by decide +kernel)
    (by decide +kernel))
  sha1_run_then (lea_r32_effect_step 0x103570 7 (.sib 1 (some 0) 0 .none) (by decide +kernel)
    (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_imm32_effect_step 0x103573 0xc7 0xca62c1d6 (by decide +kernel)
    (by decide +kernel))
  sha1_run_finish [effect077]

set_option maxHeartbeats 1200000 in
theorem effect072_words {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s)
    (hw : Write.AllHold s (cut072 stack input H M))
    (he : (effect072 s).Holds s t) :
    Write.AllHold t (cut073 stack input H M) := by
  have hfull : ∀ w ∈ (effect072 s).writes, w.Full := by
    apply Effect.Local.full
    unfold effect072
    repeat' first | (solve | x86_local) | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  sha1_norm at hs
  simp only [cut072, Write.AllHold] at hw
  obtain ⟨h0, h1, h2, h3, h5, h6, h7, h8, h10, h11, h12, h13, h14, h15, hM0, hM4, hM24, hM32, hM40,
    hM48, hM56, hM64, hM72, hM80, hM88, hM116, hM120, hM124, hM144, hM152⟩ := hw
  sha1_norm at h0 h1 h2 h3 h5 h6 h7 h8
  sha1_norm at h10 h11 h12 h13 h14 h15 hM0 hM4
  sha1_norm at hM24 hM32 hM40 hM48 hM56 hM64 hM72 hM80
  sha1_norm at hM88 hM116 hM120 hM124 hM144 hM152
  simp only [cut073,  Write.AllHold, ← ho.read_reg, ← ho.read_mem]
  sha1_norm [effect072, hs]
  simp_all only [Operand.read]
  have hA68 := workingAfter_step_a_values M H 63 (by decide +kernel)
  change (workingAfter M H 68).a = ((workingAfter M H 67).a).rotateLeft 5 +
    ((workingAfter M H 66).a ^^^ ((workingAfter M H 65).a).rotateLeft 30 ^^^
      ((workingAfter M H 64).a).rotateLeft 30) +
    ((workingAfter M H 63).a).rotateLeft 30 + 0xca62c1d6 + scheduleWord M 67 at hA68
  have hA69 := workingAfter_step_a_values M H 64 (by decide +kernel)
  change (workingAfter M H 69).a = ((workingAfter M H 68).a).rotateLeft 5 +
    ((workingAfter M H 67).a ^^^ ((workingAfter M H 66).a).rotateLeft 30 ^^^
      ((workingAfter M H 65).a).rotateLeft 30) +
    ((workingAfter M H 64).a).rotateLeft 30 + 0xca62c1d6 + scheduleWord M 68 at hA69
  have hW68 : scheduleWord M 68 =
      (scheduleWord M 65 ^^^ scheduleWord M 60 ^^^
        scheduleWord M 54 ^^^ scheduleWord M 52).rotateLeft 1 := by
    have hh := scheduleWord_recurrence M (68 : Fin 80) (by decide +kernel)
    rw [sha1Rotl_eq_rotateLeft 1 _ (by decide +kernel)] at hh
    exact hh
  rw [hA69, hA68, hW68]
  simp (config := { decide := true, implicitDefEqProofs := false }) only [leaSpec,
    BitVec.setWidth_add, BitVec.shiftLeft_zero, BitVec.add_zero, BitVec.setWidth_setWidth_of_le,
    BitVec.setWidth_eq, true_and, and_true]
  simp_all only [BitVec.ofNat_eq_ofNat]
  repeat' apply And.intro
  all_goals first | exact True.intro | ac_rfl

set_option maxHeartbeats 1200000 in
theorem effect073_words {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s)
    (hw : Write.AllHold s (cut073 stack input H M))
    (he : (effect073 s).Holds s t) :
    Write.AllHold t (cut074 stack input H M) := by
  have hfull : ∀ w ∈ (effect073 s).writes, w.Full := by
    apply Effect.Local.full
    unfold effect073
    repeat' first | (solve | x86_local) | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  sha1_norm at hs
  simp only [cut073, Write.AllHold] at hw
  obtain ⟨h0, h1, h2, h5, h7, h9, h11, h12, h13, h14, h15, hM0, hM4, hM8, hM16, hM24, hM32, hM40,
    hM48, hM56, hM64, hM72, hM80, hM88, hM116, hM120, hM124, hM144, hM152⟩ := hw
  sha1_norm at h0 h1 h2 h5 h7 h9 h11 h12
  sha1_norm at h13 h14 h15 hM0 hM4 hM8 hM16 hM24
  sha1_norm at hM32 hM40 hM48 hM56 hM64 hM72 hM80 hM88
  sha1_norm at hM116 hM120 hM124 hM144 hM152
  simp only [cut074,  Write.AllHold, ← ho.read_reg, ← ho.read_mem]
  sha1_norm [effect073, hs]
  simp_all only [Operand.read]
  have hA70 := workingAfter_step_a_values M H 65 (by decide +kernel)
  change (workingAfter M H 70).a = ((workingAfter M H 69).a).rotateLeft 5 +
    ((workingAfter M H 68).a ^^^ ((workingAfter M H 67).a).rotateLeft 30 ^^^
      ((workingAfter M H 66).a).rotateLeft 30) +
    ((workingAfter M H 65).a).rotateLeft 30 + 0xca62c1d6 + scheduleWord M 69 at hA70
  have hW69 : scheduleWord M 69 =
      (scheduleWord M 66 ^^^ scheduleWord M 61 ^^^
        scheduleWord M 55 ^^^ scheduleWord M 53).rotateLeft 1 := by
    have hh := scheduleWord_recurrence M (69 : Fin 80) (by decide +kernel)
    rw [sha1Rotl_eq_rotateLeft 1 _ (by decide +kernel)] at hh
    exact hh
  have hW71 : scheduleWord M 71 =
      (scheduleWord M 68 ^^^ scheduleWord M 63 ^^^
        scheduleWord M 57 ^^^ scheduleWord M 55).rotateLeft 1 := by
    have hh := scheduleWord_recurrence M (71 : Fin 80) (by decide +kernel)
    rw [sha1Rotl_eq_rotateLeft 1 _ (by decide +kernel)] at hh
    exact hh
  rw [hA70, hW69, hW71]
  simp (config := { decide := true, implicitDefEqProofs := false }) only [memLoad_low32,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, true_and, and_true]
  simp_all only [BitVec.ofNat_eq_ofNat]
  repeat' apply And.intro
  all_goals first | exact True.intro | ac_rfl

set_option maxHeartbeats 1200000 in
theorem effect074_words {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s)
    (hw : Write.AllHold s (cut074 stack input H M))
    (he : (effect074 s).Holds s t) :
    Write.AllHold t (cut075 stack input H M) := by
  have hfull : ∀ w ∈ (effect074 s).writes, w.Full := by
    apply Effect.Local.full
    unfold effect074
    repeat' first | (solve | x86_local) | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  sha1_norm at hs
  simp only [cut074, Write.AllHold] at hw
  obtain ⟨h0, h1, h3, h7, h9, h10, h11, h12, h13, h14, h15, hM0, hM4, hM8, hM16, hM24, hM32, hM48,
    hM56, hM64, hM72, hM80, hM116, hM120, hM124, hM144, hM152⟩ := hw
  sha1_norm at h0 h1 h3 h7 h9 h10 h11 h12
  sha1_norm at h13 h14 h15 hM0 hM4 hM8 hM16 hM24
  sha1_norm at hM32 hM48 hM56 hM64 hM72 hM80 hM116 hM120
  sha1_norm at hM124 hM144 hM152
  simp only [cut075,  Write.AllHold, ← ho.read_reg, ← ho.read_mem]
  sha1_norm [effect074, hs]
  simp_all only [Operand.read]
  have hA71 := workingAfter_step_a_values M H 66 (by decide +kernel)
  change (workingAfter M H 71).a = ((workingAfter M H 70).a).rotateLeft 5 +
    ((workingAfter M H 69).a ^^^ ((workingAfter M H 68).a).rotateLeft 30 ^^^
      ((workingAfter M H 67).a).rotateLeft 30) +
    ((workingAfter M H 66).a).rotateLeft 30 + 0xca62c1d6 + scheduleWord M 70 at hA71
  rw [hA71]
  simp (config := { decide := true, implicitDefEqProofs := false }) only [←
    BitVec.setWidth_eq_extractLsb', read32_memStore64_low, BitVec.extractLsb'_setWidth_of_le,
    leaSpec, BitVec.setWidth_add, BitVec.shiftLeft_zero, BitVec.add_zero,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, true_and, and_true]
  simp_all only [BitVec.ofNat_eq_ofNat]
  repeat' apply And.intro
  all_goals first | exact True.intro | ac_rfl

set_option maxHeartbeats 1200000 in
theorem effect075_words {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s)
    (hw : Write.AllHold s (cut075 stack input H M))
    (he : (effect075 s).Holds s t) :
    Write.AllHold t (cut076 stack input H M) := by
  have hfull : ∀ w ∈ (effect075 s).writes, w.Full := by
    apply Effect.Local.full
    unfold effect075
    repeat' first | (solve | x86_local) | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  sha1_norm at hs
  simp only [cut075, Write.AllHold] at hw
  obtain ⟨h0, h1, h2, h3, h6, h7, h9, h11, h12, h13, h14, h15, hM0, hM4, hM8, hM24, hM32, hM40,
    hM48, hM56, hM64, hM72, hM80, hM116, hM120, hM124, hM144, hM152⟩ := hw
  sha1_norm at h0 h1 h2 h3 h6 h7 h9 h11
  sha1_norm at h12 h13 h14 h15 hM0 hM4 hM8 hM24
  sha1_norm at hM32 hM40 hM48 hM56 hM64 hM72 hM80 hM116
  sha1_norm at hM120 hM124 hM144 hM152
  simp only [cut076,  Write.AllHold, ← ho.read_reg, ← ho.read_mem]
  sha1_norm [effect075, hs]
  simp_all only [Operand.read]
  have hA72 := workingAfter_step_a_values M H 67 (by decide +kernel)
  change (workingAfter M H 72).a = ((workingAfter M H 71).a).rotateLeft 5 +
    ((workingAfter M H 70).a ^^^ ((workingAfter M H 69).a).rotateLeft 30 ^^^
      ((workingAfter M H 68).a).rotateLeft 30) +
    ((workingAfter M H 67).a).rotateLeft 30 + 0xca62c1d6 + scheduleWord M 71 at hA72
  have hW74 : scheduleWord M 74 =
      (scheduleWord M 71 ^^^ scheduleWord M 66 ^^^
        scheduleWord M 60 ^^^ scheduleWord M 58).rotateLeft 1 := by
    have hh := scheduleWord_recurrence M (74 : Fin 80) (by decide +kernel)
    rw [sha1Rotl_eq_rotateLeft 1 _ (by decide +kernel)] at hh
    exact hh
  rw [hA72, hW74]
  simp (config := { decide := true, implicitDefEqProofs := false }) only
    [BitVec.extractLsb'_eq_self, read32_memStore64_low, BitVec.extractLsb'_setWidth_of_le,
    memLoad_low32, leaSpec, BitVec.setWidth_add, BitVec.shiftLeft_zero, BitVec.add_zero,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, true_and, and_true]
  simp_all only [BitVec.ofNat_eq_ofNat]
  repeat' apply And.intro
  all_goals first | exact True.intro | ac_rfl

set_option maxHeartbeats 1200000 in
theorem effect076_words {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s)
    (hw : Write.AllHold s (cut076 stack input H M))
    (he : (effect076 s).Holds s t) :
    Write.AllHold t (cut077 stack input H M) := by
  have hfull : ∀ w ∈ (effect076 s).writes, w.Full := by
    apply Effect.Local.full
    unfold effect076
    repeat' first | (solve | x86_local) | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  sha1_norm at hs
  simp only [cut076, Write.AllHold] at hw
  obtain ⟨h0, h1, h5, h6, h8, h9, h11, h12, h13, h14, h15, hM0, hM4, hM8, hM16, hM24, hM32, hM40,
    hM48, hM56, hM64, hM72, hM80, hM116, hM120, hM124, hM144, hM152⟩ := hw
  sha1_norm at h0 h1 h5 h6 h8 h9 h11 h12
  sha1_norm at h13 h14 h15 hM0 hM4 hM8 hM16 hM24
  sha1_norm at hM32 hM40 hM48 hM56 hM64 hM72 hM80 hM116
  sha1_norm at hM120 hM124 hM144 hM152
  simp only [cut077,  Write.AllHold, ← ho.read_reg, ← ho.read_mem]
  sha1_norm [effect076, hs]
  simp_all only [Operand.read]
  have hA73 := workingAfter_step_a_values M H 68 (by decide +kernel)
  change (workingAfter M H 73).a = ((workingAfter M H 72).a).rotateLeft 5 +
    ((workingAfter M H 71).a ^^^ ((workingAfter M H 70).a).rotateLeft 30 ^^^
      ((workingAfter M H 69).a).rotateLeft 30) +
    ((workingAfter M H 68).a).rotateLeft 30 + 0xca62c1d6 + scheduleWord M 72 at hA73
  have hW72 : scheduleWord M 72 =
      (scheduleWord M 69 ^^^ scheduleWord M 64 ^^^
        scheduleWord M 58 ^^^ scheduleWord M 56).rotateLeft 1 := by
    have hh := scheduleWord_recurrence M (72 : Fin 80) (by decide +kernel)
    rw [sha1Rotl_eq_rotateLeft 1 _ (by decide +kernel)] at hh
    exact hh
  rw [hA73, hW72]
  simp (config := { decide := true, implicitDefEqProofs := false }) only [memLoad_low32,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, true_and, and_true]
  simp_all only [BitVec.ofNat_eq_ofNat]
  repeat' apply And.intro
  all_goals first | exact True.intro | ac_rfl

set_option maxHeartbeats 1200000 in
theorem effect077_words {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s)
    (hw : Write.AllHold s (cut077 stack input H M))
    (he : (effect077 s).Holds s t) :
    Write.AllHold t (cut078 stack input H M) := by
  have hfull : ∀ w ∈ (effect077 s).writes, w.Full := by
    apply Effect.Local.full
    unfold effect077
    repeat' first | (solve | x86_local) | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  sha1_norm at hs
  simp only [cut077, Write.AllHold] at hw
  obtain ⟨h0, h2, h3, h5, h6, h7, h8, h10, h11, h12, h13, h15, hM8, hM16, hM24, hM32, hM40, hM48,
    hM64, hM72, hM116, hM120, hM124, hM144, hM152⟩ := hw
  sha1_norm at h0 h2 h3 h5 h6 h7 h8 h10
  sha1_norm at h11 h12 h13 h15 hM8 hM16 hM24 hM32
  sha1_norm at hM40 hM48 hM64 hM72 hM116 hM120 hM124 hM144
  sha1_norm at hM152
  simp only [cut078,  Write.AllHold, ← ho.read_reg, ← ho.read_mem]
  sha1_norm [effect077, hs]
  simp_all only [Operand.read]
  have hA74 := workingAfter_step_a_values M H 69 (by decide +kernel)
  change (workingAfter M H 74).a = ((workingAfter M H 73).a).rotateLeft 5 +
    ((workingAfter M H 72).a ^^^ ((workingAfter M H 71).a).rotateLeft 30 ^^^
      ((workingAfter M H 70).a).rotateLeft 30) +
    ((workingAfter M H 69).a).rotateLeft 30 + 0xca62c1d6 + scheduleWord M 73 at hA74
  have hW73 : scheduleWord M 73 =
      (scheduleWord M 70 ^^^ scheduleWord M 65 ^^^
        scheduleWord M 59 ^^^ scheduleWord M 57).rotateLeft 1 := by
    have hh := scheduleWord_recurrence M (73 : Fin 80) (by decide +kernel)
    rw [sha1Rotl_eq_rotateLeft 1 _ (by decide +kernel)] at hh
    exact hh
  have hW75 : scheduleWord M 75 =
      (scheduleWord M 72 ^^^ scheduleWord M 67 ^^^
        scheduleWord M 61 ^^^ scheduleWord M 59).rotateLeft 1 := by
    have hh := scheduleWord_recurrence M (75 : Fin 80) (by decide +kernel)
    rw [sha1Rotl_eq_rotateLeft 1 _ (by decide +kernel)] at hh
    exact hh
  rw [hA74, hW73, hW75]
  simp (config := { decide := true, implicitDefEqProofs := false }) only [memLoad_low32, leaSpec,
    BitVec.setWidth_add, BitVec.shiftLeft_zero, BitVec.add_zero, BitVec.setWidth_setWidth_of_le,
    BitVec.setWidth_eq, true_and, and_true]
  simp_all only [BitVec.ofNat_eq_ofNat]
  repeat' apply And.intro
  all_goals first | exact True.intro | ac_rfl

set_option maxHeartbeats 1200000 in
theorem effect072_agrees {stack input : BitVec 64} {M : Vector (BitVec 32) 16}
    {s t : RamState} (hf : FrameData stack input M s)
    (he : (effect072 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have hfoot : ∀ c ∈ (effect072 s).components, c ∈ [.mem ((Operand.reg 4 : Operand 64).read s +
    BitVec.ofNat 64 16) 4, .mem ((Operand.reg 4 : Operand 64).read s + BitVec.ofNat 64 8) 4, .reg 0,
    .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg
    13, .reg 14, .reg 15, .flags, .rip] := by
    unfold effect072
    iterate 19 apply components_seq_of
    all_goals sha1_norm
  have ha := he.agrees.mono hfoot
  try rw [hs] at ha
  apply ha.widen
  · intro c hc hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals simp_all (config := { decide := true, implicitDefEqProofs := false }) only
      [Component.isMem, scratchComponents, x86_compose]
  · intro address c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl)
    · exact scratchComponents_stack (offset := 16) (length := 4) (Or.inl (by decide +kernel)) hCov
    · exact scratchComponents_stack (offset := 8) (length := 4) (Or.inl (by decide +kernel)) hCov
    all_goals exact hCov.elim

set_option maxHeartbeats 1200000 in
theorem effect073_agrees {stack input : BitVec 64} {M : Vector (BitVec 32) 16}
    {s t : RamState} (hf : FrameData stack input M s)
    (he : (effect073 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have hfoot : ∀ c ∈ (effect073 s).components, c ∈ [.mem ((Operand.reg 4 : Operand 64).read s +
    BitVec.ofNat 64 4) 4, .reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9,
    .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] := by
    unfold effect073
    iterate 19 apply components_seq_of
    all_goals sha1_norm
  have ha := he.agrees.mono hfoot
  try rw [hs] at ha
  apply ha.widen
  · intro c hc hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl)
    all_goals simp_all (config := { decide := true, implicitDefEqProofs := false }) only
      [Component.isMem, scratchComponents, x86_compose]
  · intro address c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl)
    · exact scratchComponents_stack (offset := 4) (length := 4) (Or.inl (by decide +kernel)) hCov
    all_goals exact hCov.elim

set_option maxHeartbeats 1200000 in
theorem effect074_agrees {stack input : BitVec 64} {M : Vector (BitVec 32) 16}
    {s t : RamState} (hf : FrameData stack input M s)
    (he : (effect074 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have hfoot : ∀ c ∈ (effect074 s).components, c ∈ [.mem ((Operand.reg 4 : Operand 64).read s +
    BitVec.ofNat 64 40) 8, .reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9,
    .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] := by
    unfold effect074
    iterate 15 apply components_seq_of
    all_goals sha1_norm
  have ha := he.agrees.mono hfoot
  try rw [hs] at ha
  apply ha.widen
  · intro c hc hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl)
    all_goals simp_all (config := { decide := true, implicitDefEqProofs := false }) only
      [Component.isMem, scratchComponents, x86_compose]
  · intro address c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl)
    · exact scratchComponents_stack (offset := 40) (length := 8) (Or.inl (by decide +kernel)) hCov
    all_goals exact hCov.elim

set_option maxHeartbeats 1200000 in
theorem effect075_agrees {stack input : BitVec 64} {M : Vector (BitVec 32) 16}
    {s t : RamState} (hf : FrameData stack input M s)
    (he : (effect075 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have hfoot : ∀ c ∈ (effect075 s).components, c ∈ [.mem ((Operand.reg 4 : Operand 64).read s +
    BitVec.ofNat 64 24) 8, .mem ((Operand.reg 4 : Operand 64).read s + BitVec.ofNat 64 16) 4, .reg
    0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12,
    .reg 13, .reg 14, .reg 15, .flags, .rip] := by
    unfold effect075
    iterate 17 apply components_seq_of
    all_goals sha1_norm
  have ha := he.agrees.mono hfoot
  try rw [hs] at ha
  apply ha.widen
  · intro c hc hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals simp_all (config := { decide := true, implicitDefEqProofs := false }) only
      [Component.isMem, scratchComponents, x86_compose]
  · intro address c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl)
    · exact scratchComponents_stack (offset := 24) (length := 8) (Or.inl (by decide +kernel)) hCov
    · exact scratchComponents_stack (offset := 16) (length := 4) (Or.inl (by decide +kernel)) hCov
    all_goals exact hCov.elim

set_option maxHeartbeats 1200000 in
theorem effect076_agrees {stack input : BitVec 64} {M : Vector (BitVec 32) 16}
    {s t : RamState} (hf : FrameData stack input M s)
    (he : (effect076 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have hfoot : ∀ c ∈ (effect076 s).components, c ∈ [.reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6,
    .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] :=
    by
    unfold effect076
    iterate 15 apply components_seq_of
    all_goals sha1_norm
  have ha := he.agrees.mono hfoot
  try rw [hs] at ha
  apply ha.widen
  · intro c hc hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl)
    all_goals simp_all (config := { decide := true, implicitDefEqProofs := false }) only
      [scratchComponents, x86_compose]
  · intro address c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl)
    all_goals exact hCov.elim

set_option maxHeartbeats 1200000 in
theorem effect077_agrees {stack input : BitVec 64} {M : Vector (BitVec 32) 16}
    {s t : RamState} (hf : FrameData stack input M s)
    (he : (effect077 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have hfoot : ∀ c ∈ (effect077 s).components, c ∈ [.reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6,
    .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] :=
    by
    unfold effect077
    iterate 13 apply components_seq_of
    all_goals sha1_norm
  have ha := he.agrees.mono hfoot
  try rw [hs] at ha
  apply ha.widen
  · intro c hc hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl)
    all_goals simp_all (config := { decide := true, implicitDefEqProofs := false }) only
      [scratchComponents, x86_compose]
  · intro address c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl)
    all_goals exact hCov.elim

theorem segment072 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x103428 0x103467 cut072 cut073 := by
  have hout : ∀ d : Nat, d ≤ bytes072.length →
      0x103428 + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    apply outsideCompression_ne hOutside <;>
      simp only [bytes072, List.length_cons, List.length_nil] at hd <;>
      simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega
  apply Segment.of_block (fun _ _ _ _ ↦ effect072)
    (fun stack input H M ↦ block072 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64 0x3428) bytes072,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact he.rip.trans (by rfl)
  · intro stack input H M s t _ hf _ he
    exact effect072_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect072_words hf hw he

theorem segment073 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x103467 0x1034aa cut073 cut074 := by
  have hout : ∀ d : Nat, d ≤ bytes073.length →
      0x103467 + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    apply outsideCompression_ne hOutside <;>
      simp only [bytes073, List.length_cons, List.length_nil] at hd <;>
      simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega
  apply Segment.of_block (fun _ _ _ _ ↦ effect073)
    (fun stack input H M ↦ block073 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64 0x3467) bytes073,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact he.rip.trans (by rfl)
  · intro stack input H M s t _ hf _ he
    exact effect073_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect073_words hf hw he

theorem segment074 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x1034aa 0x1034dc cut074 cut075 := by
  have hout : ∀ d : Nat, d ≤ bytes074.length →
      0x1034aa + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    apply outsideCompression_ne hOutside <;>
      simp only [bytes074, List.length_cons, List.length_nil] at hd <;>
      simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega
  apply Segment.of_block (fun _ _ _ _ ↦ effect074)
    (fun stack input H M ↦ block074 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64 0x34aa) bytes074,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact he.rip.trans (by rfl)
  · intro stack input H M s t _ hf _ he
    exact effect074_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect074_words hf hw he

theorem segment075 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x1034dc 0x103518 cut075 cut076 := by
  have hout : ∀ d : Nat, d ≤ bytes075.length →
      0x1034dc + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    apply outsideCompression_ne hOutside <;>
      simp only [bytes075, List.length_cons, List.length_nil] at hd <;>
      simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega
  apply Segment.of_block (fun _ _ _ _ ↦ effect075)
    (fun stack input H M ↦ block075 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64 0x34dc) bytes075,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact he.rip.trans (by rfl)
  · intro stack input H M s t _ hf _ he
    exact effect075_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect075_words hf hw he

theorem segment076 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x103518 0x10354e cut076 cut077 := by
  have hout : ∀ d : Nat, d ≤ bytes076.length →
      0x103518 + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    apply outsideCompression_ne hOutside <;>
      simp only [bytes076, List.length_cons, List.length_nil] at hd <;>
      simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega
  apply Segment.of_block (fun _ _ _ _ ↦ effect076)
    (fun stack input H M ↦ block076 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64 0x3518) bytes076,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact he.rip.trans (by rfl)
  · intro stack input H M s t _ hf _ he
    exact effect076_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect076_words hf hw he

theorem segment077 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x10354e 0x103579 cut077 cut078 := by
  have hout : ∀ d : Nat, d ≤ bytes077.length →
      0x10354e + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    apply outsideCompression_ne hOutside <;>
      simp only [bytes077, List.length_cons, List.length_nil] at hd <;>
      simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega
  apply Segment.of_block (fun _ _ _ _ ↦ effect077)
    (fun stack input H M ↦ block077 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64 0x354e) bytes077,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact he.rip.trans (by rfl)
  · intro stack input H M s t _ hf _ he
    exact effect077_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect077_words hf hw he


theorem segments072_082 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x103428 0x1036a2 cut072 cut083 := by
  have h0 := segment072 boundary hOutside
  have h1 := h0.seq (segment073 boundary hOutside)
  have h2 := h1.seq (segment074 boundary hOutside)
  have h3 := h2.seq (segment075 boundary hOutside)
  have h4 := h3.seq (segment076 boundary hOutside)
  have h5 := h4.seq (segment077 boundary hOutside)
  exact h5.seq (segments078_082 boundary hOutside)

end Sha1.Proofs.Compress.Machine
