import Sha1.Proofs.Compress.Machine.Run
import Sha1.Proofs.Compress.Rounds.Scalar
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Mov.Generated.RM.Triple
import Sha1.Proofs.Common.Instructions.MovStore.Triple
import X86Proofs.Instructions.Rol.Generated.R.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RM.Triple
import X86Proofs.Instructions.Xor.Generated.RM.Triple
import X86Proofs.Instructions.Add.Generated.Imm32.Triple
import X86Proofs.Instructions.Add.Generated.AccImm32.Triple
import X86Proofs.Instructions.Bswap.Generated.R.Triple
import X86Proofs.Instructions.Lea.Generated.RM.Triple

namespace Sha1.Proofs.Compress.Machine

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Sha1.Spec.Program
open Standards.NIST.SHA1 Sha1.Proofs.Compress.Rounds

attribute [local irreducible] workingAfter scheduleWord messageSchedule

def bytes045 : List UInt8 :=
  [0x41, 0x31, 0xd0, 0x41, 0x21, 0xf8, 0x4c, 0x8b, 0x5c, 0x24, 0x48, 0x48, 0x8b, 0x5c, 0x24, 0x60, 0x44, 0x31, 0xdb, 0x33, 0x5c, 0x24, 0x8, 0x44, 0x89, 0x24, 0x24, 0x44, 0x31, 0xe3, 0xd1, 0xc3, 0x49, 0x89, 0xdc, 0x41, 0x89, 0xf1, 0x41, 0x21, 0xd1, 0x45, 0x31, 0xc1, 0x44, 0x1, 0xe0, 0x44, 0x1, 0xc8, 0x41, 0x89, 0xc8, 0x41, 0xc1, 0xc0, 0x5, 0x44, 0x1, 0xc0, 0x5, 0xdc, 0xbc, 0x1b, 0x8f]

set_option maxHeartbeats 800000 in
def effect045 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq ((xorR32R32Effect 0x102e83 3 8 2)) (andR32R32Effect 0x102e86 3 8 7)) (movR64M64Effect 0x102e89 11 (.sib 4 none 0 (.d8 0x48)))) (movR64M64Effect 0x102e8e 3 (.sib 4 none 0 (.d8 0x60)))) (xorR32R32Effect 0x102e93 3 3 11)) (xorR32M32LowEffect 0x102e96 3 (.sib 4 none 0 (.d8 0x8)))) (movM32R32Effect 0x102e9a 12 (.sib 4 none 0 .none))) (xorR32R32Effect 0x102e9e 3 3 12)) (rolR32Effect 0x102ea1 2 3 1)) (movR64R64Effect 0x102ea3 12 3)) (movR32R32Effect 0x102ea6 3 9 6)) (andR32R32Effect 0x102ea9 3 9 2)) (xorR32R32Effect 0x102eac 3 9 8)) (addR32R32Effect 0x102eaf 3 0 12)) (addR32R32Effect 0x102eb2 3 0 9)) (movR32R32Effect 0x102eb5 3 8 1)) (rolR32Effect 0x102eb8 4 8 5)) (addR32R32Effect 0x102ebc 3 0 8)) (addEaxImm32Effect 0x102ebf 0x8f1bbcdc)

set_option maxHeartbeats 1600000 in
theorem block045 [Bindings] (boundary : ReturnBoundary)
    (stack input : BitVec 64) (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes045.length → 0x102e83 + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x102e83 ∧ FrameData stack input M s ∧
        Write.AllHold s (cut045 stack input H M))
      (codeRange 0x102e83 bytes045) effect045 := by
  unfold bytes045 at hout ⊢
  sha1_run_begin (xor_r32_r32_rex_effect_step 0x102e83 0x41 0xd0 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (and_r32_r32_rex_effect_step 0x102e86 0x41 0xf8 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r64_m64_effect_step 0x102e89 0x4c (by unfold RexWPrefix; decide +kernel) 3 (.sib 4 none 0 (.d8 0x48)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r64_m64_effect_step 0x102e8e 0x48 (by unfold RexWPrefix; decide +kernel) 3 (.sib 4 none 0 (.d8 0x60)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102e93 0x44 0xdb (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_m32_low_effect_step 0x102e96 3 (.sib 4 none 0 (.d8 0x8)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m32_r32_effect_step 0x102e9a 0x44 (by unfold RexNoWPrefix; decide +kernel) 4 (.sib 4 none 0 .none) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102e9e 0x44 0xe3 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_one_effect_step 0x102ea1 0xc3 (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r64_r64_effect_step 0x102ea3 0x49 0xdc (by unfold RexWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x102ea6 0x41 0xf1 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (and_r32_r32_rex_effect_step 0x102ea9 0x41 0xd1 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102eac 0x45 0xc1 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x102eaf 0x44 0xe0 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x102eb2 0x44 0xc8 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x102eb5 0x41 0xc8 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_imm8_rex_effect_step 0x102eb8 0x41 0xc0 0x5 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x102ebc 0x44 0xc0 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (add_eax_imm32_effect_step 0x102ebf 0x8f1bbcdc)
  sha1_run_finish [effect045]

def bytes046 : List UInt8 :=
  [0x4d, 0x89, 0xd8, 0x8b, 0x5c, 0x24, 0xc, 0x41, 0x31, 0xd8, 0x41, 0x31, 0xe8, 0x45, 0x31, 0xd0, 0x41, 0xd1, 0xc0, 0x4c, 0x89, 0x44, 0x24, 0x48, 0xc1, 0xc7, 0x1e, 0x41, 0x89, 0xf9, 0x41, 0x31, 0xf1, 0x41, 0x21, 0xc9, 0x41, 0x1, 0xf0, 0x21, 0xfe, 0x44, 0x31, 0xce, 0x4c, 0x8b, 0x4c, 0x24, 0x30]

set_option maxHeartbeats 800000 in
def effect046 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq ((movR64R64Effect 0x102ec4 8 11)) (movR32M32LowEffect 0x102ec7 3 (.sib 4 none 0 (.d8 0xc)))) (xorR32R32Effect 0x102ecb 3 8 3)) (xorR32R32Effect 0x102ece 3 8 5)) (xorR32R32Effect 0x102ed1 3 8 10)) (rolR32Effect 0x102ed4 3 8 1)) (movM64R64Effect 0x102ed7 8 (.sib 4 none 0 (.d8 0x48)))) (rolR32Effect 0x102edc 3 7 30)) (movR32R32Effect 0x102edf 3 9 7)) (xorR32R32Effect 0x102ee2 3 9 6)) (andR32R32Effect 0x102ee5 3 9 1)) (addR32R32Effect 0x102ee8 3 8 6)) (andR32R32Effect 0x102eeb 2 6 7)) (xorR32R32Effect 0x102eed 3 6 9)) (movR64M64Effect 0x102ef0 9 (.sib 4 none 0 (.d8 0x30)))

set_option maxHeartbeats 1600000 in
theorem block046 [Bindings] (boundary : ReturnBoundary)
    (stack input : BitVec 64) (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes046.length → 0x102ec4 + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x102ec4 ∧ FrameData stack input M s ∧
        Write.AllHold s (cut046 stack input H M))
      (codeRange 0x102ec4 bytes046) effect046 := by
  unfold bytes046 at hout ⊢
  sha1_run_begin (mov_r64_r64_effect_step 0x102ec4 0x4d 0xd8 (by unfold RexWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_m32_low_effect_step 0x102ec7 3 (.sib 4 none 0 (.d8 0xc)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102ecb 0x41 0xd8 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102ece 0x41 0xe8 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102ed1 0x45 0xd0 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_one_rex_effect_step 0x102ed4 0x41 0xc0 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m64_r64_effect_step 0x102ed7 0x4c (by unfold RexWPrefix; decide +kernel) 0 (.sib 4 none 0 (.d8 0x48)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x102edc 0xc7 0x1e (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x102edf 0x41 0xf9 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102ee2 0x41 0xf1 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (and_r32_r32_rex_effect_step 0x102ee5 0x41 0xc9 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x102ee8 0x41 0xf0 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (and_r32_r32_effect_step 0x102eeb 0xfe (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102eed 0x44 0xce (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r64_m64_effect_step 0x102ef0 0x4c (by unfold RexWPrefix; decide +kernel) 1 (.sib 4 none 0 (.d8 0x30)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_finish [effect046]

def bytes047 : List UInt8 :=
  [0x45, 0x31, 0xcd, 0x45, 0x31, 0xf9, 0x44, 0x33, 0x6c, 0x24, 0x4, 0x44, 0x33, 0x4c, 0x24, 0x28, 0x48, 0x8b, 0x6c, 0x24, 0x18, 0x41, 0x31, 0xed, 0x41, 0xd1, 0xc5, 0x45, 0x31, 0xe1, 0x41, 0xd1, 0xc1, 0x4c, 0x89, 0x4c, 0x24, 0x30, 0x44, 0x1, 0xea, 0x4d, 0x89, 0xeb, 0x4c, 0x89, 0x6c, 0x24, 0x10, 0x1, 0xf2, 0x89, 0xc6, 0xc1, 0xc6, 0x5, 0x1, 0xf2, 0x81, 0xc2, 0xdc, 0xbc, 0x1b, 0x8f]

set_option maxHeartbeats 800000 in
def effect047 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq ((xorR32R32Effect 0x102ef5 3 13 9)) (xorR32R32Effect 0x102ef8 3 9 15)) (xorR32M32Effect 0x102efb 13 (.sib 4 none 0 (.d8 0x4)))) (xorR32M32Effect 0x102f00 9 (.sib 4 none 0 (.d8 0x28)))) (movR64M64Effect 0x102f05 5 (.sib 4 none 0 (.d8 0x18)))) (xorR32R32Effect 0x102f0a 3 13 5)) (rolR32Effect 0x102f0d 3 13 1)) (xorR32R32Effect 0x102f10 3 9 12)) (rolR32Effect 0x102f13 3 9 1)) (movM64R64Effect 0x102f16 9 (.sib 4 none 0 (.d8 0x30)))) (addR32R32Effect 0x102f1b 3 2 13)) (movR64R64Effect 0x102f1e 11 13)) (movM64R64Effect 0x102f21 13 (.sib 4 none 0 (.d8 0x10)))) (addR32R32Effect 0x102f26 2 2 6)) (movR32R32Effect 0x102f28 2 6 0)) (rolR32Effect 0x102f2a 3 6 5)) (addR32R32Effect 0x102f2d 2 2 6)) (addR32Imm32Effect 0x102f2f 6 2 0x8f1bbcdc)

set_option maxHeartbeats 1600000 in
theorem block047 [Bindings] (boundary : ReturnBoundary)
    (stack input : BitVec 64) (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes047.length → 0x102ef5 + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x102ef5 ∧ FrameData stack input M s ∧
        Write.AllHold s (cut047 stack input H M))
      (codeRange 0x102ef5 bytes047) effect047 := by
  unfold bytes047 at hout ⊢
  sha1_run_begin (xor_r32_r32_rex_effect_step 0x102ef5 0x45 0xcd (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102ef8 0x45 0xf9 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_m32_effect_step 0x102efb 0x44 (by unfold RexNoWPrefix; decide +kernel) 5 (.sib 4 none 0 (.d8 0x4)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_m32_effect_step 0x102f00 0x44 (by unfold RexNoWPrefix; decide +kernel) 1 (.sib 4 none 0 (.d8 0x28)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r64_m64_effect_step 0x102f05 0x48 (by unfold RexWPrefix; decide +kernel) 5 (.sib 4 none 0 (.d8 0x18)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102f0a 0x41 0xed (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_one_rex_effect_step 0x102f0d 0x41 0xc5 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102f10 0x45 0xe1 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_one_rex_effect_step 0x102f13 0x41 0xc1 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m64_r64_effect_step 0x102f16 0x4c (by unfold RexWPrefix; decide +kernel) 1 (.sib 4 none 0 (.d8 0x30)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x102f1b 0x44 0xea (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r64_r64_effect_step 0x102f1e 0x4d 0xeb (by unfold RexWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m64_r64_effect_step 0x102f21 0x4c (by unfold RexWPrefix; decide +kernel) 5 (.sib 4 none 0 (.d8 0x10)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_effect_step 0x102f26 0xf2 (by decide +kernel))
  sha1_run_then (mov_r32_r32_effect_step 0x102f28 0xc6 (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x102f2a 0xc6 0x5 (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_effect_step 0x102f2d 0xf2 (by decide +kernel))
  sha1_run_then (add_r32_imm32_effect_step 0x102f2f 0xc2 0x8f1bbcdc (by decide +kernel) (by decide +kernel))
  sha1_run_finish [effect047]

def bytes048 : List UInt8 :=
  [0xc1, 0xc1, 0x1e, 0x89, 0xce, 0x31, 0xfe, 0x21, 0xc6, 0x45, 0x8d, 0x14, 0x39, 0x21, 0xcf, 0x31, 0xf7, 0x89, 0xd6, 0xc1, 0xc6, 0x5, 0x44, 0x1, 0xc7, 0x1, 0xf7, 0x81, 0xc7, 0xdc, 0xbc, 0x1b, 0x8f]

set_option maxHeartbeats 800000 in
def effect048 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq ((rolR32Effect 0x102f35 3 1 30)) (movR32R32Effect 0x102f38 2 6 1)) (xorR32R32Effect 0x102f3a 2 6 7)) (andR32R32Effect 0x102f3c 2 6 0)) (leaR32Effect 0x102f3e 4 10 (.sib 9 (some 7) 0 .none))) (andR32R32Effect 0x102f42 2 7 1)) (xorR32R32Effect 0x102f44 2 7 6)) (movR32R32Effect 0x102f46 2 6 2)) (rolR32Effect 0x102f48 3 6 5)) (addR32R32Effect 0x102f4b 3 7 8)) (addR32R32Effect 0x102f4e 2 7 6)) (addR32Imm32Effect 0x102f50 6 7 0x8f1bbcdc)

set_option maxHeartbeats 1600000 in
theorem block048 [Bindings] (boundary : ReturnBoundary)
    (stack input : BitVec 64) (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes048.length → 0x102f35 + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x102f35 ∧ FrameData stack input M s ∧
        Write.AllHold s (cut048 stack input H M))
      (codeRange 0x102f35 bytes048) effect048 := by
  unfold bytes048 at hout ⊢
  sha1_run_begin (rol_r32_imm8_effect_step 0x102f35 0xc1 0x1e (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_effect_step 0x102f38 0xce (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x102f3a 0xfe (by decide +kernel))
  sha1_run_then (and_r32_r32_effect_step 0x102f3c 0xc6 (by decide +kernel))
  sha1_run_then (lea_r32_rex_effect_step 0x102f3e 0x45 (by unfold RexNoWPrefix; decide +kernel) 2 (.sib 9 (some 7) 0 .none) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (and_r32_r32_effect_step 0x102f42 0xcf (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x102f44 0xf7 (by decide +kernel))
  sha1_run_then (mov_r32_r32_effect_step 0x102f46 0xd6 (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x102f48 0xc6 0x5 (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x102f4b 0x44 0xc7 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_effect_step 0x102f4e 0xf7 (by decide +kernel))
  sha1_run_then (add_r32_imm32_effect_step 0x102f50 0xc7 0x8f1bbcdc (by decide +kernel) (by decide +kernel))
  sha1_run_finish [effect048]

def bytes049 : List UInt8 :=
  [0xc1, 0xc0, 0x1e, 0x89, 0xc6, 0x31, 0xce, 0x21, 0xd6, 0x41, 0x89, 0xc0, 0x41, 0x21, 0xc8, 0x41, 0x31, 0xf0, 0x45, 0x1, 0xd0, 0x89, 0xfe, 0xc1, 0xc6, 0x5, 0xc1, 0xc2, 0x1e, 0x44, 0x1, 0xc6, 0x81, 0xc6, 0xdc, 0xbc, 0x1b, 0x8f]

set_option maxHeartbeats 800000 in
def effect049 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq ((rolR32Effect 0x102f56 3 0 30)) (movR32R32Effect 0x102f59 2 6 0)) (xorR32R32Effect 0x102f5b 2 6 1)) (andR32R32Effect 0x102f5d 2 6 2)) (movR32R32Effect 0x102f5f 3 8 0)) (andR32R32Effect 0x102f62 3 8 1)) (xorR32R32Effect 0x102f65 3 8 6)) (addR32R32Effect 0x102f68 3 8 10)) (movR32R32Effect 0x102f6b 2 6 7)) (rolR32Effect 0x102f6d 3 6 5)) (rolR32Effect 0x102f70 3 2 30)) (addR32R32Effect 0x102f73 3 6 8)) (addR32Imm32Effect 0x102f76 6 6 0x8f1bbcdc)

set_option maxHeartbeats 1600000 in
theorem block049 [Bindings] (boundary : ReturnBoundary)
    (stack input : BitVec 64) (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes049.length → 0x102f56 + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x102f56 ∧ FrameData stack input M s ∧
        Write.AllHold s (cut049 stack input H M))
      (codeRange 0x102f56 bytes049) effect049 := by
  unfold bytes049 at hout ⊢
  sha1_run_begin (rol_r32_imm8_effect_step 0x102f56 0xc0 0x1e (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_effect_step 0x102f59 0xc6 (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x102f5b 0xce (by decide +kernel))
  sha1_run_then (and_r32_r32_effect_step 0x102f5d 0xd6 (by decide +kernel))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x102f5f 0x41 0xc0 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (and_r32_r32_rex_effect_step 0x102f62 0x41 0xc8 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102f65 0x41 0xf0 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x102f68 0x45 0xd0 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_effect_step 0x102f6b 0xfe (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x102f6d 0xc6 0x5 (by decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x102f70 0xc2 0x1e (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x102f73 0x44 0xc6 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_imm32_effect_step 0x102f76 0xc6 0x8f1bbcdc (by decide +kernel) (by decide +kernel))
  sha1_run_finish [effect049]

def bytes050 : List UInt8 :=
  [0x41, 0x89, 0xd0, 0x41, 0x31, 0xc0, 0x41, 0x21, 0xf8, 0x41, 0x89, 0xd1, 0x41, 0x21, 0xc1, 0x45, 0x31, 0xc1, 0x4c, 0x8b, 0x6c, 0x24, 0x58, 0x41, 0x89, 0xda, 0x45, 0x31, 0xea, 0x45, 0x31, 0xf2, 0x45, 0x31, 0xda, 0x41, 0xd1, 0xc2, 0x41, 0x89, 0xf0, 0x41, 0xc1, 0xc0, 0x5, 0x44, 0x1, 0xd1, 0x44, 0x89, 0xd3, 0x44, 0x89, 0x54, 0x24, 0xc, 0x44, 0x1, 0xc9, 0x44, 0x1, 0xc1, 0x81, 0xc1, 0xdc, 0xbc, 0x1b, 0x8f]

set_option maxHeartbeats 800000 in
def effect050 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq ((movR32R32Effect 0x102f7c 3 8 2)) (xorR32R32Effect 0x102f7f 3 8 0)) (andR32R32Effect 0x102f82 3 8 7)) (movR32R32Effect 0x102f85 3 9 2)) (andR32R32Effect 0x102f88 3 9 0)) (xorR32R32Effect 0x102f8b 3 9 8)) (movR64M64Effect 0x102f8e 13 (.sib 4 none 0 (.d8 0x58)))) (movR32R32Effect 0x102f93 3 10 3)) (xorR32R32Effect 0x102f96 3 10 13)) (xorR32R32Effect 0x102f99 3 10 14)) (xorR32R32Effect 0x102f9c 3 10 11)) (rolR32Effect 0x102f9f 3 10 1)) (movR32R32Effect 0x102fa2 3 8 6)) (rolR32Effect 0x102fa5 4 8 5)) (addR32R32Effect 0x102fa9 3 1 10)) (movR32R32Effect 0x102fac 3 3 10)) (movM32R32Effect 0x102faf 10 (.sib 4 none 0 (.d8 0xc)))) (addR32R32Effect 0x102fb4 3 1 9)) (addR32R32Effect 0x102fb7 3 1 8)) (addR32Imm32Effect 0x102fba 6 1 0x8f1bbcdc)

set_option maxHeartbeats 1600000 in
theorem block050 [Bindings] (boundary : ReturnBoundary)
    (stack input : BitVec 64) (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes050.length → 0x102f7c + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x102f7c ∧ FrameData stack input M s ∧
        Write.AllHold s (cut050 stack input H M))
      (codeRange 0x102f7c bytes050) effect050 := by
  unfold bytes050 at hout ⊢
  sha1_run_begin (mov_r32_r32_rex_effect_step 0x102f7c 0x41 0xd0 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102f7f 0x41 0xc0 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (and_r32_r32_rex_effect_step 0x102f82 0x41 0xf8 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x102f85 0x41 0xd1 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (and_r32_r32_rex_effect_step 0x102f88 0x41 0xc1 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102f8b 0x45 0xc1 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r64_m64_effect_step 0x102f8e 0x4c (by unfold RexWPrefix; decide +kernel) 5 (.sib 4 none 0 (.d8 0x58)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x102f93 0x41 0xda (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102f96 0x45 0xea (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102f99 0x45 0xf2 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102f9c 0x45 0xda (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_one_rex_effect_step 0x102f9f 0x41 0xc2 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x102fa2 0x41 0xf0 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_imm8_rex_effect_step 0x102fa5 0x41 0xc0 0x5 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x102fa9 0x44 0xd1 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x102fac 0x44 0xd3 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m32_r32_effect_step 0x102faf 0x44 (by unfold RexNoWPrefix; decide +kernel) 2 (.sib 4 none 0 (.d8 0xc)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x102fb4 0x44 0xc9 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x102fb7 0x44 0xc1 (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_imm32_effect_step 0x102fba 0xc1 0x8f1bbcdc (by decide +kernel) (by decide +kernel))
  sha1_run_finish [effect050]

private def genericCut045 (stack input : BitVec 64) (H : Vector (BitVec 32) 5)
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) : List Write :=
  [⟨(.reg 0 : Operand 32), ((A 40)).rotateLeft 30⟩,
    ⟨(.reg 1 : Operand 32), (A 44)⟩,
    ⟨(.reg 2 : Operand 32), ((A 41)).rotateLeft 30⟩,
    ⟨(.reg 5 : Operand 32), W 38⟩,
    ⟨(.reg 6 : Operand 32), ((A 42)).rotateLeft 30⟩,
    ⟨(.reg 7 : Operand 32), (A 43)⟩,
    ⟨(.reg 8 : Operand 32), ((A 42)).rotateLeft 30⟩,
    ⟨(.reg 10 : Operand 32), W 43⟩,
    ⟨(.reg 12 : Operand 32), W 41⟩,
    ⟨(.reg 13 : Operand 32), W 29⟩,
    ⟨(.reg 14 : Operand 32), W 40⟩,
    ⟨(.reg 15 : Operand 32), W 33⟩,
    ⟨(.mem (stack + 4) : Operand 32), W 37⟩,
    ⟨(.mem (stack + 8) : Operand 32), W 36⟩,
    ⟨(.mem (stack + 12) : Operand 32), W 32⟩,
    ⟨(.mem (stack + 24) : Operand 32), W 42⟩,
    ⟨(.mem (stack + 32) : Operand 32), W 38⟩,
    ⟨(.mem (stack + 40) : Operand 32), W 39⟩,
    ⟨(.mem (stack + 48) : Operand 32), W 31⟩,
    ⟨(.mem (stack + 56) : Operand 32), W 35⟩,
    ⟨(.mem (stack + 64) : Operand 64), input⟩,
    ⟨(.mem (stack + 72) : Operand 32), W 30⟩,
    ⟨(.mem (stack + 80) : Operand 32), W 43⟩,
    ⟨(.mem (stack + 88) : Operand 32), W 34⟩,
    ⟨(.mem (stack + 96) : Operand 32), W 28⟩,
    ⟨(.mem (stack + 116) : Operand 32), H[0]⟩,
    ⟨(.mem (stack + 120) : Operand 32), H[3]⟩,
    ⟨(.mem (stack + 124) : Operand 32), H[4]⟩,
    ⟨(.mem (stack + 144) : Operand 32), H[2]⟩,
    ⟨(.mem (stack + 152) : Operand 32), H[1]⟩]


private def genericCut046 (stack input : BitVec 64) (H : Vector (BitVec 32) 5)
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) : List Write :=
  [⟨(.reg 0 : Operand 32), (A 45)⟩,
    ⟨(.reg 1 : Operand 32), (A 44)⟩,
    ⟨(.reg 2 : Operand 32), ((A 41)).rotateLeft 30⟩,
    ⟨(.reg 5 : Operand 32), W 38⟩,
    ⟨(.reg 6 : Operand 32), ((A 42)).rotateLeft 30⟩,
    ⟨(.reg 7 : Operand 32), (A 43)⟩,
    ⟨(.reg 10 : Operand 32), W 43⟩,
    ⟨(.reg 11 : Operand 32), W 30⟩,
    ⟨(.reg 12 : Operand 32), W 44⟩,
    ⟨(.reg 13 : Operand 32), W 29⟩,
    ⟨(.reg 14 : Operand 32), W 40⟩,
    ⟨(.reg 15 : Operand 32), W 33⟩,
    ⟨(.mem (stack + 0) : Operand 32), W 41⟩,
    ⟨(.mem (stack + 4) : Operand 32), W 37⟩,
    ⟨(.mem (stack + 8) : Operand 32), W 36⟩,
    ⟨(.mem (stack + 12) : Operand 32), W 32⟩,
    ⟨(.mem (stack + 24) : Operand 32), W 42⟩,
    ⟨(.mem (stack + 32) : Operand 32), W 38⟩,
    ⟨(.mem (stack + 40) : Operand 32), W 39⟩,
    ⟨(.mem (stack + 48) : Operand 32), W 31⟩,
    ⟨(.mem (stack + 56) : Operand 32), W 35⟩,
    ⟨(.mem (stack + 64) : Operand 64), input⟩,
    ⟨(.mem (stack + 80) : Operand 32), W 43⟩,
    ⟨(.mem (stack + 88) : Operand 32), W 34⟩,
    ⟨(.mem (stack + 116) : Operand 32), H[0]⟩,
    ⟨(.mem (stack + 120) : Operand 32), H[3]⟩,
    ⟨(.mem (stack + 124) : Operand 32), H[4]⟩,
    ⟨(.mem (stack + 144) : Operand 32), H[2]⟩,
    ⟨(.mem (stack + 152) : Operand 32), H[1]⟩]


private def genericCut047 (stack input : BitVec 64) (H : Vector (BitVec 32) 5)
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) : List Write :=
  [⟨(.reg 0 : Operand 32), (A 45)⟩,
    ⟨(.reg 1 : Operand 32), (A 44)⟩,
    ⟨(.reg 2 : Operand 32), ((A 41)).rotateLeft 30⟩,
    ⟨(.reg 3 : Operand 32), W 32⟩,
    ⟨(.reg 6 : Operand 32), (((A 44) &&& ((A 42)).rotateLeft 30) ^^^ ((A 44) &&& ((A 43)).rotateLeft 30) ^^^ (((A 42)).rotateLeft 30 &&& ((A 43)).rotateLeft 30))⟩,
    ⟨(.reg 7 : Operand 32), ((A 43)).rotateLeft 30⟩,
    ⟨(.reg 8 : Operand 32), (W 46 + ((A 42)).rotateLeft 30)⟩,
    ⟨(.reg 9 : Operand 32), W 31⟩,
    ⟨(.reg 12 : Operand 32), W 44⟩,
    ⟨(.reg 13 : Operand 32), W 29⟩,
    ⟨(.reg 14 : Operand 32), W 40⟩,
    ⟨(.reg 15 : Operand 32), W 33⟩,
    ⟨(.mem (stack + 0) : Operand 32), W 41⟩,
    ⟨(.mem (stack + 4) : Operand 32), W 37⟩,
    ⟨(.mem (stack + 8) : Operand 32), W 36⟩,
    ⟨(.mem (stack + 24) : Operand 32), W 42⟩,
    ⟨(.mem (stack + 32) : Operand 32), W 38⟩,
    ⟨(.mem (stack + 40) : Operand 32), W 39⟩,
    ⟨(.mem (stack + 56) : Operand 32), W 35⟩,
    ⟨(.mem (stack + 64) : Operand 64), input⟩,
    ⟨(.mem (stack + 72) : Operand 32), W 46⟩,
    ⟨(.mem (stack + 80) : Operand 32), W 43⟩,
    ⟨(.mem (stack + 88) : Operand 32), W 34⟩,
    ⟨(.mem (stack + 116) : Operand 32), H[0]⟩,
    ⟨(.mem (stack + 120) : Operand 32), H[3]⟩,
    ⟨(.mem (stack + 124) : Operand 32), H[4]⟩,
    ⟨(.mem (stack + 144) : Operand 32), H[2]⟩,
    ⟨(.mem (stack + 152) : Operand 32), H[1]⟩]


private def genericCut048 (stack input : BitVec 64) (H : Vector (BitVec 32) 5)
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) : List Write :=
  [⟨(.reg 0 : Operand 32), (A 45)⟩,
    ⟨(.reg 1 : Operand 32), (A 44)⟩,
    ⟨(.reg 2 : Operand 32), (A 46)⟩,
    ⟨(.reg 3 : Operand 32), W 32⟩,
    ⟨(.reg 5 : Operand 32), W 42⟩,
    ⟨(.reg 7 : Operand 32), ((A 43)).rotateLeft 30⟩,
    ⟨(.reg 8 : Operand 32), (W 46 + ((A 42)).rotateLeft 30)⟩,
    ⟨(.reg 9 : Operand 32), W 47⟩,
    ⟨(.reg 11 : Operand 32), W 45⟩,
    ⟨(.reg 12 : Operand 32), W 44⟩,
    ⟨(.reg 14 : Operand 32), W 40⟩,
    ⟨(.reg 15 : Operand 32), W 33⟩,
    ⟨(.mem (stack + 0) : Operand 32), W 41⟩,
    ⟨(.mem (stack + 4) : Operand 32), W 37⟩,
    ⟨(.mem (stack + 8) : Operand 32), W 36⟩,
    ⟨(.mem (stack + 16) : Operand 32), W 45⟩,
    ⟨(.mem (stack + 24) : Operand 32), W 42⟩,
    ⟨(.mem (stack + 32) : Operand 32), W 38⟩,
    ⟨(.mem (stack + 40) : Operand 32), W 39⟩,
    ⟨(.mem (stack + 48) : Operand 32), W 47⟩,
    ⟨(.mem (stack + 56) : Operand 32), W 35⟩,
    ⟨(.mem (stack + 64) : Operand 64), input⟩,
    ⟨(.mem (stack + 72) : Operand 32), W 46⟩,
    ⟨(.mem (stack + 80) : Operand 32), W 43⟩,
    ⟨(.mem (stack + 88) : Operand 32), W 34⟩,
    ⟨(.mem (stack + 116) : Operand 32), H[0]⟩,
    ⟨(.mem (stack + 120) : Operand 32), H[3]⟩,
    ⟨(.mem (stack + 124) : Operand 32), H[4]⟩,
    ⟨(.mem (stack + 144) : Operand 32), H[2]⟩,
    ⟨(.mem (stack + 152) : Operand 32), H[1]⟩]


private def genericCut049 (stack input : BitVec 64) (H : Vector (BitVec 32) 5)
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) : List Write :=
  [⟨(.reg 0 : Operand 32), (A 45)⟩,
    ⟨(.reg 1 : Operand 32), ((A 44)).rotateLeft 30⟩,
    ⟨(.reg 2 : Operand 32), (A 46)⟩,
    ⟨(.reg 3 : Operand 32), W 32⟩,
    ⟨(.reg 5 : Operand 32), W 42⟩,
    ⟨(.reg 7 : Operand 32), (A 47)⟩,
    ⟨(.reg 10 : Operand 32), (W 47 + ((A 43)).rotateLeft 30)⟩,
    ⟨(.reg 11 : Operand 32), W 45⟩,
    ⟨(.reg 12 : Operand 32), W 44⟩,
    ⟨(.reg 14 : Operand 32), W 40⟩,
    ⟨(.reg 15 : Operand 32), W 33⟩,
    ⟨(.mem (stack + 0) : Operand 32), W 41⟩,
    ⟨(.mem (stack + 4) : Operand 32), W 37⟩,
    ⟨(.mem (stack + 8) : Operand 32), W 36⟩,
    ⟨(.mem (stack + 16) : Operand 32), W 45⟩,
    ⟨(.mem (stack + 24) : Operand 32), W 42⟩,
    ⟨(.mem (stack + 32) : Operand 32), W 38⟩,
    ⟨(.mem (stack + 40) : Operand 32), W 39⟩,
    ⟨(.mem (stack + 48) : Operand 32), W 47⟩,
    ⟨(.mem (stack + 56) : Operand 32), W 35⟩,
    ⟨(.mem (stack + 64) : Operand 64), input⟩,
    ⟨(.mem (stack + 72) : Operand 32), W 46⟩,
    ⟨(.mem (stack + 80) : Operand 32), W 43⟩,
    ⟨(.mem (stack + 88) : Operand 32), W 34⟩,
    ⟨(.mem (stack + 116) : Operand 32), H[0]⟩,
    ⟨(.mem (stack + 120) : Operand 32), H[3]⟩,
    ⟨(.mem (stack + 124) : Operand 32), H[4]⟩,
    ⟨(.mem (stack + 144) : Operand 32), H[2]⟩,
    ⟨(.mem (stack + 152) : Operand 32), H[1]⟩]


private def genericCut050 (stack input : BitVec 64) (H : Vector (BitVec 32) 5)
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) : List Write :=
  [⟨(.reg 0 : Operand 32), ((A 45)).rotateLeft 30⟩,
    ⟨(.reg 1 : Operand 32), ((A 44)).rotateLeft 30⟩,
    ⟨(.reg 2 : Operand 32), ((A 46)).rotateLeft 30⟩,
    ⟨(.reg 3 : Operand 32), W 32⟩,
    ⟨(.reg 5 : Operand 32), W 42⟩,
    ⟨(.reg 6 : Operand 32), (A 48)⟩,
    ⟨(.reg 7 : Operand 32), (A 47)⟩,
    ⟨(.reg 11 : Operand 32), W 45⟩,
    ⟨(.reg 12 : Operand 32), W 44⟩,
    ⟨(.reg 14 : Operand 32), W 40⟩,
    ⟨(.reg 15 : Operand 32), W 33⟩,
    ⟨(.mem (stack + 0) : Operand 32), W 41⟩,
    ⟨(.mem (stack + 4) : Operand 32), W 37⟩,
    ⟨(.mem (stack + 8) : Operand 32), W 36⟩,
    ⟨(.mem (stack + 16) : Operand 32), W 45⟩,
    ⟨(.mem (stack + 24) : Operand 32), W 42⟩,
    ⟨(.mem (stack + 32) : Operand 32), W 38⟩,
    ⟨(.mem (stack + 40) : Operand 32), W 39⟩,
    ⟨(.mem (stack + 48) : Operand 32), W 47⟩,
    ⟨(.mem (stack + 56) : Operand 32), W 35⟩,
    ⟨(.mem (stack + 64) : Operand 64), input⟩,
    ⟨(.mem (stack + 72) : Operand 32), W 46⟩,
    ⟨(.mem (stack + 80) : Operand 32), W 43⟩,
    ⟨(.mem (stack + 88) : Operand 32), W 34⟩,
    ⟨(.mem (stack + 116) : Operand 32), H[0]⟩,
    ⟨(.mem (stack + 120) : Operand 32), H[3]⟩,
    ⟨(.mem (stack + 124) : Operand 32), H[4]⟩,
    ⟨(.mem (stack + 144) : Operand 32), H[2]⟩,
    ⟨(.mem (stack + 152) : Operand 32), H[1]⟩]


private def genericCut051 (stack input : BitVec 64) (H : Vector (BitVec 32) 5)
    (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32) : List Write :=
  [⟨(.reg 0 : Operand 32), ((A 45)).rotateLeft 30⟩,
    ⟨(.reg 1 : Operand 32), (A 49)⟩,
    ⟨(.reg 2 : Operand 32), ((A 46)).rotateLeft 30⟩,
    ⟨(.reg 3 : Operand 32), W 48⟩,
    ⟨(.reg 5 : Operand 32), W 42⟩,
    ⟨(.reg 6 : Operand 32), (A 48)⟩,
    ⟨(.reg 7 : Operand 32), (A 47)⟩,
    ⟨(.reg 12 : Operand 32), W 44⟩,
    ⟨(.reg 13 : Operand 32), W 34⟩,
    ⟨(.reg 14 : Operand 32), W 40⟩,
    ⟨(.reg 15 : Operand 32), W 33⟩,
    ⟨(.mem (stack + 0) : Operand 32), W 41⟩,
    ⟨(.mem (stack + 4) : Operand 32), W 37⟩,
    ⟨(.mem (stack + 8) : Operand 32), W 36⟩,
    ⟨(.mem (stack + 12) : Operand 32), W 48⟩,
    ⟨(.mem (stack + 16) : Operand 32), W 45⟩,
    ⟨(.mem (stack + 24) : Operand 32), W 42⟩,
    ⟨(.mem (stack + 32) : Operand 32), W 38⟩,
    ⟨(.mem (stack + 40) : Operand 32), W 39⟩,
    ⟨(.mem (stack + 48) : Operand 32), W 47⟩,
    ⟨(.mem (stack + 56) : Operand 32), W 35⟩,
    ⟨(.mem (stack + 64) : Operand 64), input⟩,
    ⟨(.mem (stack + 72) : Operand 32), W 46⟩,
    ⟨(.mem (stack + 80) : Operand 32), W 43⟩,
    ⟨(.mem (stack + 116) : Operand 32), H[0]⟩,
    ⟨(.mem (stack + 120) : Operand 32), H[3]⟩,
    ⟨(.mem (stack + 124) : Operand 32), H[4]⟩,
    ⟨(.mem (stack + 144) : Operand 32), H[2]⟩,
    ⟨(.mem (stack + 152) : Operand 32), H[1]⟩]

set_option maxHeartbeats 1600000 in
theorem effect045_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s) (he : (effect045 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have hfoot : ∀ c ∈ (effect045 s).components, c ∈ [.mem ((Operand.reg 4 : Operand 64).read s + 0) 4, .reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] := by
    unfold effect045
    iterate 18 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [addEaxImm32Effect_components, addR32R32Effect_components, andR32R32Effect_components, movM32R32Effect_components, movR32R32Effect_components, movR64M64Effect_components, movR64R64Effect_components, rolR32Effect_components, xorR32M32LowEffect_components, xorR32R32Effect_components, List.mem_cons, List.not_mem_nil,
       or_false, or_imp, forall_and, forall_eq, or_true]
    all_goals x86_norm
  have ha := he.agrees.mono hfoot
  rw [hs] at ha
  apply ha.widen
  · intro c hc hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all (config := {decide := true}) only [Component.isMem, scratchComponents, x86_compose]
  · intro address c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hCov.elim
      | exact scratchComponents_stack (Or.inl (by decide +kernel)) hCov

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 16384 in
set_option maxHeartbeats 1600000 in
private theorem genericWords045 {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    {M : Vector (BitVec 32) 16} (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32)
    (hWork : A 45 = (A 44).rotateLeft 5 + (((A 43) &&& ((A 42).rotateLeft 30)) ^^^ ((A 43) &&& ((A 41).rotateLeft 30)) ^^^ (((A 42).rotateLeft 30) &&& ((A 41).rotateLeft 30))) + (A 40).rotateLeft 30 + 0x8f1bbcdc + W 44) (hW44 : W 44 = (W 41 ^^^ W 36 ^^^ W 30 ^^^ W 28).rotateLeft 1)
    {s t : RamState} (hf : FrameData stack input M s)
    (hw : Write.AllHold s (genericCut045 stack input H A W))
    (he : (effect045 s).Holds s t) :
    Write.AllHold t (genericCut046 stack input H A W) := by
  have hfull : ∀ w ∈ (effect045 s).writes, w.Full := by
    apply Effect.Local.full
    unfold effect045
    repeat' first | (solve | x86_local) | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have hLow (a : BitVec 64) :
      ((Operand.mem a : Operand 64).read s).setWidth 32 =
        (Operand.mem a : Operand 32).read s := memLoad_low32 s.external a
  x86_norm at hs
  simp only [genericCut045, Write.AllHold] at hw
  obtain ⟨h0,h1,h2,h5,h6,h7,h8,h10,h12,h13,h14,h15,hM4,hM8,hM12,hM24,hM32,hM40,hM48,hM56,hM64,hM72,hM80,hM88,hM96,hM116,hM120,hM124,hM144,hM152⟩ := hw
  x86_norm at h0 h1 h2 h5 h6 h7 h8 h10 h12 h13 h14 h15 hM4 hM8 hM12 hM24 hM32 hM40 hM48 hM56 hM64 hM72 hM80 hM88 hM96 hM116 hM120 hM124 hM144 hM152
  simp only [genericCut046, Write.AllHold, ← ho.read_reg, ← ho.read_mem]
  x86_norm [effect045, hs, leaSpec]
  simp only [h0,h1,h2,h5,h6,h7,h8,h10,h12,h13,h14,h15,hM4,hM8,hM12,hM24,hM32,hM40,hM48,hM56,hM64,hM72,hM80,hM88,hM96,hM116,hM120,hM124,hM144,hM152]
  simp (config := {decide := true}) only [BitVec.setWidth_setWidth_of_le,
    BitVec.setWidth_eq, ← BitVec.setWidth_eq_extractLsb',
    read32_memStore64_low, hLow]
  try simp only [h0,h1,h2,h5,h6,h7,h8,h10,h12,h13,h14,h15,hM4,hM8,hM12,hM24,hM32,hM40,hM48,hM56,hM64,hM72,hM80,hM88,hM96,hM116,hM120,hM124,hM144,hM152]
  simp only [hWork,hW44]
  try simp only [BitVec.ofNat_eq_ofNat]
  repeat' first | apply And.intro | exact True.intro
  all_goals (
    try simp only [← sha1Maj_eq_xor]
    try simp only [Standards.NIST.SHA2.SHA256.Maj, BitVec.and_comm]
    all_goals ac_rfl)

theorem effect045_words {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s)
    (hw : Write.AllHold s (cut045 stack input H M))
    (he : (effect045 s).Holds s t) :
    Write.AllHold t (cut046 stack input H M) := by
  apply genericWords045 (fun n => (workingAfter M H n).a) (scheduleWord M)
  · have hWork := workingAfter_step_a_values M H 40 (by decide +kernel)
    simp only [Nat.reduceAdd] at hWork
    rw [sha1_f_majority (t := ⟨44, by decide⟩) (by decide) (by decide),
      sha1_K_majority (t := ⟨44, by decide⟩) (by decide) (by decide)] at hWork
    simp only [Standards.NIST.SHA2.SHA256.Maj] at hWork
    exact hWork
  · have hSchedule := scheduleWord_recurrence M ⟨44, by decide⟩ (by decide +kernel)
    simp only [Nat.reduceSub] at hSchedule
    rw [sha1Rotl_eq_rotateLeft 1 _ (by decide)] at hSchedule
    exact hSchedule
  · exact hf
  · exact hw
  · exact he

theorem effect045_rip {s t : RamState} (he : (effect045 s).Holds s t) :
    t.RIP = 0x102ec4 := by
  exact he.rip.trans (by rfl)

theorem segment045 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x102e83 0x102ec4 cut045 cut046 := by
  have hout : ∀ d : Nat, d ≤ bytes045.length →
      0x102e83 + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    apply outsideCompression_ne hOutside <;>
      simp only [bytes045, List.length_cons, List.length_nil] at hd <;>
      simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega
  apply Segment.of_block (fun _ _ _ _ => effect045)
    (fun stack input H M => block045 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64 0x2e83) bytes045,
      x ∈ Extracted.programImage
    exact program_text_subset 0x2e83 (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact effect045_rip he
  · intro stack input H M s t _ hf _ he
    exact effect045_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect045_words hf hw he

set_option maxHeartbeats 1600000 in
theorem effect046_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s) (he : (effect046 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have hfoot : ∀ c ∈ (effect046 s).components, c ∈ [.mem ((Operand.reg 4 : Operand 64).read s + 72) 8, .reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] := by
    unfold effect046
    iterate 14 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [addR32R32Effect_components, andR32R32Effect_components, movM64R64Effect_components, movR32M32LowEffect_components, movR32R32Effect_components, movR64M64Effect_components, movR64R64Effect_components, rolR32Effect_components, xorR32R32Effect_components, List.mem_cons, List.not_mem_nil,
       or_false, or_imp, forall_and, forall_eq, or_true]
    all_goals x86_norm
  have ha := he.agrees.mono hfoot
  rw [hs] at ha
  apply ha.widen
  · intro c hc hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all (config := {decide := true}) only [Component.isMem, scratchComponents, x86_compose]
  · intro address c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hCov.elim
      | exact scratchComponents_stack (Or.inl (by decide +kernel)) hCov

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 16384 in
set_option maxHeartbeats 1600000 in
private theorem genericWords046 {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    {M : Vector (BitVec 32) 16} (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32)
    (hW46 : W 46 = (W 43 ^^^ W 38 ^^^ W 32 ^^^ W 30).rotateLeft 1)
    {s t : RamState} (hf : FrameData stack input M s)
    (hw : Write.AllHold s (genericCut046 stack input H A W))
    (he : (effect046 s).Holds s t) :
    Write.AllHold t (genericCut047 stack input H A W) := by
  have hfull : ∀ w ∈ (effect046 s).writes, w.Full := by
    apply Effect.Local.full
    unfold effect046
    repeat' first | (solve | x86_local) | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have hLow (a : BitVec 64) :
      ((Operand.mem a : Operand 64).read s).setWidth 32 =
        (Operand.mem a : Operand 32).read s := memLoad_low32 s.external a
  x86_norm at hs
  simp only [genericCut046, Write.AllHold] at hw
  obtain ⟨h0,h1,h2,h5,h6,h7,h10,h11,h12,h13,h14,h15,hM0,hM4,hM8,hM12,hM24,hM32,hM40,hM48,hM56,hM64,hM80,hM88,hM116,hM120,hM124,hM144,hM152⟩ := hw
  x86_norm at h0 h1 h2 h5 h6 h7 h10 h11 h12 h13 h14 h15 hM0 hM4 hM8 hM12 hM24 hM32 hM40 hM48 hM56 hM64 hM80 hM88 hM116 hM120 hM124 hM144 hM152
  simp only [genericCut047, Write.AllHold, ← ho.read_reg, ← ho.read_mem]
  x86_norm [effect046, hs, leaSpec]
  simp only [h0,h1,h2,h5,h6,h7,h10,h11,h12,h13,h14,h15,hM0,hM4,hM8,hM12,hM24,hM32,hM40,hM48,hM56,hM64,hM80,hM88,hM116,hM120,hM124,hM144,hM152]
  simp (config := {decide := true}) only [BitVec.setWidth_setWidth_of_le,
    BitVec.setWidth_eq, ← BitVec.setWidth_eq_extractLsb',
    read32_memStore64_low, hLow]
  try simp only [h0,h1,h2,h5,h6,h7,h10,h11,h12,h13,h14,h15,hM0,hM4,hM8,hM12,hM24,hM32,hM40,hM48,hM56,hM64,hM80,hM88,hM116,hM120,hM124,hM144,hM152]
  simp only [hW46]
  try simp only [BitVec.ofNat_eq_ofNat]
  repeat' first | apply And.intro | exact True.intro
  all_goals (
    try simp only [BitVec.and_comm ((A 42).rotateLeft 30) ((A 43).rotateLeft 30)]
    try simp only [← sha1Maj_eq_xor]
    try simp only [Standards.NIST.SHA2.SHA256.Maj, BitVec.and_comm]
    all_goals ac_rfl)

theorem effect046_words {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s)
    (hw : Write.AllHold s (cut046 stack input H M))
    (he : (effect046 s).Holds s t) :
    Write.AllHold t (cut047 stack input H M) := by
  apply genericWords046 (fun n => (workingAfter M H n).a) (scheduleWord M)
  · have hSchedule := scheduleWord_recurrence M ⟨46, by decide⟩ (by decide +kernel)
    simp only [Nat.reduceSub] at hSchedule
    rw [sha1Rotl_eq_rotateLeft 1 _ (by decide)] at hSchedule
    exact hSchedule
  · exact hf
  · exact hw
  · exact he

theorem effect046_rip {s t : RamState} (he : (effect046 s).Holds s t) :
    t.RIP = 0x102ef5 := by
  exact he.rip.trans (by rfl)

theorem segment046 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x102ec4 0x102ef5 cut046 cut047 := by
  have hout : ∀ d : Nat, d ≤ bytes046.length →
      0x102ec4 + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    apply outsideCompression_ne hOutside <;>
      simp only [bytes046, List.length_cons, List.length_nil] at hd <;>
      simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega
  apply Segment.of_block (fun _ _ _ _ => effect046)
    (fun stack input H M => block046 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64 0x2ec4) bytes046,
      x ∈ Extracted.programImage
    exact program_text_subset 0x2ec4 (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact effect046_rip he
  · intro stack input H M s t _ hf _ he
    exact effect046_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect046_words hf hw he

set_option maxHeartbeats 1600000 in
theorem effect047_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s) (he : (effect047 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have hfoot : ∀ c ∈ (effect047 s).components, c ∈ [.mem ((Operand.reg 4 : Operand 64).read s + 48) 8, .mem ((Operand.reg 4 : Operand 64).read s + 16) 8, .reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] := by
    unfold effect047
    iterate 17 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [addR32Imm32Effect_components, addR32R32Effect_components, movM64R64Effect_components, movR32R32Effect_components, movR64M64Effect_components, movR64R64Effect_components, rolR32Effect_components, xorR32M32Effect_components, xorR32R32Effect_components, List.mem_cons, List.not_mem_nil,
       or_false, or_imp, forall_and, forall_eq, or_true]
    all_goals x86_norm
  have ha := he.agrees.mono hfoot
  rw [hs] at ha
  apply ha.widen
  · intro c hc hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all (config := {decide := true}) only [Component.isMem, scratchComponents, x86_compose]
  · intro address c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hCov.elim
      | exact scratchComponents_stack (Or.inl (by decide +kernel)) hCov

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 16384 in
set_option maxHeartbeats 1600000 in
private theorem genericWords047 {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    {M : Vector (BitVec 32) 16} (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32)
    (hWork : A 46 = (A 45).rotateLeft 5 + (((A 44) &&& ((A 43).rotateLeft 30)) ^^^ ((A 44) &&& ((A 42).rotateLeft 30)) ^^^ (((A 43).rotateLeft 30) &&& ((A 42).rotateLeft 30))) + (A 41).rotateLeft 30 + 0x8f1bbcdc + W 45) (hW45 : W 45 = (W 42 ^^^ W 37 ^^^ W 31 ^^^ W 29).rotateLeft 1) (hW47 : W 47 = (W 44 ^^^ W 39 ^^^ W 33 ^^^ W 31).rotateLeft 1)
    {s t : RamState} (hf : FrameData stack input M s)
    (hw : Write.AllHold s (genericCut047 stack input H A W))
    (he : (effect047 s).Holds s t) :
    Write.AllHold t (genericCut048 stack input H A W) := by
  have hfull : ∀ w ∈ (effect047 s).writes, w.Full := by
    apply Effect.Local.full
    unfold effect047
    repeat' first | (solve | x86_local) | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have hLow (a : BitVec 64) :
      ((Operand.mem a : Operand 64).read s).setWidth 32 =
        (Operand.mem a : Operand 32).read s := memLoad_low32 s.external a
  x86_norm at hs
  simp only [genericCut047, Write.AllHold] at hw
  obtain ⟨h0,h1,h2,h3,h6,h7,h8,h9,h12,h13,h14,h15,hM0,hM4,hM8,hM24,hM32,hM40,hM56,hM64,hM72,hM80,hM88,hM116,hM120,hM124,hM144,hM152⟩ := hw
  x86_norm at h0 h1 h2 h3 h6 h7 h8 h9 h12 h13 h14 h15 hM0 hM4 hM8 hM24 hM32 hM40 hM56 hM64 hM72 hM80 hM88 hM116 hM120 hM124 hM144 hM152
  simp only [genericCut048, Write.AllHold, ← ho.read_reg, ← ho.read_mem]
  x86_norm [effect047, hs, leaSpec]
  simp only [h0,h1,h2,h3,h6,h7,h8,h9,h12,h13,h14,h15,hM0,hM4,hM8,hM24,hM32,hM40,hM56,hM64,hM72,hM80,hM88,hM116,hM120,hM124,hM144,hM152]
  simp (config := {decide := true}) only [BitVec.setWidth_setWidth_of_le,
    BitVec.setWidth_eq, ← BitVec.setWidth_eq_extractLsb',
    read32_memStore64_low, hLow]
  try simp only [h0,h1,h2,h3,h6,h7,h8,h9,h12,h13,h14,h15,hM0,hM4,hM8,hM24,hM32,hM40,hM56,hM64,hM72,hM80,hM88,hM116,hM120,hM124,hM144,hM152]
  simp only [hWork,hW45,hW47]
  try simp only [BitVec.ofNat_eq_ofNat]
  repeat' first | apply And.intro | exact True.intro
  all_goals (
    try simp only [← sha1Maj_eq_xor]
    try simp only [Standards.NIST.SHA2.SHA256.Maj, BitVec.and_comm]
    all_goals ac_rfl)

theorem effect047_words {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s)
    (hw : Write.AllHold s (cut047 stack input H M))
    (he : (effect047 s).Holds s t) :
    Write.AllHold t (cut048 stack input H M) := by
  apply genericWords047 (fun n => (workingAfter M H n).a) (scheduleWord M)
  · have hWork := workingAfter_step_a_values M H 41 (by decide +kernel)
    simp only [Nat.reduceAdd] at hWork
    rw [sha1_f_majority (t := ⟨45, by decide⟩) (by decide) (by decide),
      sha1_K_majority (t := ⟨45, by decide⟩) (by decide) (by decide)] at hWork
    simp only [Standards.NIST.SHA2.SHA256.Maj] at hWork
    exact hWork
  · have hSchedule := scheduleWord_recurrence M ⟨45, by decide⟩ (by decide +kernel)
    simp only [Nat.reduceSub] at hSchedule
    rw [sha1Rotl_eq_rotateLeft 1 _ (by decide)] at hSchedule
    exact hSchedule
  · have hSchedule := scheduleWord_recurrence M ⟨47, by decide⟩ (by decide +kernel)
    simp only [Nat.reduceSub] at hSchedule
    rw [sha1Rotl_eq_rotateLeft 1 _ (by decide)] at hSchedule
    exact hSchedule
  · exact hf
  · exact hw
  · exact he

theorem effect047_rip {s t : RamState} (he : (effect047 s).Holds s t) :
    t.RIP = 0x102f35 := by
  exact he.rip.trans (by rfl)

theorem segment047 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x102ef5 0x102f35 cut047 cut048 := by
  have hout : ∀ d : Nat, d ≤ bytes047.length →
      0x102ef5 + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    apply outsideCompression_ne hOutside <;>
      simp only [bytes047, List.length_cons, List.length_nil] at hd <;>
      simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega
  apply Segment.of_block (fun _ _ _ _ => effect047)
    (fun stack input H M => block047 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64 0x2ef5) bytes047,
      x ∈ Extracted.programImage
    exact program_text_subset 0x2ef5 (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact effect047_rip he
  · intro stack input H M s t _ hf _ he
    exact effect047_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect047_words hf hw he

set_option maxHeartbeats 1600000 in
theorem effect048_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s) (he : (effect048 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have hfoot : ∀ c ∈ (effect048 s).components, c ∈ [.reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] := by
    unfold effect048
    iterate 11 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [addR32Imm32Effect_components, addR32R32Effect_components, andR32R32Effect_components, leaR32Effect_components, movR32R32Effect_components, rolR32Effect_components, xorR32R32Effect_components, List.mem_cons, List.not_mem_nil,
       or_false, or_imp, forall_and, forall_eq]
    all_goals x86_norm
  have ha := he.agrees.mono hfoot
  clear hs
  apply ha.widen
  · intro c hc hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all (config := {decide := true}) only [scratchComponents, x86_compose]
  · intro address c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hCov.elim
      | exact scratchComponents_stack (Or.inl (by decide +kernel)) hCov

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 16384 in
set_option maxHeartbeats 1600000 in
private theorem genericWords048 {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    {M : Vector (BitVec 32) 16} (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32)
    (hWork : A 47 = (A 46).rotateLeft 5 + (((A 45) &&& ((A 44).rotateLeft 30)) ^^^ ((A 45) &&& ((A 43).rotateLeft 30)) ^^^ (((A 44).rotateLeft 30) &&& ((A 43).rotateLeft 30))) + (A 42).rotateLeft 30 + 0x8f1bbcdc + W 46)
    {s t : RamState} (hf : FrameData stack input M s)
    (hw : Write.AllHold s (genericCut048 stack input H A W))
    (he : (effect048 s).Holds s t) :
    Write.AllHold t (genericCut049 stack input H A W) := by
  have hfull : ∀ w ∈ (effect048 s).writes, w.Full := by
    apply Effect.Local.full
    unfold effect048
    repeat' first | (solve | x86_local) | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  x86_norm at hs
  simp only [genericCut048, Write.AllHold] at hw
  obtain ⟨h0,h1,h2,h3,h5,h7,h8,h9,h11,h12,h14,h15,hM0,hM4,hM8,hM16,hM24,hM32,hM40,hM48,hM56,hM64,hM72,hM80,hM88,hM116,hM120,hM124,hM144,hM152⟩ := hw
  x86_norm at h0 h1 h2 h3 h5 h7 h8 h9 h11 h12 h14 h15 hM0 hM4 hM8 hM16 hM24 hM32 hM40 hM48 hM56 hM64 hM72 hM80 hM88 hM116 hM120 hM124 hM144 hM152
  simp only [genericCut049, Write.AllHold, ← ho.read_reg, ← ho.read_mem]
  x86_norm [effect048, hs, leaSpec, BitVec.setWidth_add, BitVec.shiftLeft_zero]
  simp only [h0,h1,h2,h3,h5,h7,h8,h9,h11,h12,h14,h15,hM0,hM4,hM8,hM16,hM24,hM32,hM40,hM48,hM56,hM64,hM72,hM80,hM88,hM116,hM120,hM124,hM144,hM152]
  simp (config := {decide := true}) only [BitVec.setWidth_setWidth_of_le,
    BitVec.setWidth_eq, ← BitVec.setWidth_eq_extractLsb',
    read32_memStore64_low]
  try simp only [h0,h1,h2,h3,h5,h7,h8,h9,h11,h12,h14,h15,hM0,hM4,hM8,hM16,hM24,hM32,hM40,hM48,hM56,hM64,hM72,hM80,hM88,hM116,hM120,hM124,hM144,hM152]
  simp only [hWork]
  try simp only [BitVec.ofNat_eq_ofNat]
  repeat' first | apply And.intro | exact True.intro
  all_goals (
    try simp only [BitVec.and_comm ((A 43).rotateLeft 30) ((A 44).rotateLeft 30)]
    try simp only [← sha1Maj_eq_xor]
    try simp only [Standards.NIST.SHA2.SHA256.Maj, BitVec.and_comm]
    all_goals ac_rfl)

theorem effect048_words {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s)
    (hw : Write.AllHold s (cut048 stack input H M))
    (he : (effect048 s).Holds s t) :
    Write.AllHold t (cut049 stack input H M) := by
  apply genericWords048 (fun n => (workingAfter M H n).a) (scheduleWord M)
  · have hWork := workingAfter_step_a_values M H 42 (by decide +kernel)
    simp only [Nat.reduceAdd] at hWork
    rw [sha1_f_majority (t := ⟨46, by decide⟩) (by decide) (by decide),
      sha1_K_majority (t := ⟨46, by decide⟩) (by decide) (by decide)] at hWork
    simp only [Standards.NIST.SHA2.SHA256.Maj] at hWork
    exact hWork
  · exact hf
  · exact hw
  · exact he

theorem effect048_rip {s t : RamState} (he : (effect048 s).Holds s t) :
    t.RIP = 0x102f56 := by
  exact he.rip.trans (by rfl)

theorem segment048 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x102f35 0x102f56 cut048 cut049 := by
  have hout : ∀ d : Nat, d ≤ bytes048.length →
      0x102f35 + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    apply outsideCompression_ne hOutside <;>
      simp only [bytes048, List.length_cons, List.length_nil] at hd <;>
      simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega
  apply Segment.of_block (fun _ _ _ _ => effect048)
    (fun stack input H M => block048 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64 0x2f35) bytes048,
      x ∈ Extracted.programImage
    exact program_text_subset 0x2f35 (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact effect048_rip he
  · intro stack input H M s t _ hf _ he
    exact effect048_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect048_words hf hw he

set_option maxHeartbeats 1600000 in
theorem effect049_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s) (he : (effect049 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have hfoot : ∀ c ∈ (effect049 s).components, c ∈ [.reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] := by
    unfold effect049
    iterate 12 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [addR32Imm32Effect_components, addR32R32Effect_components, andR32R32Effect_components, movR32R32Effect_components, rolR32Effect_components, xorR32R32Effect_components, List.mem_cons, List.not_mem_nil,
       or_false, or_imp, forall_and, forall_eq]
    all_goals x86_norm
  have ha := he.agrees.mono hfoot
  clear hs
  apply ha.widen
  · intro c hc hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all (config := {decide := true}) only [scratchComponents, x86_compose]
  · intro address c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hCov.elim
      | exact scratchComponents_stack (Or.inl (by decide +kernel)) hCov

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 16384 in
set_option maxHeartbeats 1600000 in
private theorem genericWords049 {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    {M : Vector (BitVec 32) 16} (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32)
    (hWork : A 48 = (A 47).rotateLeft 5 + (((A 46) &&& ((A 45).rotateLeft 30)) ^^^ ((A 46) &&& ((A 44).rotateLeft 30)) ^^^ (((A 45).rotateLeft 30) &&& ((A 44).rotateLeft 30))) + (A 43).rotateLeft 30 + 0x8f1bbcdc + W 47)
    {s t : RamState} (hf : FrameData stack input M s)
    (hw : Write.AllHold s (genericCut049 stack input H A W))
    (he : (effect049 s).Holds s t) :
    Write.AllHold t (genericCut050 stack input H A W) := by
  have hfull : ∀ w ∈ (effect049 s).writes, w.Full := by
    apply Effect.Local.full
    unfold effect049
    repeat' first | (solve | x86_local) | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  x86_norm at hs
  simp only [genericCut049, Write.AllHold] at hw
  obtain ⟨h0,h1,h2,h3,h5,h7,h10,h11,h12,h14,h15,hM0,hM4,hM8,hM16,hM24,hM32,hM40,hM48,hM56,hM64,hM72,hM80,hM88,hM116,hM120,hM124,hM144,hM152⟩ := hw
  x86_norm at h0 h1 h2 h3 h5 h7 h10 h11 h12 h14 h15 hM0 hM4 hM8 hM16 hM24 hM32 hM40 hM48 hM56 hM64 hM72 hM80 hM88 hM116 hM120 hM124 hM144 hM152
  simp only [genericCut050, Write.AllHold, ← ho.read_reg, ← ho.read_mem]
  x86_norm [effect049, hs, leaSpec]
  simp only [h0,h1,h2,h3,h5,h7,h10,h11,h12,h14,h15,hM0,hM4,hM8,hM16,hM24,hM32,hM40,hM48,hM56,hM64,hM72,hM80,hM88,hM116,hM120,hM124,hM144,hM152]
  simp (config := {decide := true}) only [BitVec.setWidth_setWidth_of_le,
    BitVec.setWidth_eq, ← BitVec.setWidth_eq_extractLsb',
    read32_memStore64_low]
  try simp only [h0,h1,h2,h3,h5,h7,h10,h11,h12,h14,h15,hM0,hM4,hM8,hM16,hM24,hM32,hM40,hM48,hM56,hM64,hM72,hM80,hM88,hM116,hM120,hM124,hM144,hM152]
  simp only [hWork]
  try simp only [BitVec.ofNat_eq_ofNat]
  repeat' first | apply And.intro | exact True.intro
  all_goals (
    try simp only [← sha1Maj_eq_xor]
    try simp only [Standards.NIST.SHA2.SHA256.Maj, BitVec.and_comm]
    all_goals ac_rfl)

theorem effect049_words {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s)
    (hw : Write.AllHold s (cut049 stack input H M))
    (he : (effect049 s).Holds s t) :
    Write.AllHold t (cut050 stack input H M) := by
  apply genericWords049 (fun n => (workingAfter M H n).a) (scheduleWord M)
  · have hWork := workingAfter_step_a_values M H 43 (by decide +kernel)
    simp only [Nat.reduceAdd] at hWork
    rw [sha1_f_majority (t := ⟨47, by decide⟩) (by decide) (by decide),
      sha1_K_majority (t := ⟨47, by decide⟩) (by decide) (by decide)] at hWork
    simp only [Standards.NIST.SHA2.SHA256.Maj] at hWork
    exact hWork
  · exact hf
  · exact hw
  · exact he

theorem effect049_rip {s t : RamState} (he : (effect049 s).Holds s t) :
    t.RIP = 0x102f7c := by
  exact he.rip.trans (by rfl)

theorem segment049 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x102f56 0x102f7c cut049 cut050 := by
  have hout : ∀ d : Nat, d ≤ bytes049.length →
      0x102f56 + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    apply outsideCompression_ne hOutside <;>
      simp only [bytes049, List.length_cons, List.length_nil] at hd <;>
      simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega
  apply Segment.of_block (fun _ _ _ _ => effect049)
    (fun stack input H M => block049 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64 0x2f56) bytes049,
      x ∈ Extracted.programImage
    exact program_text_subset 0x2f56 (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact effect049_rip he
  · intro stack input H M s t _ hf _ he
    exact effect049_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect049_words hf hw he

set_option maxHeartbeats 1600000 in
theorem effect050_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s) (he : (effect050 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have hfoot : ∀ c ∈ (effect050 s).components, c ∈ [.mem ((Operand.reg 4 : Operand 64).read s + 12) 4, .reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] := by
    unfold effect050
    iterate 19 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [addR32Imm32Effect_components, addR32R32Effect_components, andR32R32Effect_components, movM32R32Effect_components, movR32R32Effect_components, movR64M64Effect_components, rolR32Effect_components, xorR32R32Effect_components, List.mem_cons, List.not_mem_nil,
       or_false, or_imp, forall_and, forall_eq, or_true]
    all_goals x86_norm
  have ha := he.agrees.mono hfoot
  rw [hs] at ha
  apply ha.widen
  · intro c hc hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all (config := {decide := true}) only [Component.isMem, scratchComponents, x86_compose]
  · intro address c hc hCov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hCov.elim
      | exact scratchComponents_stack (Or.inl (by decide +kernel)) hCov

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 16384 in
set_option maxHeartbeats 1600000 in
private theorem genericWords050 {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    {M : Vector (BitVec 32) 16} (A : Nat → BitVec 32) (W : Fin 80 → BitVec 32)
    (hWork : A 49 = (A 48).rotateLeft 5 + (((A 47) &&& ((A 46).rotateLeft 30)) ^^^ ((A 47) &&& ((A 45).rotateLeft 30)) ^^^ (((A 46).rotateLeft 30) &&& ((A 45).rotateLeft 30))) + (A 44).rotateLeft 30 + 0x8f1bbcdc + W 48) (hW48 : W 48 = (W 45 ^^^ W 40 ^^^ W 34 ^^^ W 32).rotateLeft 1)
    {s t : RamState} (hf : FrameData stack input M s)
    (hw : Write.AllHold s (genericCut050 stack input H A W))
    (he : (effect050 s).Holds s t) :
    Write.AllHold t (genericCut051 stack input H A W) := by
  have hfull : ∀ w ∈ (effect050 s).writes, w.Full := by
    apply Effect.Local.full
    unfold effect050
    repeat' first | (solve | x86_local) | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have hLow (a : BitVec 64) :
      ((Operand.mem a : Operand 64).read s).setWidth 32 =
        (Operand.mem a : Operand 32).read s := memLoad_low32 s.external a
  x86_norm at hs
  simp only [genericCut050, Write.AllHold] at hw
  obtain ⟨h0,h1,h2,h3,h5,h6,h7,h11,h12,h14,h15,hM0,hM4,hM8,hM16,hM24,hM32,hM40,hM48,hM56,hM64,hM72,hM80,hM88,hM116,hM120,hM124,hM144,hM152⟩ := hw
  x86_norm at h0 h1 h2 h3 h5 h6 h7 h11 h12 h14 h15 hM0 hM4 hM8 hM16 hM24 hM32 hM40 hM48 hM56 hM64 hM72 hM80 hM88 hM116 hM120 hM124 hM144 hM152
  simp only [genericCut051, Write.AllHold, ← ho.read_reg, ← ho.read_mem]
  x86_norm [effect050, hs, leaSpec]
  simp only [h0,h1,h2,h3,h5,h6,h7,h11,h12,h14,h15,hM0,hM4,hM8,hM16,hM24,hM32,hM40,hM48,hM56,hM64,hM72,hM80,hM88,hM116,hM120,hM124,hM144,hM152]
  simp (config := {decide := true}) only [BitVec.setWidth_setWidth_of_le,
    BitVec.setWidth_eq, ← BitVec.setWidth_eq_extractLsb',
    read32_memStore64_low, hLow]
  try simp only [h0,h1,h2,h3,h5,h6,h7,h11,h12,h14,h15,hM0,hM4,hM8,hM16,hM24,hM32,hM40,hM48,hM56,hM64,hM72,hM80,hM88,hM116,hM120,hM124,hM144,hM152]
  simp only [hWork,hW48]
  try simp only [BitVec.ofNat_eq_ofNat]
  repeat' first | apply And.intro | exact True.intro
  all_goals (
    try simp only [← sha1Maj_eq_xor]
    try simp only [Standards.NIST.SHA2.SHA256.Maj, BitVec.and_comm]
    all_goals ac_rfl)

theorem effect050_words {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s)
    (hw : Write.AllHold s (cut050 stack input H M))
    (he : (effect050 s).Holds s t) :
    Write.AllHold t (cut051 stack input H M) := by
  apply genericWords050 (fun n => (workingAfter M H n).a) (scheduleWord M)
  · have hWork := workingAfter_step_a_values M H 44 (by decide +kernel)
    simp only [Nat.reduceAdd] at hWork
    rw [sha1_f_majority (t := ⟨48, by decide⟩) (by decide) (by decide),
      sha1_K_majority (t := ⟨48, by decide⟩) (by decide) (by decide)] at hWork
    simp only [Standards.NIST.SHA2.SHA256.Maj] at hWork
    exact hWork
  · have hSchedule := scheduleWord_recurrence M ⟨48, by decide⟩ (by decide +kernel)
    simp only [Nat.reduceSub] at hSchedule
    rw [sha1Rotl_eq_rotateLeft 1 _ (by decide)] at hSchedule
    exact hSchedule
  · exact hf
  · exact hw
  · exact he

theorem effect050_rip {s t : RamState} (he : (effect050 s).Holds s t) :
    t.RIP = 0x102fc0 := by
  exact he.rip.trans (by rfl)

theorem segment050 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x102f7c 0x102fc0 cut050 cut051 := by
  have hout : ∀ d : Nat, d ≤ bytes050.length →
      0x102f7c + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    apply outsideCompression_ne hOutside <;>
      simp only [bytes050, List.length_cons, List.length_nil] at hd <;>
      simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega
  apply Segment.of_block (fun _ _ _ _ => effect050)
    (fun stack input H M => block050 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64 0x2f7c) bytes050,
      x ∈ Extracted.programImage
    exact program_text_subset 0x2f7c (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact effect050_rip he
  · intro stack input H M s t _ hf _ he
    exact effect050_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect050_words hf hw he

theorem segments045_050 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x102e83 0x102fc0 cut045 cut051 := by
  have h0 := segment045 boundary hOutside
  have h1 := h0.seq (segment046 boundary hOutside)
  have h2 := h1.seq (segment047 boundary hOutside)
  have h3 := h2.seq (segment048 boundary hOutside)
  have h4 := h3.seq (segment049 boundary hOutside)
  have h5 := h4.seq (segment050 boundary hOutside)
  exact h5

end Sha1.Proofs.Compress.Machine
