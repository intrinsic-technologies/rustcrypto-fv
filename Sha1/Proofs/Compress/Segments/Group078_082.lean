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

def bytes078 : List UInt8 :=
  [0x42, 0x8d, 0x4, 0x3, 0x41, 0x31, 0xf0, 0x41, 0x31, 0xd0, 0x44, 0x3, 0x44, 0x24, 0x10, 0x89, 0xf9, 0xc1, 0xc1, 0x5, 0x44, 0x1, 0xc1, 0x81, 0xc1, 0xd6, 0xc1, 0x62, 0xca, 0xc1, 0xc2, 0x1e, 0x41, 0x89, 0xd0, 0x41, 0x31, 0xf0, 0x41, 0x31, 0xf8, 0x41, 0x1, 0xc0, 0x89, 0xc8, 0xc1, 0xc0, 0x5, 0x44, 0x1, 0xc0, 0x5, 0xd6, 0xc1, 0x62, 0xca]

def effect078 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq ((leaR32Effect 0x103579 4 0 (.sib 3 (some 8) 0 .none))) (xorR32R32Effect 0x10357d 3 8 6)) (xorR32R32Effect 0x103580 3 8 2)) (addR32M32Effect 0x103583 5 8 (.sib 4 none 0 (.d8 0x10)))) (movR32R32Effect 0x103588 2 1 7)) (rolR32Effect 0x10358a 3 1 5)) (addR32R32Effect 0x10358d 3 1 8)) (addR32Imm32Effect 0x103590 6 1 0xca62c1d6)) (rolR32Effect 0x103596 3 2 30)) (movR32R32Effect 0x103599 3 8 2)) (xorR32R32Effect 0x10359c 3 8 6)) (xorR32R32Effect 0x10359f 3 8 7)) (addR32R32Effect 0x1035a2 3 8 0)) (movR32R32Effect 0x1035a5 2 0 1)) (rolR32Effect 0x1035a7 3 0 5)) (addR32R32Effect 0x1035aa 3 0 8)) (addEaxImm32Effect 0x1035ad 0xca62c1d6)

set_option maxHeartbeats 1200000 in
theorem block078 [Bindings] (boundary : ReturnBoundary) (stack input : BitVec 64)
    (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes078.length →
      0x103579 + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x103579 ∧ FrameData stack input M s ∧
        Write.AllHold s (cut078 stack input H M))
      (codeRange 0x103579 bytes078) effect078 := by
  unfold bytes078 at hout ⊢
  sha1_run_begin (lea_r32_rex_effect_step 0x103579 0x42 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) 0 (.sib 3 (some 8) 0 .none) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x10357d 0x41 0xf0 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x103580 0x41 0xd0 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (add_r32_m32_rex_effect_step 0x103583 0x44 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) 0 (.sib 4 none 0 (.d8 0x10)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (mov_r32_r32_effect_step 0x103588 0xf9 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (rol_r32_imm8_effect_step 0x10358a 0xc1 0x5 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (add_r32_r32_rex_effect_step 0x10358d 0x44 0xc1 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (add_r32_imm32_effect_step 0x103590 0xc1 0xca62c1d6 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (rol_r32_imm8_effect_step 0x103596 0xc2 0x1e (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x103599 0x41 0xd0 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x10359c 0x41 0xf0 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x10359f 0x41 0xf8 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (add_r32_r32_rex_effect_step 0x1035a2 0x41 0xc0 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (mov_r32_r32_effect_step 0x1035a5 0xc8 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (rol_r32_imm8_effect_step 0x1035a7 0xc0 0x5 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (add_r32_r32_rex_effect_step 0x1035aa 0x44 0xc0 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (add_eax_imm32_effect_step 0x1035ad 0xca62c1d6)
  sha1_run_finish [effect078]

def bytes079 : List UInt8 :=
  [0x4c, 0x8b, 0x44, 0x24, 0x48, 0x45, 0x31, 0xc7, 0x45, 0x31, 0xc4, 0x4c, 0x8b, 0x44, 0x24, 0x30, 0x45, 0x31, 0xc5, 0x45, 0x31, 0xc3, 0x44, 0x33, 0x7c, 0x24, 0x8, 0x45, 0x31, 0xd5, 0x45, 0x31, 0xcc, 0x44, 0x33, 0x5c, 0x24, 0x28, 0x45, 0x31, 0xf7, 0x44, 0x33, 0x6c, 0x24, 0x18, 0x41, 0x31, 0xdc, 0xc1, 0xc7, 0x1e, 0x41, 0xd1, 0xc7, 0x45, 0x31, 0xfb, 0x41, 0x1, 0xf7, 0x89, 0xfe]

def effect079 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq ((movR64M64Effect 0x1035b2 8 (.sib 4 none 0 (.d8 0x48)))) (xorR32R32Effect 0x1035b7 3 15 8)) (xorR32R32Effect 0x1035ba 3 12 8)) (movR64M64Effect 0x1035bd 8 (.sib 4 none 0 (.d8 0x30)))) (xorR32R32Effect 0x1035c2 3 13 8)) (xorR32R32Effect 0x1035c5 3 11 8)) (xorR32M32Effect 0x1035c8 15 (.sib 4 none 0 (.d8 0x8)))) (xorR32R32Effect 0x1035cd 3 13 10)) (xorR32R32Effect 0x1035d0 3 12 9)) (xorR32M32Effect 0x1035d3 11 (.sib 4 none 0 (.d8 0x28)))) (xorR32R32Effect 0x1035d8 3 15 14)) (xorR32M32Effect 0x1035db 13 (.sib 4 none 0 (.d8 0x18)))) (xorR32R32Effect 0x1035e0 3 12 3)) (rolR32Effect 0x1035e3 3 7 30)) (rolR32Effect 0x1035e6 3 15 1)) (xorR32R32Effect 0x1035e9 3 11 15)) (addR32R32Effect 0x1035ec 3 15 6)) (movR32R32Effect 0x1035ef 2 6 7)

set_option maxHeartbeats 1200000 in
theorem block079 [Bindings] (boundary : ReturnBoundary) (stack input : BitVec 64)
    (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes079.length →
      0x1035b2 + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x1035b2 ∧ FrameData stack input M s ∧
        Write.AllHold s (cut079 stack input H M))
      (codeRange 0x1035b2 bytes079) effect079 := by
  unfold bytes079 at hout ⊢
  sha1_run_begin (mov_r64_m64_effect_step 0x1035b2 0x4c (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) 0 (.sib 4 none 0 (.d8 0x48)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x1035b7 0x45 0xc7 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x1035ba 0x45 0xc4 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (mov_r64_m64_effect_step 0x1035bd 0x4c (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) 0 (.sib 4 none 0 (.d8 0x30)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x1035c2 0x45 0xc5 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x1035c5 0x45 0xc3 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (xor_r32_m32_effect_step 0x1035c8 0x44 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) 7 (.sib 4 none 0 (.d8 0x8)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x1035cd 0x45 0xd5 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x1035d0 0x45 0xcc (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (xor_r32_m32_effect_step 0x1035d3 0x44 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) 3 (.sib 4 none 0 (.d8 0x28)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x1035d8 0x45 0xf7 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (xor_r32_m32_effect_step 0x1035db 0x44 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) 5 (.sib 4 none 0 (.d8 0x18)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x1035e0 0x41 0xdc (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (rol_r32_imm8_effect_step 0x1035e3 0xc7 0x1e (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (rol_r32_one_rex_effect_step 0x1035e6 0x41 0xc7 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x1035e9 0x45 0xfb (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (add_r32_r32_rex_effect_step 0x1035ec 0x41 0xf7 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (mov_r32_r32_effect_step 0x1035ef 0xfe (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_finish [effect079]

def bytes080 : List UInt8 :=
  [0x31, 0xd6, 0x31, 0xce, 0x41, 0x1, 0xf7, 0x89, 0xc6, 0xc1, 0xc6, 0x5, 0x46, 0x8d, 0x14, 0x3e, 0x41, 0x81, 0xc2, 0xd6, 0xc1, 0x62, 0xca, 0x41, 0xd1, 0xc5, 0x41, 0xd1, 0xc4, 0x41, 0xd1, 0xc3, 0xc1, 0xc1, 0x1e, 0x41, 0x1, 0xd5, 0x44, 0x89, 0xd2, 0xc1, 0xc2, 0x5, 0x41, 0x1, 0xfc, 0x31, 0xcf, 0x31, 0xc7, 0x41, 0x1, 0xfd, 0x44, 0x1, 0xea, 0x81, 0xc2, 0xd6, 0xc1, 0x62, 0xca]

def effect080 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq ((xorR32R32Effect 0x1035f1 2 6 2)) (xorR32R32Effect 0x1035f3 2 6 1)) (addR32R32Effect 0x1035f5 3 15 6)) (movR32R32Effect 0x1035f8 2 6 0)) (rolR32Effect 0x1035fa 3 6 5)) (leaR32Effect 0x1035fd 4 10 (.sib 6 (some 15) 0 .none))) (addR32Imm32Effect 0x103601 7 10 0xca62c1d6)) (rolR32Effect 0x103608 3 13 1)) (rolR32Effect 0x10360b 3 12 1)) (rolR32Effect 0x10360e 3 11 1)) (rolR32Effect 0x103611 3 1 30)) (addR32R32Effect 0x103614 3 13 2)) (movR32R32Effect 0x103617 3 2 10)) (rolR32Effect 0x10361a 3 2 5)) (addR32R32Effect 0x10361d 3 12 7)) (xorR32R32Effect 0x103620 2 7 1)) (xorR32R32Effect 0x103622 2 7 0)) (addR32R32Effect 0x103624 3 13 7)) (addR32R32Effect 0x103627 3 2 13)) (addR32Imm32Effect 0x10362a 6 2 0xca62c1d6)

set_option maxHeartbeats 1200000 in
theorem block080 [Bindings] (boundary : ReturnBoundary) (stack input : BitVec 64)
    (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes080.length →
      0x1035f1 + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x1035f1 ∧ FrameData stack input M s ∧
        Write.AllHold s (cut080 stack input H M))
      (codeRange 0x1035f1 bytes080) effect080 := by
  unfold bytes080 at hout ⊢
  sha1_run_begin (xor_r32_r32_effect_step 0x1035f1 0xd6 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (xor_r32_r32_effect_step 0x1035f3 0xce (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (add_r32_r32_rex_effect_step 0x1035f5 0x41 0xf7 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (mov_r32_r32_effect_step 0x1035f8 0xc6 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (rol_r32_imm8_effect_step 0x1035fa 0xc6 0x5 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (lea_r32_rex_effect_step 0x1035fd 0x46 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) 2 (.sib 6 (some 15) 0 .none) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (add_r32_imm32_rex_effect_step 0x103601 0x41 0xc2 0xca62c1d6 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (rol_r32_one_rex_effect_step 0x103608 0x41 0xc5 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (rol_r32_one_rex_effect_step 0x10360b 0x41 0xc4 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (rol_r32_one_rex_effect_step 0x10360e 0x41 0xc3 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (rol_r32_imm8_effect_step 0x103611 0xc1 0x1e (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (add_r32_r32_rex_effect_step 0x103614 0x41 0xd5 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x103617 0x44 0xd2 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (rol_r32_imm8_effect_step 0x10361a 0xc2 0x5 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (add_r32_r32_rex_effect_step 0x10361d 0x41 0xfc (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (xor_r32_r32_effect_step 0x103620 0xcf (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (xor_r32_r32_effect_step 0x103622 0xc7 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (add_r32_r32_rex_effect_step 0x103624 0x41 0xfd (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (add_r32_r32_rex_effect_step 0x103627 0x44 0xea (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (add_r32_imm32_effect_step 0x10362a 0xc2 0xca62c1d6 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_finish [effect080]

def bytes081 : List UInt8 :=
  [0xc1, 0xc0, 0x1e, 0x41, 0x89, 0xd0, 0x41, 0xc1, 0xc0, 0x5, 0x89, 0xc7, 0x31, 0xcf, 0x44, 0x31, 0xd7, 0x44, 0x1, 0xe7, 0x41, 0x89, 0xf9, 0x44, 0x1, 0xc7, 0x45, 0x1, 0xc8, 0x41, 0x81, 0xc0, 0xd6, 0xc1, 0x62, 0xca]

def effect081 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq ((rolR32Effect 0x103630 3 0 30)) (movR32R32Effect 0x103633 3 8 2)) (rolR32Effect 0x103636 4 8 5)) (movR32R32Effect 0x10363a 2 7 0)) (xorR32R32Effect 0x10363c 2 7 1)) (xorR32R32Effect 0x10363e 3 7 10)) (addR32R32Effect 0x103641 3 7 12)) (movR32R32Effect 0x103644 3 9 7)) (addR32R32Effect 0x103647 3 7 8)) (addR32R32Effect 0x10364a 3 8 9)) (addR32Imm32Effect 0x10364d 7 8 0xca62c1d6)

set_option maxHeartbeats 1200000 in
theorem block081 [Bindings] (boundary : ReturnBoundary) (stack input : BitVec 64)
    (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes081.length →
      0x103630 + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x103630 ∧ FrameData stack input M s ∧
        Write.AllHold s (cut081 stack input H M))
      (codeRange 0x103630 bytes081) effect081 := by
  unfold bytes081 at hout ⊢
  sha1_run_begin (rol_r32_imm8_effect_step 0x103630 0xc0 0x1e (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x103633 0x41 0xd0 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (rol_r32_imm8_rex_effect_step 0x103636 0x41 0xc0 0x5 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (mov_r32_r32_effect_step 0x10363a 0xc7 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (xor_r32_r32_effect_step 0x10363c 0xcf (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x10363e 0x44 0xd7 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (add_r32_r32_rex_effect_step 0x103641 0x44 0xe7 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x103644 0x41 0xf9 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (add_r32_r32_rex_effect_step 0x103647 0x44 0xc7 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (add_r32_r32_rex_effect_step 0x10364a 0x45 0xc8 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (add_r32_imm32_rex_effect_step 0x10364d 0x41 0xc0 0xca62c1d6 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_finish [effect081]

def bytes082 : List UInt8 :=
  [0x44, 0x3, 0x5c, 0x24, 0x74, 0x41, 0xc1, 0xc2, 0x1e, 0x41, 0x1, 0xcb, 0x44, 0x89, 0xd1, 0x31, 0xc1, 0x31, 0xd1, 0x41, 0x1, 0xcb, 0x48, 0x8b, 0x74, 0x24, 0x40, 0x41, 0xc1, 0xc0, 0x5, 0x45, 0x1, 0xc3, 0x41, 0x81, 0xc3, 0xd6, 0xc1, 0x62, 0xca, 0x4c, 0x8b, 0x84, 0x24, 0x98, 0x0, 0x0, 0x0, 0x41, 0x1, 0xf8, 0x41, 0x81, 0xc0, 0xd6, 0xc1, 0x62, 0xca, 0xc1, 0xc2, 0x1e, 0x3, 0x94, 0x24, 0x90, 0x0, 0x0, 0x0, 0x44, 0x3, 0x54, 0x24, 0x78, 0x3, 0x44, 0x24, 0x7c]

def effect082 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq ((addR32M32Effect 0x103654 5 11 (.sib 4 none 0 (.d8 0x74)))) (rolR32Effect 0x103659 4 10 30)) (addR32R32Effect 0x10365d 3 11 1)) (movR32R32Effect 0x103660 3 1 10)) (xorR32R32Effect 0x103663 2 1 0)) (xorR32R32Effect 0x103665 2 1 2)) (addR32R32Effect 0x103667 3 11 1)) (movR64M64Effect 0x10366a 6 (.sib 4 none 0 (.d8 0x40)))) (rolR32Effect 0x10366f 4 8 5)) (addR32R32Effect 0x103673 3 11 8)) (addR32Imm32Effect 0x103676 7 11 0xca62c1d6)) (movR64M64Effect 0x10367d 8 (.sib 4 none 0 (.d32 0x98)))) (addR32R32Effect 0x103685 3 8 7)) (addR32Imm32Effect 0x103688 7 8 0xca62c1d6)) (rolR32Effect 0x10368f 3 2 30)) (addR32M32Effect 0x103692 7 2 (.sib 4 none 0 (.d32 0x90)))) (addR32M32Effect 0x103699 5 10 (.sib 4 none 0 (.d8 0x78)))) (addR32M32Effect 0x10369e 4 0 (.sib 4 none 0 (.d8 0x7c)))

set_option maxHeartbeats 1200000 in
theorem block082 [Bindings] (boundary : ReturnBoundary) (stack input : BitVec 64)
    (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes082.length →
      0x103654 + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x103654 ∧ FrameData stack input M s ∧
        Write.AllHold s (cut082 stack input H M))
      (codeRange 0x103654 bytes082) effect082 := by
  unfold bytes082 at hout ⊢
  sha1_run_begin (add_r32_m32_rex_effect_step 0x103654 0x44 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) 3 (.sib 4 none 0 (.d8 0x74)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (rol_r32_imm8_rex_effect_step 0x103659 0x41 0xc2 0x1e (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (add_r32_r32_rex_effect_step 0x10365d 0x41 0xcb (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x103660 0x44 0xd1 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (xor_r32_r32_effect_step 0x103663 0xc1 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (xor_r32_r32_effect_step 0x103665 0xd1 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (add_r32_r32_rex_effect_step 0x103667 0x41 0xcb (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (mov_r64_m64_effect_step 0x10366a 0x48 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) 6 (.sib 4 none 0 (.d8 0x40)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (rol_r32_imm8_rex_effect_step 0x10366f 0x41 0xc0 0x5 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (add_r32_r32_rex_effect_step 0x103673 0x45 0xc3 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (add_r32_imm32_rex_effect_step 0x103676 0x41 0xc3 0xca62c1d6 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (mov_r64_m64_effect_step 0x10367d 0x4c (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) 0 (.sib 4 none 0 (.d32 0x98)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (add_r32_r32_rex_effect_step 0x103685 0x41 0xf8 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (add_r32_imm32_rex_effect_step 0x103688 0x41 0xc0 0xca62c1d6 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (rol_r32_imm8_effect_step 0x10368f 0xc2 0x1e (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (add_r32_m32_effect_step 0x103692 2 (.sib 4 none 0 (.d32 0x90)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (add_r32_m32_rex_effect_step 0x103699 0x44 (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) 2 (.sib 4 none 0 (.d8 0x78)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_then (add_r32_m32_effect_step 0x10369e 0 (.sib 4 none 0 (.d8 0x7c)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)) (by first | decide +kernel | (unfold RexNoWPrefix; decide +kernel) | (unfold RexWPrefix; decide +kernel)))
  sha1_run_finish [effect082]

set_option maxHeartbeats 1200000 in
theorem effect078_words {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s)
    (hw : Write.AllHold s (cut078 stack input H M))
    (he : (effect078 s).Holds s t) :
    Write.AllHold t (cut079 stack input H M) := by
  have hfull : ∀ w ∈ (effect078 s).writes, w.Full := by
    apply Effect.Local.full
    unfold effect078
    repeat' first | (solve | x86_local) | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  sha1_norm at hs
  simp only [cut078, Write.AllHold] at hw
  obtain ⟨h2, h3, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, hM8, hM16, hM24, hM40, hM48, hM64, hM72, hM116, hM120, hM124, hM144, hM152⟩ := hw
  sha1_norm at h2 h3 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 hM8 hM16 hM24 hM40 hM48 hM64 hM72 hM116 hM120 hM124 hM144 hM152
  simp only [cut079,  Write.AllHold, ← ho.read_reg, ← ho.read_mem]
  sha1_norm [effect078, hs]
  simp only [Operand.read] at h2 h3 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 hM8 hM16 hM24 hM40 hM48 hM64 hM72 hM116 hM120 hM124 hM144 hM152
  simp only [Operand.read, h2, h3, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, hM8, hM16, hM24, hM40, hM48, hM64, hM72, hM116, hM120, hM124, hM144, hM152]
  have hA75 := workingAfter_step_a_values M H 70 (by decide +kernel)
  change (workingAfter M H 75).a = ((workingAfter M H 74).a).rotateLeft 5 +
    ((workingAfter M H 73).a ^^^ ((workingAfter M H 72).a).rotateLeft 30 ^^^
      ((workingAfter M H 71).a).rotateLeft 30) +
    ((workingAfter M H 70).a).rotateLeft 30 + 0xca62c1d6 + scheduleWord M 74 at hA75
  have hA76 := workingAfter_step_a_values M H 71 (by decide +kernel)
  change (workingAfter M H 76).a = ((workingAfter M H 75).a).rotateLeft 5 +
    ((workingAfter M H 74).a ^^^ ((workingAfter M H 73).a).rotateLeft 30 ^^^
      ((workingAfter M H 72).a).rotateLeft 30) +
    ((workingAfter M H 71).a).rotateLeft 30 + 0xca62c1d6 + scheduleWord M 75 at hA76
  rw [hA76, hA75]
  simp (config := { decide := true, implicitDefEqProofs := false }) only [leaSpec, BitVec.setWidth_add, BitVec.shiftLeft_zero, BitVec.add_zero, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, and_true]
  try simp_all only [BitVec.ofNat_eq_ofNat]
  repeat' apply And.intro
  all_goals ac_rfl

set_option maxHeartbeats 1200000 in
theorem effect079_words {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s)
    (hw : Write.AllHold s (cut079 stack input H M))
    (he : (effect079 s).Holds s t) :
    Write.AllHold t (cut080 stack input H M) := by
  have hfull : ∀ w ∈ (effect079 s).writes, w.Full := by
    apply Effect.Local.full
    unfold effect079
    repeat' first | (solve | x86_local) | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  sha1_norm at hs
  simp only [cut079, Write.AllHold] at hw
  obtain ⟨h0, h1, h2, h3, h6, h7, h9, h10, h11, h12, h13, h14, h15, hM8, hM24, hM40, hM48, hM64, hM72, hM116, hM120, hM124, hM144, hM152⟩ := hw
  sha1_norm at h0 h1 h2 h3 h6 h7 h9 h10 h11 h12 h13 h14 h15 hM8 hM24 hM40 hM48 hM64 hM72 hM116 hM120 hM124 hM144 hM152
  simp only [cut080,  Write.AllHold, ← ho.read_reg, ← ho.read_mem]
  sha1_norm [effect079, hs]
  simp only [Operand.read] at h0 h1 h2 h3 h6 h7 h9 h10 h11 h12 h13 h14 h15 hM8 hM24 hM40 hM48 hM64 hM72 hM116 hM120 hM124 hM144 hM152
  simp only [Operand.read, h0, h1, h2, h3, h6, h7, h9, h10, h11, h12, h13, h14, h15, hM8, hM24, hM40, hM64, hM116, hM120, hM124, hM144, hM152]
  have hW76 : scheduleWord M 76 =
      (scheduleWord M 73 ^^^ scheduleWord M 68 ^^^
        scheduleWord M 62 ^^^ scheduleWord M 60).rotateLeft 1 := by
    have hh := scheduleWord_recurrence M (76 : Fin 80) (by decide +kernel)
    rw [sha1Rotl_eq_rotateLeft 1 _ (by decide +kernel)] at hh
    exact hh
  rw [hW76]
  simp (config := { decide := true, implicitDefEqProofs := false }) only [memLoad_low32, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, true_and, and_true]
  simp_all only
  repeat' apply And.intro
  all_goals first | exact True.intro | ac_rfl

set_option maxHeartbeats 1200000 in
theorem effect080_words {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s)
    (hw : Write.AllHold s (cut080 stack input H M))
    (he : (effect080 s).Holds s t) :
    Write.AllHold t (cut081 stack input H M) := by
  have hfull : ∀ w ∈ (effect080 s).writes, w.Full := by
    apply Effect.Local.full
    unfold effect080
    repeat' first | (solve | x86_local) | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  sha1_norm at hs
  simp only [cut080, Write.AllHold] at hw
  obtain ⟨h0, h1, h2, h6, h7, h11, h12, h13, h15, hM64, hM116, hM120, hM124, hM144, hM152⟩ := hw
  sha1_norm at h0 h1 h2 h6 h7 h11 h12 h13 h15 hM64 hM116 hM120 hM124 hM144 hM152
  simp only [cut081,  Write.AllHold, ← ho.read_reg, ← ho.read_mem]
  sha1_norm [effect080, hs]
  simp only [Operand.read] at h0 h1 h2 h6 h7 h11 h12 h13 h15 hM64 hM116 hM120 hM124 hM144 hM152
  simp only [Operand.read, h0, h1, h2, h6, h7, h11, h12, h13, h15, hM64, hM116, hM120, hM124, hM144, hM152]
  have hA77 := workingAfter_step_a_values M H 72 (by decide +kernel)
  change (workingAfter M H 77).a = ((workingAfter M H 76).a).rotateLeft 5 +
    ((workingAfter M H 75).a ^^^ ((workingAfter M H 74).a).rotateLeft 30 ^^^
      ((workingAfter M H 73).a).rotateLeft 30) +
    ((workingAfter M H 72).a).rotateLeft 30 + 0xca62c1d6 + scheduleWord M 76 at hA77
  have hA78 := workingAfter_step_a_values M H 73 (by decide +kernel)
  change (workingAfter M H 78).a = ((workingAfter M H 77).a).rotateLeft 5 +
    ((workingAfter M H 76).a ^^^ ((workingAfter M H 75).a).rotateLeft 30 ^^^
      ((workingAfter M H 74).a).rotateLeft 30) +
    ((workingAfter M H 73).a).rotateLeft 30 + 0xca62c1d6 + scheduleWord M 77 at hA78
  have hW78 : scheduleWord M 78 =
      (scheduleWord M 75 ^^^ scheduleWord M 70 ^^^
        scheduleWord M 64 ^^^ scheduleWord M 62).rotateLeft 1 := by
    have hh := scheduleWord_recurrence M (78 : Fin 80) (by decide +kernel)
    rw [sha1Rotl_eq_rotateLeft 1 _ (by decide +kernel)] at hh
    exact hh
  have hW79 : scheduleWord M 79 =
      (scheduleWord M 76 ^^^ scheduleWord M 71 ^^^
        scheduleWord M 65 ^^^ scheduleWord M 63).rotateLeft 1 := by
    have hh := scheduleWord_recurrence M (79 : Fin 80) (by decide +kernel)
    rw [sha1Rotl_eq_rotateLeft 1 _ (by decide +kernel)] at hh
    exact hh
  have hW77 : scheduleWord M 77 =
      (scheduleWord M 74 ^^^ scheduleWord M 69 ^^^
        scheduleWord M 63 ^^^ scheduleWord M 61).rotateLeft 1 := by
    have hh := scheduleWord_recurrence M (77 : Fin 80) (by decide +kernel)
    rw [sha1Rotl_eq_rotateLeft 1 _ (by decide +kernel)] at hh
    exact hh
  rw [hA78, hA77, hW77, hW78, hW79]
  simp (config := { decide := true, implicitDefEqProofs := false }) only [leaSpec, BitVec.setWidth_add, BitVec.shiftLeft_zero, BitVec.add_zero, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, true_and, and_true]
  try simp_all only [BitVec.ofNat_eq_ofNat]
  repeat' apply And.intro
  all_goals ac_rfl

set_option maxHeartbeats 1200000 in
theorem effect081_words {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s)
    (hw : Write.AllHold s (cut081 stack input H M))
    (he : (effect081 s).Holds s t) :
    Write.AllHold t (cut082 stack input H M) := by
  have hfull : ∀ w ∈ (effect081 s).writes, w.Full := by
    apply Effect.Local.full
    unfold effect081
    repeat' first | (solve | x86_local) | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  sha1_norm at hs
  simp only [cut081, Write.AllHold] at hw
  obtain ⟨h0, h1, h2, h10, h11, h12, hM64, hM116, hM120, hM124, hM144, hM152⟩ := hw
  sha1_norm at h0 h1 h2 h10 h11 h12 hM64 hM116 hM120 hM124 hM144 hM152
  simp only [cut082,  Write.AllHold, ← ho.read_reg, ← ho.read_mem]
  sha1_norm [effect081, hs]
  simp only [Operand.read] at h0 h1 h2 h10 h11 h12 hM64 hM116 hM120 hM124 hM144 hM152
  simp only [Operand.read, h0, h1, h2, h10, h11, h12, hM64, hM116, hM120, hM124, hM144, hM152]
  have hA79 := workingAfter_step_a_values M H 74 (by decide +kernel)
  change (workingAfter M H 79).a = ((workingAfter M H 78).a).rotateLeft 5 +
    ((workingAfter M H 77).a ^^^ ((workingAfter M H 76).a).rotateLeft 30 ^^^
      ((workingAfter M H 75).a).rotateLeft 30) +
    ((workingAfter M H 74).a).rotateLeft 30 + 0xca62c1d6 + scheduleWord M 78 at hA79
  rw [hA79]
  simp (config := { decide := true, implicitDefEqProofs := false }) only [BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, true_and, and_true]
  try simp_all only [BitVec.ofNat_eq_ofNat]
  repeat' apply And.intro
  all_goals ac_rfl

set_option maxHeartbeats 1200000 in
theorem effect082_words {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s)
    (hw : Write.AllHold s (cut082 stack input H M))
    (he : (effect082 s).Holds s t) :
    Write.AllHold t (cut083 stack input H M) := by
  have hfull : ∀ w ∈ (effect082 s).writes, w.Full := by
    apply Effect.Local.full
    unfold effect082
    repeat' first | (solve | x86_local) | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  sha1_norm at hs
  simp only [cut082, Write.AllHold] at hw
  obtain ⟨h0, h1, h2, h7, h8, h10, h11, hM64, hM116, hM120, hM124, hM144, hM152⟩ := hw
  sha1_norm at h0 h1 h2 h7 h8 h10 h11 hM64 hM116 hM120 hM124 hM144 hM152
  simp only [cut083, snapshot80, Write.AllHold, ← ho.read_reg]
  sha1_norm [effect082, hs]
  simp only [Operand.read] at h0 h1 h2 h7 h8 h10 h11 hM64 hM116 hM120 hM124 hM144 hM152
  simp only [Operand.read, h0, h1, h2, h7, h8, h10, h11, hM64, hM116, hM120, hM124, hM144]
  rw [compress_eq_a_values]
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  have hA80 := workingAfter_step_a_values M H 75 (by decide +kernel)
  change (workingAfter M H 80).a = ((workingAfter M H 79).a).rotateLeft 5 +
    ((workingAfter M H 78).a ^^^ ((workingAfter M H 77).a).rotateLeft 30 ^^^
      ((workingAfter M H 76).a).rotateLeft 30) +
    ((workingAfter M H 75).a).rotateLeft 30 + 0xca62c1d6 + scheduleWord M 79 at hA80
  have hA79 := workingAfter_step_a_values M H 74 (by decide +kernel)
  change (workingAfter M H 79).a = ((workingAfter M H 78).a).rotateLeft 5 +
    ((workingAfter M H 77).a ^^^ ((workingAfter M H 76).a).rotateLeft 30 ^^^
      ((workingAfter M H 75).a).rotateLeft 30) +
    ((workingAfter M H 74).a).rotateLeft 30 + 0xca62c1d6 + scheduleWord M 78 at hA79
  rw [hA80, hA79]
  simp (config := { decide := true, implicitDefEqProofs := false }) only [memLoad_low32, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, and_true]
  try simp_all only [BitVec.ofNat_eq_ofNat]
  repeat' apply And.intro
  all_goals ac_rfl

set_option maxHeartbeats 1200000 in
theorem effect078_agrees {stack : BitVec 64} {s t : RamState}
    (he : (effect078 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hfoot : ∀ c ∈ (effect078 s).components, c ∈ [.reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] := by
    unfold effect078
    iterate 16 apply components_seq_of
    all_goals sha1_norm
  apply he.agrees.mono
  intro c hc
  have hmem := hfoot c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [scratchComponents]

set_option maxHeartbeats 1200000 in
theorem effect079_agrees {stack : BitVec 64} {s t : RamState}
    (he : (effect079 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hfoot : ∀ c ∈ (effect079 s).components, c ∈ [.reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] := by
    unfold effect079
    iterate 17 apply components_seq_of
    all_goals sha1_norm
  apply he.agrees.mono
  intro c hc
  have hmem := hfoot c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [scratchComponents]

set_option maxHeartbeats 1200000 in
theorem effect080_agrees {stack : BitVec 64} {s t : RamState}
    (he : (effect080 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hfoot : ∀ c ∈ (effect080 s).components, c ∈ [.reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] := by
    unfold effect080
    iterate 19 apply components_seq_of
    all_goals sha1_norm
  apply he.agrees.mono
  intro c hc
  have hmem := hfoot c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [scratchComponents]

set_option maxHeartbeats 1200000 in
theorem effect081_agrees {stack : BitVec 64} {s t : RamState}
    (he : (effect081 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hfoot : ∀ c ∈ (effect081 s).components, c ∈ [.reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] := by
    unfold effect081
    iterate 10 apply components_seq_of
    all_goals sha1_norm
  apply he.agrees.mono
  intro c hc
  have hmem := hfoot c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [scratchComponents]

set_option maxHeartbeats 1200000 in
theorem effect082_agrees {stack : BitVec 64} {s t : RamState}
    (he : (effect082 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hfoot : ∀ c ∈ (effect082 s).components, c ∈ [.reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .flags, .rip] := by
    unfold effect082
    iterate 17 apply components_seq_of
    all_goals sha1_norm
  apply he.agrees.mono
  intro c hc
  have hmem := hfoot c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [scratchComponents]

theorem segment078 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x103579 0x1035b2 cut078 cut079 := by
  have hout : ∀ d : Nat, d ≤ bytes078.length →
      0x103579 + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    apply outsideCompression_ne hOutside <;>
      simp only [bytes078, List.length_cons, List.length_nil] at hd <;>
      simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega
  apply Segment.of_block (fun _ _ _ _ ↦ effect078)
    (fun stack input H M ↦ block078 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64 0x3579) bytes078,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact he.rip.trans (by rfl)
  · intro stack input H M s t _ hf _ he
    exact effect078_agrees he
  · intro stack input H M s t _ hf hw he
    exact effect078_words hf hw he

theorem segment079 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x1035b2 0x1035f1 cut079 cut080 := by
  have hout : ∀ d : Nat, d ≤ bytes079.length →
      0x1035b2 + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    apply outsideCompression_ne hOutside <;>
      simp only [bytes079, List.length_cons, List.length_nil] at hd <;>
      simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega
  apply Segment.of_block (fun _ _ _ _ ↦ effect079)
    (fun stack input H M ↦ block079 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64 0x35b2) bytes079,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact he.rip.trans (by rfl)
  · intro stack input H M s t _ hf _ he
    exact effect079_agrees he
  · intro stack input H M s t _ hf hw he
    exact effect079_words hf hw he

theorem segment080 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x1035f1 0x103630 cut080 cut081 := by
  have hout : ∀ d : Nat, d ≤ bytes080.length →
      0x1035f1 + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    apply outsideCompression_ne hOutside <;>
      simp only [bytes080, List.length_cons, List.length_nil] at hd <;>
      simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega
  apply Segment.of_block (fun _ _ _ _ ↦ effect080)
    (fun stack input H M ↦ block080 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64 0x35f1) bytes080,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact he.rip.trans (by rfl)
  · intro stack input H M s t _ hf _ he
    exact effect080_agrees he
  · intro stack input H M s t _ hf hw he
    exact effect080_words hf hw he

theorem segment081 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x103630 0x103654 cut081 cut082 := by
  have hout : ∀ d : Nat, d ≤ bytes081.length →
      0x103630 + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    apply outsideCompression_ne hOutside <;>
      simp only [bytes081, List.length_cons, List.length_nil] at hd <;>
      simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega
  apply Segment.of_block (fun _ _ _ _ ↦ effect081)
    (fun stack input H M ↦ block081 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64 0x3630) bytes081,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact he.rip.trans (by rfl)
  · intro stack input H M s t _ hf _ he
    exact effect081_agrees he
  · intro stack input H M s t _ hf hw he
    exact effect081_words hf hw he

theorem segment082 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x103654 0x1036a2 cut082 cut083 := by
  have hout : ∀ d : Nat, d ≤ bytes082.length →
      0x103654 + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    apply outsideCompression_ne hOutside <;>
      simp only [bytes082, List.length_cons, List.length_nil] at hd <;>
      simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega
  apply Segment.of_block (fun _ _ _ _ ↦ effect082)
    (fun stack input H M ↦ block082 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64 0x3654) bytes082,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact he.rip.trans (by rfl)
  · intro stack input H M s t _ hf _ he
    exact effect082_agrees he
  · intro stack input H M s t _ hf hw he
    exact effect082_words hf hw he
theorem segments078_082 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x103579 0x1036a2 cut078 cut083 := by
  have h0 := segment078 boundary hOutside
  have h1 := h0.seq (segment079 boundary hOutside)
  have h2 := h1.seq (segment080 boundary hOutside)
  have h3 := h2.seq (segment081 boundary hOutside)
  have h4 := h3.seq (segment082 boundary hOutside)
  exact h4

end Sha1.Proofs.Compress.Machine
