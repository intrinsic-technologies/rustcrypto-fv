import Sha1.Proofs.Compress.Machine.Run
import Sha1.Proofs.Compress.Rounds.Scalar
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Mov.Generated.RM.Triple
import Sha1.Proofs.Common.Instructions.MovStore.Triple
import X86Proofs.Instructions.Rol.Generated.R.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.Imm32.Triple
import X86Proofs.Instructions.Add.Generated.AccImm32.Triple
import X86Proofs.Instructions.Bswap.Generated.R.Triple
import X86Proofs.Instructions.Lea.Generated.RM.Triple

namespace Sha1.Proofs.Compress.Machine

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Sha1.Spec.Program
open Standards.NIST.SHA1 Sha1.Proofs.Compress.Rounds

attribute [local irreducible] workingAfter scheduleWord messageSchedule

def bytes010 : List UInt8 :=
  [0x89, 0xfa, 0xc1, 0xc2, 0x1e, 0x48, 0x8b, 0x7c, 0x24, 0x40, 0x8b, 0x7f, 0x24, 0xf, 0xcf, 0x41,
    0x89, 0xf8, 0x89, 0x3c, 0x24, 0x89, 0xd7, 0x44, 0x31, 0xd7, 0x21, 0xc7, 0x44, 0x31, 0xd7, 0x44,
    0x1, 0xc1, 0x1, 0xf9, 0x89, 0xf7, 0xc1, 0xc7, 0x5, 0x1, 0xcf, 0x81, 0xc7, 0x99, 0x79, 0x82,
    0x5a]

set_option maxHeartbeats 800000 in
def effect010 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    ((movR32R32Effect 0x1026ff 2 2 7)) (rolR32Effect 0x102701 3 2 30)) (movR64M64Effect 0x102704 7
    (.sib 4 none 0 (.d8 0x40)))) (movR32M32LowEffect 0x102709 7 (.base 7 (.d8 0x24))))
    (bswapR32Effect 0x10270c 2 7)) (movR32R32Effect 0x10270e 3 8 7)) (movM32R32Effect 0x102711 7
    (.sib 4 none 0 .none))) (movR32R32Effect 0x102714 2 7 2)) (xorR32R32Effect 0x102716 3 7 10))
    (andR32R32Effect 0x102719 2 7 0)) (xorR32R32Effect 0x10271b 3 7 10)) (addR32R32Effect 0x10271e 3
    1 8)) (addR32R32Effect 0x102721 2 1 7)) (movR32R32Effect 0x102723 2 7 6)) (rolR32Effect 0x102725
    3 7 5)) (addR32R32Effect 0x102728 2 7 1)) (addR32Imm32Effect 0x10272a 6 7 0x5a827999)

set_option maxHeartbeats 1600000 in
private theorem block010 [Bindings] (boundary : ReturnBoundary)
    (stack input : BitVec 64) (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes010.length → 0x1026ff + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x1026ff ∧ FrameData stack input M s ∧
        Write.AllHold s (cut010 stack input H M))
      (codeRange 0x1026ff bytes010) effect010 := by
  unfold bytes010 at hout ⊢
  sha1_run_begin (mov_r32_r32_effect_step 0x1026ff 0xfa (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x102701 0xc2 0x1e (by decide +kernel)
    (by decide +kernel))
  sha1_run_then (mov_r64_m64_effect_step 0x102704 0x48 (by unfold RexWPrefix; decide +kernel) 7
    (.sib 4 none 0 (.d8 0x40)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_m32_low_effect_step 0x102709 7 (.base 7 (.d8 0x24)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel))
  sha1_run_then (bswap_r32_effect_step 0x10270c 0xcf (by decide +kernel))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x10270e 0x41 0xf8
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m32_r32_low_effect_step 0x102711 7
    (.sib 4 none 0 .none) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_effect_step 0x102714 0xd7 (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102716 0x44 0xd7
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (and_r32_r32_effect_step 0x102719 0xc7 (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x10271b 0x44 0xd7
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x10271e 0x44 0xc1
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_effect_step 0x102721 0xf9 (by decide +kernel))
  sha1_run_then (mov_r32_r32_effect_step 0x102723 0xf7 (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x102725 0xc7 0x5 (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_effect_step 0x102728 0xcf (by decide +kernel))
  sha1_run_then (add_r32_imm32_effect_step 0x10272a 0xc7 0x5a827999 (by decide +kernel)
    (by decide +kernel))
  sha1_run_finish [effect010]

def bytes011 : List UInt8 :=
  [0x48, 0x8b, 0x4c, 0x24, 0x40, 0x44, 0x8b, 0x69, 0x28, 0x41, 0xf, 0xcd, 0x43, 0x8d, 0xc, 0x2a,
    0x4c, 0x89, 0x6c, 0x24, 0x18, 0xc1, 0xc0, 0x1e, 0x41, 0x89, 0xc0, 0x41, 0x31, 0xd0, 0x41, 0x21,
    0xf0, 0x41, 0x31, 0xd0, 0x41, 0x1, 0xc8, 0x89, 0xf9, 0xc1, 0xc1, 0x5, 0x41, 0x1, 0xc8, 0x41,
    0x81, 0xc0, 0x99, 0x79, 0x82, 0x5a]

set_option maxHeartbeats 800000 in
def effect011 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq ((movR64M64Effect
    0x102730 1 (.sib 4 none 0 (.d8 0x40)))) (movR32M32Effect 0x102735 13 (.base 1 (.d8 0x28))))
    (bswapR32Effect 0x102739 3 13)) (leaR32Effect 0x10273c 4 1 (.sib 10 (some 13) 0 .none)))
    (movM64R64Effect 0x102740 13 (.sib 4 none 0 (.d8 0x18)))) (rolR32Effect 0x102745 3 0 30))
    (movR32R32Effect 0x102748 3 8 0)) (xorR32R32Effect 0x10274b 3 8 2)) (andR32R32Effect 0x10274e 3
    8 6)) (xorR32R32Effect 0x102751 3 8 2)) (addR32R32Effect 0x102754 3 8 1)) (movR32R32Effect
    0x102757 2 1 7)) (rolR32Effect 0x102759 3 1 5)) (addR32R32Effect 0x10275c 3 8 1))
    (addR32Imm32Effect 0x10275f 7 8 0x5a827999)

set_option maxHeartbeats 1600000 in
private theorem block011 [Bindings] (boundary : ReturnBoundary)
    (stack input : BitVec 64) (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes011.length → 0x102730 + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x102730 ∧ FrameData stack input M s ∧
        Write.AllHold s (cut011 stack input H M))
      (codeRange 0x102730 bytes011) effect011 := by
  unfold bytes011 at hout ⊢
  sha1_run_begin (mov_r64_m64_effect_step 0x102730 0x48 (by unfold RexWPrefix; decide +kernel) 1
    (.sib 4 none 0 (.d8 0x40)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_m32_effect_step 0x102735 0x44 (by unfold RexNoWPrefix; decide +kernel) 5
    (.base 1 (.d8 0x28)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (bswap_r32_rex_effect_step 0x102739 0x41 (by unfold RexNoWPrefix; decide +kernel)
    0xcd (by decide +kernel))
  sha1_run_then (lea_r32_rex_effect_step 0x10273c 0x43 (by unfold RexNoWPrefix; decide +kernel) 1
    (.sib 10 (some 13) 0 .none) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m64_r64_effect_step 0x102740 0x4c
    (by unfold RexWPrefix; decide +kernel) 5 (.sib 4 none 0 (.d8 0x18)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x102745 0xc0 0x1e (by decide +kernel)
    (by decide +kernel))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x102748 0x41 0xc0
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x10274b 0x41 0xd0
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (and_r32_r32_rex_effect_step 0x10274e 0x41 0xf0
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x102751 0x41 0xd0
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x102754 0x41 0xc8
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_effect_step 0x102757 0xf9 (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x102759 0xc1 0x5 (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x10275c 0x41 0xc8
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_imm32_rex_effect_step 0x10275f 0x41 0xc0 0x5a827999
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_finish [effect011]

def bytes012 : List UInt8 :=
  [0x48, 0x8b, 0x4c, 0x24, 0x40, 0x8b, 0x49, 0x2c, 0xf, 0xc9, 0x48, 0x89, 0x4c, 0x24, 0x50, 0x1,
    0xd1, 0xc1, 0xc6, 0x1e, 0x89, 0xf2, 0x31, 0xc2, 0x21, 0xfa, 0x31, 0xc2, 0x1, 0xca, 0x44, 0x89,
    0xc1, 0xc1, 0xc1, 0x5, 0xc1, 0xc7, 0x1e, 0x1, 0xd1, 0x81, 0xc1, 0x99, 0x79, 0x82, 0x5a]

set_option maxHeartbeats 800000 in
def effect012 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    ((movR64M64Effect 0x102766 1 (.sib 4 none 0 (.d8 0x40)))) (movR32M32LowEffect 0x10276b 1 (.base
    1 (.d8 0x2c)))) (bswapR32Effect 0x10276e 2 1)) (movM64R64Effect 0x102770 1 (.sib 4 none 0 (.d8
    0x50)))) (addR32R32Effect 0x102775 2 1 2)) (rolR32Effect 0x102777 3 6 30)) (movR32R32Effect
    0x10277a 2 2 6)) (xorR32R32Effect 0x10277c 2 2 0)) (andR32R32Effect 0x10277e 2 2 7))
    (xorR32R32Effect 0x102780 2 2 0)) (addR32R32Effect 0x102782 2 2 1)) (movR32R32Effect 0x102784 3
    1 8)) (rolR32Effect 0x102787 3 1 5)) (rolR32Effect 0x10278a 3 7 30)) (addR32R32Effect 0x10278d 2
    1 2)) (addR32Imm32Effect 0x10278f 6 1 0x5a827999)

set_option maxHeartbeats 1600000 in
private theorem block012 [Bindings] (boundary : ReturnBoundary)
    (stack input : BitVec 64) (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes012.length → 0x102766 + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x102766 ∧ FrameData stack input M s ∧
        Write.AllHold s (cut012 stack input H M))
      (codeRange 0x102766 bytes012) effect012 := by
  unfold bytes012 at hout ⊢
  sha1_run_begin (mov_r64_m64_effect_step 0x102766 0x48 (by unfold RexWPrefix; decide +kernel) 1
    (.sib 4 none 0 (.d8 0x40)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_m32_low_effect_step 0x10276b 1 (.base 1 (.d8 0x2c)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel))
  sha1_run_then (bswap_r32_effect_step 0x10276e 0xc9 (by decide +kernel))
  sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m64_r64_effect_step 0x102770 0x48
    (by unfold RexWPrefix; decide +kernel) 1 (.sib 4 none 0 (.d8 0x50)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_effect_step 0x102775 0xd1 (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x102777 0xc6 0x1e (by decide +kernel)
    (by decide +kernel))
  sha1_run_then (mov_r32_r32_effect_step 0x10277a 0xf2 (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x10277c 0xc2 (by decide +kernel))
  sha1_run_then (and_r32_r32_effect_step 0x10277e 0xfa (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x102780 0xc2 (by decide +kernel))
  sha1_run_then (add_r32_r32_effect_step 0x102782 0xca (by decide +kernel))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x102784 0x44 0xc1
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x102787 0xc1 0x5 (by decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x10278a 0xc7 0x1e (by decide +kernel)
    (by decide +kernel))
  sha1_run_then (add_r32_r32_effect_step 0x10278d 0xd1 (by decide +kernel))
  sha1_run_then (add_r32_imm32_effect_step 0x10278f 0xc1 0x5a827999 (by decide +kernel)
    (by decide +kernel))
  sha1_run_finish [effect012]

def bytes013 : List UInt8 :=
  [0x89, 0xfa, 0x31, 0xf2, 0x44, 0x21, 0xc2, 0x4c, 0x8b, 0x54, 0x24, 0x40, 0x45, 0x8b, 0x4a, 0x30,
    0x41, 0xf, 0xc9, 0x4c, 0x89, 0x4c, 0x24, 0x60, 0x31, 0xf2, 0x44, 0x1, 0xc8, 0x1, 0xd0, 0x89,
    0xca, 0xc1, 0xc2, 0x5, 0x1, 0xc2, 0x81, 0xc2, 0x99, 0x79, 0x82, 0x5a]

set_option maxHeartbeats 800000 in
def effect013 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq ((movR32R32Effect 0x102795 2 2 7))
    (xorR32R32Effect 0x102797 2 2 6)) (andR32R32Effect 0x102799 3 2 8)) (movR64M64Effect 0x10279c 10
    (.sib 4 none 0 (.d8 0x40)))) (movR32M32Effect 0x1027a1 9 (.base 10 (.d8 0x30)))) (bswapR32Effect
    0x1027a5 3 9)) (movM64R64Effect 0x1027a8 9 (.sib 4 none 0 (.d8 0x60)))) (xorR32R32Effect
    0x1027ad 2 2 6)) (addR32R32Effect 0x1027af 3 0 9)) (addR32R32Effect 0x1027b2 2 0 2))
    (movR32R32Effect 0x1027b4 2 2 1)) (rolR32Effect 0x1027b6 3 2 5)) (addR32R32Effect 0x1027b9 2 2
    0)) (addR32Imm32Effect 0x1027bb 6 2 0x5a827999)

set_option maxHeartbeats 1600000 in
private theorem block013 [Bindings] (boundary : ReturnBoundary)
    (stack input : BitVec 64) (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes013.length → 0x102795 + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x102795 ∧ FrameData stack input M s ∧
        Write.AllHold s (cut013 stack input H M))
      (codeRange 0x102795 bytes013) effect013 := by
  unfold bytes013 at hout ⊢
  sha1_run_begin (mov_r32_r32_effect_step 0x102795 0xfa (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x102797 0xf2 (by decide +kernel))
  sha1_run_then (and_r32_r32_rex_effect_step 0x102799 0x44 0xc2
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r64_m64_effect_step 0x10279c 0x4c (by unfold RexWPrefix; decide +kernel) 2
    (.sib 4 none 0 (.d8 0x40)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_m32_effect_step 0x1027a1 0x45 (by unfold RexNoWPrefix; decide +kernel) 1
    (.base 10 (.d8 0x30)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (bswap_r32_rex_effect_step 0x1027a5 0x41 (by unfold RexNoWPrefix; decide +kernel)
    0xc9 (by decide +kernel))
  sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m64_r64_effect_step 0x1027a8 0x4c
    (by unfold RexWPrefix; decide +kernel) 1 (.sib 4 none 0 (.d8 0x60)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_effect_step 0x1027ad 0xf2 (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x1027af 0x44 0xc8
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_effect_step 0x1027b2 0xd0 (by decide +kernel))
  sha1_run_then (mov_r32_r32_effect_step 0x1027b4 0xca (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x1027b6 0xc2 0x5 (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_effect_step 0x1027b9 0xc2 (by decide +kernel))
  sha1_run_then (add_r32_imm32_effect_step 0x1027bb 0xc2 0x5a827999 (by decide +kernel)
    (by decide +kernel))
  sha1_run_finish [effect013]

def bytes014 : List UInt8 :=
  [0x44, 0x89, 0xc0, 0x4c, 0x8b, 0x44, 0x24, 0x40, 0x41, 0x8b, 0x68, 0x34, 0xf, 0xcd, 0xc1, 0xc0,
    0x1e, 0x41, 0x89, 0xc0, 0x41, 0x31, 0xf8, 0x41, 0x21, 0xc8, 0x41, 0x31, 0xf8, 0x1, 0xee, 0x48,
    0x89, 0x6c, 0x24, 0x10, 0x44, 0x1, 0xc6, 0x41, 0x89, 0xd0, 0x41, 0xc1, 0xc0, 0x5, 0x44, 0x1,
    0xc6, 0x81, 0xc6, 0x99, 0x79, 0x82, 0x5a]

set_option maxHeartbeats 800000 in
def effect014 : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq
    ((movR32R32Effect 0x1027c1 3 0 8)) (movR64M64Effect 0x1027c4 8 (.sib 4 none 0 (.d8 0x40))))
    (movR32M32Effect 0x1027c9 5 (.base 8 (.d8 0x34)))) (bswapR32Effect 0x1027cd 2 5)) (rolR32Effect
    0x1027cf 3 0 30)) (movR32R32Effect 0x1027d2 3 8 0)) (xorR32R32Effect 0x1027d5 3 8 7))
    (andR32R32Effect 0x1027d8 3 8 1)) (xorR32R32Effect 0x1027db 3 8 7)) (addR32R32Effect 0x1027de 2
    6 5)) (movM64R64Effect 0x1027e0 5 (.sib 4 none 0 (.d8 0x10)))) (addR32R32Effect 0x1027e5 3 6 8))
    (movR32R32Effect 0x1027e8 3 8 2)) (rolR32Effect 0x1027eb 4 8 5)) (addR32R32Effect 0x1027ef 3 6
    8)) (addR32Imm32Effect 0x1027f2 6 6 0x5a827999)

set_option maxHeartbeats 1600000 in
private theorem block014 [Bindings] (boundary : ReturnBoundary)
    (stack input : BitVec 64) (H : Vector (BitVec 32) 5) (M : Vector (BitVec 32) 16)
    (hout : ∀ d : Nat, d ≤ bytes014.length → 0x1027c1 + BitVec.ofNat 64 d ≠ boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x1027c1 ∧ FrameData stack input M s ∧
        Write.AllHold s (cut014 stack input H M))
      (codeRange 0x1027c1 bytes014) effect014 := by
  unfold bytes014 at hout ⊢
  sha1_run_begin (mov_r32_r32_rex_effect_step 0x1027c1 0x44 0xc0
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r64_m64_effect_step 0x1027c4 0x4c (by unfold RexWPrefix; decide +kernel) 0
    (.sib 4 none 0 (.d8 0x40)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_m32_effect_step 0x1027c9 0x41 (by unfold RexNoWPrefix; decide +kernel) 5
    (.base 8 (.d8 0x34)) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (bswap_r32_effect_step 0x1027cd 0xcd (by decide +kernel))
  sha1_run_then (rol_r32_imm8_effect_step 0x1027cf 0xc0 0x1e (by decide +kernel)
    (by decide +kernel))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x1027d2 0x41 0xc0
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x1027d5 0x41 0xf8
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (and_r32_r32_rex_effect_step 0x1027d8 0x41 0xc8
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (xor_r32_r32_rex_effect_step 0x1027db 0x41 0xf8
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_effect_step 0x1027de 0xee (by decide +kernel))
  sha1_run_then (Sha1.Proofs.Common.Instructions.MovStore.mov_m64_r64_effect_step 0x1027e0 0x48
    (by unfold RexWPrefix; decide +kernel) 5 (.sib 4 none 0 (.d8 0x10)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x1027e5 0x44 0xc6
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (mov_r32_r32_rex_effect_step 0x1027e8 0x41 0xd0
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (rol_r32_imm8_rex_effect_step 0x1027eb 0x41 0xc0 0x5
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_r32_rex_effect_step 0x1027ef 0x44 0xc6
    (by unfold RexNoWPrefix; decide +kernel) (by decide +kernel))
  sha1_run_then (add_r32_imm32_effect_step 0x1027f2 0xc6 0x5a827999 (by decide +kernel)
    (by decide +kernel))
  sha1_run_finish [effect014]

set_option maxHeartbeats 800000 in
private theorem effect010_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s) (he : (effect010 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  sha1_norm at hs
  have hfoot : ∀ c ∈ (effect010 s).components, c ∈ [.mem (stack + 0) 4] ++ scratchComponents stack
    := by
    unfold effect010
    iterate 16 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [addR32Imm32Effect_components, addR32R32Effect_components, andR32R32Effect_components,
        bswapR32Effect_components, movM32R32Effect_components, movR32M32LowEffect_components,
        movR32R32Effect_components, movR64M64Effect_components, rolR32Effect_components,
        xorR32R32Effect_components, scratchComponents,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_imp,
        forall_and, forall_eq, or_true, true_or]
    all_goals sha1_norm [hs]
  apply (he.agrees.mono hfoot).widen
  · intro c hc hn
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | hc
    · cases hn
    · exact hc
  · intro a c hc hCov
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | hc
    · exact scratchComponents_stack (Or.inl (by decide +kernel)) hCov
    · exact ⟨c, hc, hCov⟩

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1600000 in
private theorem effect010_words {stack input : BitVec 64}
    {H : Vector (BitVec 32) 5} {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s)
    (hw : Write.AllHold s (cut010 stack input H M))
    (he : (effect010 s).Holds s t) :
    Write.AllHold t (cut011 stack input H M) := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have hin9 : (Operand.mem (input + 36) : Operand 32).read s =
      bswapSpec (scheduleWord M 9) := by
    rw [scheduleWord_initial M 9 (by decide +kernel)]
    exact hf.words 9
  sha1_norm at hin9
  have hfull : ∀ w ∈ (effect010 s).writes, w.Full := by
    apply Effect.Local.full
    unfold effect010
    repeat' first | (solve | x86_local) | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  simp only [cut010, Write.AllHold] at hw
  obtain ⟨h0, h1, h6, h7, h10, h12, h14, h15, hM4, hM8, hM32, hM40, hM56, hM64, hM88, hM116, hM120,
    hM124, hM144, hM152⟩ := hw
  sha1_norm at hs h0 h1 h6 h7 h10 h12 h14 h15 hM4 hM8 hM32 hM40 hM56 hM64 hM88 hM116 hM120 hM124
  sha1_norm at hM144 hM152
  simp only [cut011, Write.AllHold, ← ho.read_reg, ← ho.read_mem]
  sha1_norm [effect010, hs, hin9, h0, h1, h6, h7, h10, h12, h14, h15, hM4, hM8, hM32, hM40, hM56,
    hM64, hM88, hM116, hM120, hM124, hM144, hM152,
    movR32M32LowEffect, leaSpec, bswap32_bswap32,
    read32_memStore64_low, extractLsb'_zero_eq_setWidth,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
    BitVec.shiftLeft_zero, BitVec.add_zero]
  have hWork := workingAfter_step_a_values M H 5 (by decide +kernel)
  simp only [Nat.reduceAdd, sha1_f_choice (t := ⟨9, by decide⟩) (by decide),
    sha1_K_choice (t := ⟨9, by decide⟩) (by decide)] at hWork
  rw [sha1Ch_eq, BitVec.and_comm, BitVec.xor_comm] at hWork
  change (workingAfter M H 10).a = (workingAfter M H 9).a.rotateLeft 5 +
    (((workingAfter M H 7).a.rotateLeft 30 ^^^ (workingAfter M H 6).a.rotateLeft 30) &&&
      (workingAfter M H 8).a ^^^ (workingAfter M H 6).a.rotateLeft 30) +
    (workingAfter M H 5).a.rotateLeft 30 + (0x5a827999#32) +
    scheduleWord M 9 at hWork
  rw [hWork]
  ac_rfl

theorem segment010 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x1026ff 0x102730 cut010 cut011 := by
  have hout : ∀ d : Nat, d ≤ bytes010.length →
      0x1026ff + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    apply outsideCompression_ne hOutside <;>
      simp only [bytes010, List.length_cons, List.length_nil] at hd <;>
      simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega
  apply Segment.of_block (fun _ _ _ _ ↦ effect010)
    (fun stack input H M ↦ block010 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64 0x26ff) bytes010,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact he.rip.trans (by rfl)
  · intro stack input H M s t _ hf _ he
    exact effect010_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect010_words hf hw he

set_option maxHeartbeats 800000 in
private theorem effect011_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s) (he : (effect011 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  sha1_norm at hs
  have hfoot : ∀ c ∈ (effect011 s).components, c ∈ [.mem (stack + 24) 8] ++ scratchComponents stack
    := by
    unfold effect011
    iterate 14 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [addR32Imm32Effect_components, addR32R32Effect_components, andR32R32Effect_components,
        bswapR32Effect_components, leaR32Effect_components, movM64R64Effect_components,
        movR32M32Effect_components, movR32R32Effect_components, movR64M64Effect_components,
        rolR32Effect_components, xorR32R32Effect_components, scratchComponents,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_imp,
        forall_and, forall_eq, or_true, true_or]
    all_goals sha1_norm [hs]
  apply (he.agrees.mono hfoot).widen
  · intro c hc hn
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | hc
    · cases hn
    · exact hc
  · intro a c hc hCov
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | hc
    · exact scratchComponents_stack (Or.inl (by decide +kernel)) hCov
    · exact ⟨c, hc, hCov⟩

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1600000 in
private theorem effect011_words {stack input : BitVec 64}
    {H : Vector (BitVec 32) 5} {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s)
    (hw : Write.AllHold s (cut011 stack input H M))
    (he : (effect011 s).Holds s t) :
    Write.AllHold t (cut012 stack input H M) := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have hin10 : (Operand.mem (input + 40) : Operand 32).read s =
      bswapSpec (scheduleWord M 10) := by
    rw [scheduleWord_initial M 10 (by decide +kernel)]
    exact hf.words 10
  sha1_norm at hin10
  have hfull : ∀ w ∈ (effect011 s).writes, w.Full := by
    apply Effect.Local.full
    unfold effect011
    repeat' first | (solve | x86_local) | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  simp only [cut011, Write.AllHold] at hw
  obtain ⟨h0, h2, h6, h7, h10, h12, h14, h15, hM0, hM4, hM8, hM32, hM40, hM56, hM64, hM88, hM116,
    hM120, hM124, hM144, hM152⟩ := hw
  sha1_norm at hs h0 h2 h6 h7 h10 h12 h14 h15 hM0 hM4 hM8 hM32 hM40 hM56 hM64 hM88 hM116 hM120
  sha1_norm at hM124 hM144 hM152
  simp only [BitVec.add_zero] at hM0
  simp only [cut012, Write.AllHold, ← ho.read_reg, ← ho.read_mem]
  sha1_norm [effect011, hs, hin10, h0, h2, h6, h7, h10, h12, h14, h15, hM0, hM4, hM8, hM32, hM40,
    hM56, hM64, hM88, hM116, hM120, hM124, hM144, hM152,
    movR32M32LowEffect, leaSpec, bswap32_bswap32,
    read32_memStore64_low, extractLsb'_zero_eq_setWidth,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
    BitVec.shiftLeft_zero, BitVec.add_zero]
  have hWork := workingAfter_step_a_values M H 6 (by decide +kernel)
  simp only [Nat.reduceAdd, sha1_f_choice (t := ⟨10, by decide⟩) (by decide),
    sha1_K_choice (t := ⟨10, by decide⟩) (by decide)] at hWork
  rw [sha1Ch_eq, BitVec.and_comm, BitVec.xor_comm] at hWork
  change (workingAfter M H 11).a = (workingAfter M H 10).a.rotateLeft 5 +
    (((workingAfter M H 8).a.rotateLeft 30 ^^^ (workingAfter M H 7).a.rotateLeft 30) &&&
      (workingAfter M H 9).a ^^^ (workingAfter M H 7).a.rotateLeft 30) +
    (workingAfter M H 6).a.rotateLeft 30 + (0x5a827999#32) +
    scheduleWord M 10 at hWork
  rw [hWork]
  ac_rfl

theorem segment011 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x102730 0x102766 cut011 cut012 := by
  have hout : ∀ d : Nat, d ≤ bytes011.length →
      0x102730 + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    apply outsideCompression_ne hOutside <;>
      simp only [bytes011, List.length_cons, List.length_nil] at hd <;>
      simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega
  apply Segment.of_block (fun _ _ _ _ ↦ effect011)
    (fun stack input H M ↦ block011 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64 0x2730) bytes011,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact he.rip.trans (by rfl)
  · intro stack input H M s t _ hf _ he
    exact effect011_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect011_words hf hw he

set_option maxHeartbeats 800000 in
private theorem effect012_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s) (he : (effect012 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  sha1_norm at hs
  have hfoot : ∀ c ∈ (effect012 s).components, c ∈ [.mem (stack + 80) 8] ++ scratchComponents stack
    := by
    unfold effect012
    iterate 15 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [addR32Imm32Effect_components, addR32R32Effect_components, andR32R32Effect_components,
        bswapR32Effect_components, movM64R64Effect_components, movR32M32LowEffect_components,
        movR32R32Effect_components, movR64M64Effect_components, rolR32Effect_components,
        xorR32R32Effect_components, scratchComponents,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_imp,
        forall_and, forall_eq, or_true, true_or]
    all_goals sha1_norm [hs]
  apply (he.agrees.mono hfoot).widen
  · intro c hc hn
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | hc
    · cases hn
    · exact hc
  · intro a c hc hCov
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | hc
    · exact scratchComponents_stack (Or.inl (by decide +kernel)) hCov
    · exact ⟨c, hc, hCov⟩

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1600000 in
private theorem effect012_words {stack input : BitVec 64}
    {H : Vector (BitVec 32) 5} {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s)
    (hw : Write.AllHold s (cut012 stack input H M))
    (he : (effect012 s).Holds s t) :
    Write.AllHold t (cut013 stack input H M) := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have hin11 : (Operand.mem (input + 44) : Operand 32).read s =
      bswapSpec (scheduleWord M 11) := by
    rw [scheduleWord_initial M 11 (by decide +kernel)]
    exact hf.words 11
  sha1_norm at hin11
  have hfull : ∀ w ∈ (effect012 s).writes, w.Full := by
    apply Effect.Local.full
    unfold effect012
    repeat' first | (solve | x86_local) | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  simp only [cut012, Write.AllHold] at hw
  obtain ⟨h0, h2, h6, h7, h8, h12, h13, h14, h15, hM0, hM4, hM8, hM24, hM32, hM40, hM56, hM64, hM88,
    hM116, hM120, hM124, hM144, hM152⟩ := hw
  sha1_norm at hs h0 h2 h6 h7 h8 h12 h13 h14 h15 hM0 hM4 hM8 hM24 hM32 hM40 hM56 hM64 hM88 hM116
  sha1_norm at hM120 hM124 hM144 hM152
  simp only [BitVec.add_zero] at hM0
  simp only [cut013, Write.AllHold, ← ho.read_reg, ← ho.read_mem]
  sha1_norm [effect012, hs, hin11, h0, h2, h6, h7, h8, h12, h13, h14, h15, hM0, hM4, hM8, hM24,
    hM32, hM40, hM56, hM64, hM88, hM116, hM120, hM124, hM144, hM152,
    movR32M32LowEffect, leaSpec, bswap32_bswap32,
    read32_memStore64_low, extractLsb'_zero_eq_setWidth,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
    BitVec.shiftLeft_zero, BitVec.add_zero]
  have hWork := workingAfter_step_a_values M H 7 (by decide +kernel)
  simp only [Nat.reduceAdd, sha1_f_choice (t := ⟨11, by decide⟩) (by decide),
    sha1_K_choice (t := ⟨11, by decide⟩) (by decide)] at hWork
  rw [sha1Ch_eq, BitVec.and_comm, BitVec.xor_comm] at hWork
  change (workingAfter M H 12).a = (workingAfter M H 11).a.rotateLeft 5 +
    (((workingAfter M H 9).a.rotateLeft 30 ^^^ (workingAfter M H 8).a.rotateLeft 30) &&&
      (workingAfter M H 10).a ^^^ (workingAfter M H 8).a.rotateLeft 30) +
    (workingAfter M H 7).a.rotateLeft 30 + (0x5a827999#32) +
    scheduleWord M 11 at hWork
  rw [hWork]
  ac_rfl

theorem segment012 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x102766 0x102795 cut012 cut013 := by
  have hout : ∀ d : Nat, d ≤ bytes012.length →
      0x102766 + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    apply outsideCompression_ne hOutside <;>
      simp only [bytes012, List.length_cons, List.length_nil] at hd <;>
      simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega
  apply Segment.of_block (fun _ _ _ _ ↦ effect012)
    (fun stack input H M ↦ block012 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64 0x2766) bytes012,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact he.rip.trans (by rfl)
  · intro stack input H M s t _ hf _ he
    exact effect012_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect012_words hf hw he

set_option maxHeartbeats 800000 in
private theorem effect013_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s) (he : (effect013 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  sha1_norm at hs
  have hfoot : ∀ c ∈ (effect013 s).components, c ∈ [.mem (stack + 96) 8] ++ scratchComponents stack
    := by
    unfold effect013
    iterate 13 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [addR32Imm32Effect_components, addR32R32Effect_components, andR32R32Effect_components,
        bswapR32Effect_components, movM64R64Effect_components, movR32M32Effect_components,
        movR32R32Effect_components, movR64M64Effect_components, rolR32Effect_components,
        xorR32R32Effect_components, scratchComponents,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_imp,
        forall_and, forall_eq, or_true, true_or]
    all_goals sha1_norm [hs]
  apply (he.agrees.mono hfoot).widen
  · intro c hc hn
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | hc
    · cases hn
    · exact hc
  · intro a c hc hCov
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | hc
    · exact scratchComponents_stack (Or.inl (by decide +kernel)) hCov
    · exact ⟨c, hc, hCov⟩

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1600000 in
private theorem effect013_words {stack input : BitVec 64}
    {H : Vector (BitVec 32) 5} {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s)
    (hw : Write.AllHold s (cut013 stack input H M))
    (he : (effect013 s).Holds s t) :
    Write.AllHold t (cut014 stack input H M) := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have hin12 : (Operand.mem (input + 48) : Operand 32).read s =
      bswapSpec (scheduleWord M 12) := by
    rw [scheduleWord_initial M 12 (by decide +kernel)]
    exact hf.words 12
  sha1_norm at hin12
  have hfull : ∀ w ∈ (effect013 s).writes, w.Full := by
    apply Effect.Local.full
    unfold effect013
    repeat' first | (solve | x86_local) | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  simp only [cut013, Write.AllHold] at hw
  obtain ⟨h0, h1, h6, h7, h8, h12, h13, h14, h15, hM0, hM4, hM8, hM24, hM32, hM40, hM56, hM64, hM80,
    hM88, hM116, hM120, hM124, hM144, hM152⟩ := hw
  sha1_norm at hs h0 h1 h6 h7 h8 h12 h13 h14 h15 hM0 hM4 hM8 hM24 hM32 hM40 hM56 hM64 hM80 hM88
  sha1_norm at hM116 hM120 hM124 hM144 hM152
  simp only [BitVec.add_zero] at hM0
  simp only [cut014, Write.AllHold, ← ho.read_reg, ← ho.read_mem]
  sha1_norm [effect013, hs, hin12, h0, h1, h6, h7, h8, h12, h13, h14, h15, hM0, hM4, hM8, hM24,
    hM32, hM40, hM56, hM64, hM80, hM88, hM116, hM120, hM124, hM144, hM152,
    movR32M32LowEffect, leaSpec, bswap32_bswap32,
    read32_memStore64_low, extractLsb'_zero_eq_setWidth,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
    BitVec.shiftLeft_zero, BitVec.add_zero]
  have hWork := workingAfter_step_a_values M H 8 (by decide +kernel)
  simp only [Nat.reduceAdd, sha1_f_choice (t := ⟨12, by decide⟩) (by decide),
    sha1_K_choice (t := ⟨12, by decide⟩) (by decide)] at hWork
  rw [sha1Ch_eq, BitVec.and_comm, BitVec.xor_comm] at hWork
  change (workingAfter M H 13).a = (workingAfter M H 12).a.rotateLeft 5 +
    (((workingAfter M H 10).a.rotateLeft 30 ^^^ (workingAfter M H 9).a.rotateLeft 30) &&&
      (workingAfter M H 11).a ^^^ (workingAfter M H 9).a.rotateLeft 30) +
    (workingAfter M H 8).a.rotateLeft 30 + (0x5a827999#32) +
    scheduleWord M 12 at hWork
  rw [hWork]
  ac_rfl

theorem segment013 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x102795 0x1027c1 cut013 cut014 := by
  have hout : ∀ d : Nat, d ≤ bytes013.length →
      0x102795 + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    apply outsideCompression_ne hOutside <;>
      simp only [bytes013, List.length_cons, List.length_nil] at hd <;>
      simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega
  apply Segment.of_block (fun _ _ _ _ ↦ effect013)
    (fun stack input H M ↦ block013 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64 0x2795) bytes013,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact he.rip.trans (by rfl)
  · intro stack input H M s t _ hf _ he
    exact effect013_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect013_words hf hw he

set_option maxHeartbeats 800000 in
private theorem effect014_agrees {stack input : BitVec 64}
    {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s) (he : (effect014 s).Holds s t) :
    AgreesExcept (scratchComponents stack) s t := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  sha1_norm at hs
  have hfoot : ∀ c ∈ (effect014 s).components, c ∈ [.mem (stack + 16) 8] ++ scratchComponents stack
    := by
    unfold effect014
    iterate 15 apply components_seq_of
    all_goals simp (config := {decide := true, implicitDefEqProofs := false}) only
      [addR32Imm32Effect_components, addR32R32Effect_components, andR32R32Effect_components,
        bswapR32Effect_components, movM64R64Effect_components, movR32M32Effect_components,
        movR32R32Effect_components, movR64M64Effect_components, rolR32Effect_components,
        xorR32R32Effect_components, scratchComponents,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_imp,
        forall_and, forall_eq, or_true, true_or]
    all_goals sha1_norm [hs]
  apply (he.agrees.mono hfoot).widen
  · intro c hc hn
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | hc
    · cases hn
    · exact hc
  · intro a c hc hCov
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | hc
    · exact scratchComponents_stack (Or.inl (by decide +kernel)) hCov
    · exact ⟨c, hc, hCov⟩

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1600000 in
private theorem effect014_words {stack input : BitVec 64}
    {H : Vector (BitVec 32) 5} {M : Vector (BitVec 32) 16} {s t : RamState}
    (hf : FrameData stack input M s)
    (hw : Write.AllHold s (cut014 stack input H M))
    (he : (effect014 s).Holds s t) :
    Write.AllHold t (cut015 stack input H M) := by
  have hs : (Operand.reg 4 : Operand 64).read s = stack := hf.stackPointer
  have hin13 : (Operand.mem (input + 52) : Operand 32).read s =
      bswapSpec (scheduleWord M 13) := by
    rw [scheduleWord_initial M 13 (by decide +kernel)]
    exact hf.words 13
  sha1_norm at hin13
  have hfull : ∀ w ∈ (effect014 s).writes, w.Full := by
    apply Effect.Local.full
    unfold effect014
    repeat' first | (solve | x86_local) | apply Effect.Local.seq
  have ho := he.obsAfter hfull true
  simp only [cut014, Write.AllHold] at hw
  obtain ⟨h1, h2, h6, h7, h8, h12, h13, h14, h15, hM0, hM4, hM8, hM24, hM32, hM40, hM56, hM64, hM80,
    hM88, hM96, hM116, hM120, hM124, hM144, hM152⟩ := hw
  sha1_norm at hs h1 h2 h6 h7 h8 h12 h13 h14 h15 hM0 hM4 hM8 hM24 hM32 hM40 hM56 hM64 hM80 hM88
  sha1_norm at hM96 hM116 hM120 hM124 hM144 hM152
  simp only [BitVec.add_zero] at hM0
  simp only [cut015, Write.AllHold, ← ho.read_reg, ← ho.read_mem]
  sha1_norm [effect014, hs, hin13, h1, h2, h6, h7, h8, h12, h13, h14, h15, hM0, hM4, hM8, hM24,
    hM32, hM40, hM56, hM64, hM80, hM88, hM96, hM116, hM120, hM124, hM144, hM152,
    movR32M32LowEffect, leaSpec, bswap32_bswap32,
    read32_memStore64_low, extractLsb'_zero_eq_setWidth,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.setWidth_add,
    BitVec.shiftLeft_zero, BitVec.add_zero]
  have hWork := workingAfter_step_a_values M H 9 (by decide +kernel)
  simp only [Nat.reduceAdd, sha1_f_choice (t := ⟨13, by decide⟩) (by decide),
    sha1_K_choice (t := ⟨13, by decide⟩) (by decide)] at hWork
  rw [sha1Ch_eq, BitVec.and_comm, BitVec.xor_comm] at hWork
  change (workingAfter M H 14).a = (workingAfter M H 13).a.rotateLeft 5 +
    (((workingAfter M H 11).a.rotateLeft 30 ^^^ (workingAfter M H 10).a.rotateLeft 30) &&&
      (workingAfter M H 12).a ^^^ (workingAfter M H 10).a.rotateLeft 30) +
    (workingAfter M H 9).a.rotateLeft 30 + (0x5a827999#32) +
    scheduleWord M 13 at hWork
  rw [hWork]
  ac_rfl

theorem segment014 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x1027c1 0x1027f8 cut014 cut015 := by
  have hout : ∀ d : Nat, d ≤ bytes014.length →
      0x1027c1 + BitVec.ofNat 64 d ≠ boundary.rip := by
    intro d hd
    apply outsideCompression_ne hOutside <;>
      simp only [bytes014, List.length_cons, List.length_nil] at hd <;>
      simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega
  apply Segment.of_block (fun _ _ _ _ ↦ effect014)
    (fun stack input H M ↦ block014 boundary stack input H M hout)
  · change ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64 0x27c1) bytes014,
      x ∈ Extracted.programImage
    exact program_text_subset _ (by decide +kernel) (by decide +kernel)
  · intro stack input H M s t _ _ _ he
    exact he.rip.trans (by rfl)
  · intro stack input H M s t _ hf _ he
    exact effect014_agrees hf he
  · intro stack input H M s t _ hf hw he
    exact effect014_words hf hw he

theorem segments010_014 [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideCompression boundary.rip) :
    Segment boundary 0x1026ff 0x1027f8 cut010 cut015 := by
  have h0 := segment010 boundary hOutside
  have h1 := h0.seq (segment011 boundary hOutside)
  have h2 := h1.seq (segment012 boundary hOutside)
  have h3 := h2.seq (segment013 boundary hOutside)
  have h4 := h3.seq (segment014 boundary hOutside)
  exact h4

end Sha1.Proofs.Compress.Machine
