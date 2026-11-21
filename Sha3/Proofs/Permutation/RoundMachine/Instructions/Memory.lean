import X86Proofs.Instructions.MovLoad.Triple
import Sha3.Proofs.Permutation.LoadStore.Memory
import Sha3.Proofs.X86.Instructions.XorLoad.Triple
import Sha3.Proofs.Permutation.LoadStore.Rmw
import Sha3.Proofs.Permutation.Layout

namespace Sha3.Proofs.Permutation.RoundMachine

open X86 X86.Machine X86.UserProcess X86Proofs

theorem step_1000f0 [Bindings] (pc : BitVec 64) :
    StepEffect (StorePreReadable pc
      (storeAddrAt pc (.sib 4 none 0 (.d8 0x8)) 5) 8)
      (codeRange pc [0x4c, 0x89, 0x74, 0x24, 0x08])
      (movM64R64Effect pc 14 (.sib 4 none 0 (.d8 0x8))) := by
  exact mov_m64_r64_effect_step_of_readable pc 0x4c (by unfold RexWPrefix; decide +kernel)
    6 (.sib 4 none 0 (.d8 0x8))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_1000f5 [Bindings] (pc : BitVec 64) :
    StepEffect (StorePreReadable pc
      (storeAddrAt pc (.sib 4 none 0 (.d8 0x40)) 5) 8)
      (codeRange pc [0x4c, 0x89, 0x6c, 0x24, 0x40])
      (movM64R64Effect pc 13 (.sib 4 none 0 (.d8 0x40))) := by
  exact mov_m64_r64_effect_step_of_readable pc 0x4c (by unfold RexWPrefix; decide +kernel)
    5 (.sib 4 none 0 (.d8 0x40))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_1000fa [Bindings] (pc : BitVec 64) :
    StepEffect (StorePreReadable pc
      (storeAddrAt pc (.sib 4 none 0 (.d32 0xd0)) 8) 8)
      (codeRange pc [0x48, 0x89, 0x94, 0x24, 0xd0, 0x00, 0x00, 0x00])
      (movM64R64Effect pc 2 (.sib 4 none 0 (.d32 0xd0))) := by
  exact mov_m64_r64_effect_step_of_readable pc 0x48 (by unfold RexWPrefix; decide +kernel)
    2 (.sib 4 none 0 (.d32 0xd0))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_100102 [Bindings] (pc : BitVec 64) :
    StepEffect (LoadPre pc
      (fun s ↦ ((.sib 4 none 0 (.d8 0x50)) : AddrMode).addr s (pc + 5)) 8)
      (codeRange pc [0x48, 0x8b, 0x54, 0x24, 0x50])
      (movR64M64Effect pc 2 (.sib 4 none 0 (.d8 0x50))) := by
  exact mov_r64_m64_effect_step pc 0x48 (by unfold RexWPrefix; decide +kernel)
    2 (.sib 4 none 0 (.d8 0x50))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_100107 [Bindings] (pc : BitVec 64) :
    StepEffect (LoadPre pc
      (fun s ↦ ((.sib 4 none 0 (.d8 0x20)) : AddrMode).addr s (pc + 5)) 8)
      (codeRange pc [0x48, 0x33, 0x54, 0x24, 0x20])
      (xorR64M64Effect pc 2 (.sib 4 none 0 (.d8 0x20))) := by
  exact xor_r64_m64_effect_step pc 0x48 (by unfold RexWPrefix; decide +kernel)
    2 (.sib 4 none 0 (.d8 0x20))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_100115 [Bindings] (pc : BitVec 64) :
    StepEffect (LoadPre pc
      (fun s ↦ ((.sib 4 none 0 (.d32 0x80)) : AddrMode).addr s (pc + 8)) 8)
      (codeRange pc [0x48, 0x8b, 0x94, 0x24, 0x80, 0x00, 0x00, 0x00])
      (movR64M64Effect pc 2 (.sib 4 none 0 (.d32 0x80))) := by
  exact mov_r64_m64_effect_step pc 0x48 (by unfold RexWPrefix; decide +kernel)
    2 (.sib 4 none 0 (.d32 0x80))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_100123 [Bindings] (pc : BitVec 64) :
    StepEffect (StorePreReadable pc
      (storeAddrAt pc (.sib 4 none 0 (.d8 0x48)) 5) 8)
      (codeRange pc [0x4c, 0x89, 0x7c, 0x24, 0x48])
      (movM64R64Effect pc 15 (.sib 4 none 0 (.d8 0x48))) := by
  exact mov_m64_r64_effect_step_of_readable pc 0x4c (by unfold RexWPrefix; decide +kernel)
    7 (.sib 4 none 0 (.d8 0x48))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_100128 [Bindings] (pc : BitVec 64) :
    StepEffect (LoadPre pc
      (fun s ↦ ((.sib 4 none 0 (.d8 0x60)) : AddrMode).addr s (pc + 5)) 8)
      (codeRange pc [0x4c, 0x8b, 0x7c, 0x24, 0x60])
      (movR64M64Effect pc 15 (.sib 4 none 0 (.d8 0x60))) := by
  exact mov_r64_m64_effect_step pc 0x4c (by unfold RexWPrefix; decide +kernel)
    7 (.sib 4 none 0 (.d8 0x60))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_100136 [Bindings] (pc : BitVec 64) :
    StepEffect (LoadPre pc
      (fun s ↦ ((.sib 4 none 0 (.d8 0x58)) : AddrMode).addr s (pc + 5)) 8)
      (codeRange pc [0x48, 0x33, 0x54, 0x24, 0x58])
      (xorR64M64Effect pc 2 (.sib 4 none 0 (.d8 0x58))) := by
  exact xor_r64_m64_effect_step pc 0x48 (by unfold RexWPrefix; decide +kernel)
    2 (.sib 4 none 0 (.d8 0x58))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_10013e [Bindings] (pc : BitVec 64) :
    StepEffect (LoadPre pc
      (fun s ↦ ((.sib 4 none 0 (.d8 0x30)) : AddrMode).addr s (pc + 5)) 8)
      (codeRange pc [0x48, 0x33, 0x74, 0x24, 0x30])
      (xorR64M64Effect pc 6 (.sib 4 none 0 (.d8 0x30))) := by
  exact xor_r64_m64_effect_step pc 0x48 (by unfold RexWPrefix; decide +kernel)
    6 (.sib 4 none 0 (.d8 0x30))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_100149 [Bindings] (pc : BitVec 64) :
    StepEffect (StorePreReadable pc
      (storeAddrAt pc (.sib 4 none 0 (.d32 0x98)) 8) 8)
      (codeRange pc [0x48, 0x89, 0x9c, 0x24, 0x98, 0x00, 0x00, 0x00])
      (movM64R64Effect pc 3 (.sib 4 none 0 (.d32 0x98))) := by
  exact mov_m64_r64_effect_step_of_readable pc 0x48 (by unfold RexWPrefix; decide +kernel)
    3 (.sib 4 none 0 (.d32 0x98))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_100154 [Bindings] (pc : BitVec 64) :
    StepEffect (LoadPre pc
      (fun s ↦ ((.sib 4 none 0 (.d8 0x68)) : AddrMode).addr s (pc + 5)) 8)
      (codeRange pc [0x48, 0x33, 0x5c, 0x24, 0x68])
      (xorR64M64Effect pc 3 (.sib 4 none 0 (.d8 0x68))) := by
  exact xor_r64_m64_effect_step pc 0x48 (by unfold RexWPrefix; decide +kernel)
    3 (.sib 4 none 0 (.d8 0x68))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_100159 [Bindings] (pc : BitVec 64) :
    StepEffect (LoadPre pc
      (fun s ↦ ((.sib 4 none 0 (.d8 0x38)) : AddrMode).addr s (pc + 5)) 8)
      (codeRange pc [0x48, 0x8b, 0x54, 0x24, 0x38])
      (movR64M64Effect pc 2 (.sib 4 none 0 (.d8 0x38))) := by
  exact mov_r64_m64_effect_step pc 0x48 (by unfold RexWPrefix; decide +kernel)
    2 (.sib 4 none 0 (.d8 0x38))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_100164 [Bindings] (pc : BitVec 64) :
    StepEffect (LoadPre pc
      (fun s ↦ ((.sib 4 none 0 (.d8 0x78)) : AddrMode).addr s (pc + 5)) 8)
      (codeRange pc [0x48, 0x33, 0x44, 0x24, 0x78])
      (xorR64M64Effect pc 0 (.sib 4 none 0 (.d8 0x78))) := by
  exact xor_r64_m64_effect_step pc 0x48 (by unfold RexWPrefix; decide +kernel)
    0 (.sib 4 none 0 (.d8 0x78))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_10016f [Bindings] (pc : BitVec 64) :
    StepEffect (LoadPre pc
      (fun s ↦ ((.sib 4 none 0 .none) : AddrMode).addr s (pc + 4)) 8)
      (codeRange pc [0x48, 0x33, 0x1c, 0x24])
      (xorR64M64Effect pc 3 (.sib 4 none 0 .none)) := by
  exact xor_r64_m64_effect_step pc 0x48 (by unfold RexWPrefix; decide +kernel)
    3 (.sib 4 none 0 .none)
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_100173 [Bindings] (pc : BitVec 64) :
    StepEffect (LoadPre pc
      (fun s ↦ ((.sib 4 none 0 (.d8 0x40)) : AddrMode).addr s (pc + 5)) 8)
      (codeRange pc [0x48, 0x8b, 0x7c, 0x24, 0x40])
      (movR64M64Effect pc 7 (.sib 4 none 0 (.d8 0x40))) := by
  exact mov_r64_m64_effect_step pc 0x48 (by unfold RexWPrefix; decide +kernel)
    7 (.sib 4 none 0 (.d8 0x40))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_100178 [Bindings] (pc : BitVec 64) :
    StepEffect (LoadPre pc
      (fun s ↦ ((.sib 4 none 0 (.d8 0x70)) : AddrMode).addr s (pc + 5)) 8)
      (codeRange pc [0x48, 0x33, 0x7c, 0x24, 0x70])
      (xorR64M64Effect pc 7 (.sib 4 none 0 (.d8 0x70))) := by
  exact xor_r64_m64_effect_step pc 0x48 (by unfold RexWPrefix; decide +kernel)
    7 (.sib 4 none 0 (.d8 0x70))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_100180 [Bindings] (pc : BitVec 64) :
    StepEffect (LoadPre pc
      (fun s ↦ ((.sib 4 none 0 (.d8 0x18)) : AddrMode).addr s (pc + 5)) 8)
      (codeRange pc [0x48, 0x8b, 0x5c, 0x24, 0x18])
      (movR64M64Effect pc 3 (.sib 4 none 0 (.d8 0x18))) := by
  exact mov_r64_m64_effect_step pc 0x48 (by unfold RexWPrefix; decide +kernel)
    3 (.sib 4 none 0 (.d8 0x18))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_10018b [Bindings] (pc : BitVec 64) :
    StepEffect (LoadPre pc
      (fun s ↦ ((.sib 4 none 0 (.d8 0x28)) : AddrMode).addr s (pc + 5)) 8)
      (codeRange pc [0x48, 0x8b, 0x4c, 0x24, 0x28])
      (movR64M64Effect pc 1 (.sib 4 none 0 (.d8 0x28))) := by
  exact mov_r64_m64_effect_step pc 0x48 (by unfold RexWPrefix; decide +kernel)
    1 (.sib 4 none 0 (.d8 0x28))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_1001a2 [Bindings] (pc : BitVec 64) :
    StepEffect (LoadPre pc
      (fun s ↦ ((.sib 4 none 0 (.d8 0x10)) : AddrMode).addr s (pc + 5)) 8)
      (codeRange pc [0x4c, 0x8b, 0x74, 0x24, 0x10])
      (movR64M64Effect pc 14 (.sib 4 none 0 (.d8 0x10))) := by
  exact mov_r64_m64_effect_step pc 0x4c (by unfold RexWPrefix; decide +kernel)
    6 (.sib 4 none 0 (.d8 0x10))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_1001b0 [Bindings] (pc : BitVec 64) :
    StepEffect (StorePreReadable pc
      (storeAddrAt pc (.sib 4 none 0 (.d32 0x90)) 8) 8)
      (codeRange pc [0x48, 0x89, 0x9c, 0x24, 0x90, 0x00, 0x00, 0x00])
      (movM64R64Effect pc 3 (.sib 4 none 0 (.d32 0x90))) := by
  exact mov_m64_r64_effect_step_of_readable pc 0x48 (by unfold RexWPrefix; decide +kernel)
    3 (.sib 4 none 0 (.d32 0x90))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_1001b8 [Bindings] (pc : BitVec 64) :
    StepEffect (StorePreReadable pc
      (storeAddrAt pc (.sib 4 none 0 (.d8 0x20)) 5) 8)
      (codeRange pc [0x4c, 0x31, 0x7c, 0x24, 0x20])
      (xorMREffect pc 5 64 15 (.sib 4 none 0 (.d8 0x20))) := by
  exact xor_m64_r64_effect_step_of_readable pc 0x4c (by unfold RexWPrefix; decide +kernel)
    7 (.sib 4 none 0 (.d8 0x20))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_1001c0 [Bindings] (pc : BitVec 64) :
    StepEffect (StorePreReadable pc
      (storeAddrAt pc (.sib 4 none 0 (.d32 0xc0)) 8) 8)
      (codeRange pc [0x4c, 0x89, 0xac, 0x24, 0xc0, 0x00, 0x00, 0x00])
      (movM64R64Effect pc 13 (.sib 4 none 0 (.d32 0xc0))) := by
  exact mov_m64_r64_effect_step_of_readable pc 0x4c (by unfold RexWPrefix; decide +kernel)
    5 (.sib 4 none 0 (.d32 0xc0))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_1001cb [Bindings] (pc : BitVec 64) :
    StepEffect (LoadPre pc
      (fun s ↦ ((.sib 4 none 0 (.d8 0x50)) : AddrMode).addr s (pc + 5)) 8)
      (codeRange pc [0x4c, 0x33, 0x7c, 0x24, 0x50])
      (xorR64M64Effect pc 15 (.sib 4 none 0 (.d8 0x50))) := by
  exact xor_r64_m64_effect_step pc 0x4c (by unfold RexWPrefix; decide +kernel)
    7 (.sib 4 none 0 (.d8 0x50))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_1001d0 [Bindings] (pc : BitVec 64) :
    StepEffect (StorePreReadable pc
      (storeAddrAt pc (.sib 4 none 0 (.d32 0xc8)) 8) 8)
      (codeRange pc [0x4c, 0x89, 0xbc, 0x24, 0xc8, 0x00, 0x00, 0x00])
      (movM64R64Effect pc 15 (.sib 4 none 0 (.d32 0xc8))) := by
  exact mov_m64_r64_effect_step_of_readable pc 0x4c (by unfold RexWPrefix; decide +kernel)
    7 (.sib 4 none 0 (.d32 0xc8))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_1001d8 [Bindings] (pc : BitVec 64) :
    StepEffect (LoadPre pc
      (fun s ↦ ((.sib 4 none 0 (.d32 0x88)) : AddrMode).addr s (pc + 8)) 8)
      (codeRange pc [0x4c, 0x8b, 0xbc, 0x24, 0x88, 0x00, 0x00, 0x00])
      (movR64M64Effect pc 15 (.sib 4 none 0 (.d32 0x88))) := by
  exact mov_r64_m64_effect_step pc 0x4c (by unfold RexWPrefix; decide +kernel)
    7 (.sib 4 none 0 (.d32 0x88))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_1001ef [Bindings] (pc : BitVec 64) :
    StepEffect (LoadPre pc
      (fun s ↦ ((.sib 4 none 0 (.d32 0x80)) : AddrMode).addr s (pc + 8)) 8)
      (codeRange pc [0x48, 0x8b, 0x9c, 0x24, 0x80, 0x00, 0x00, 0x00])
      (movR64M64Effect pc 3 (.sib 4 none 0 (.d32 0x80))) := by
  exact mov_r64_m64_effect_step pc 0x48 (by unfold RexWPrefix; decide +kernel)
    3 (.sib 4 none 0 (.d32 0x80))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_100200 [Bindings] (pc : BitVec 64) :
    StepEffect (StorePreReadable pc
      (storeAddrAt pc (.sib 4 none 0 (.d8 0x28)) 5) 8)
      (codeRange pc [0x48, 0x89, 0x4c, 0x24, 0x28])
      (movM64R64Effect pc 1 (.sib 4 none 0 (.d8 0x28))) := by
  exact mov_m64_r64_effect_step_of_readable pc 0x48 (by unfold RexWPrefix; decide +kernel)
    1 (.sib 4 none 0 (.d8 0x28))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_100208 [Bindings] (pc : BitVec 64) :
    StepEffect (StorePreReadable pc
      (storeAddrAt pc (.sib 4 none 0 (.d32 0xb8)) 8) 8)
      (codeRange pc [0x4c, 0x89, 0x94, 0x24, 0xb8, 0x00, 0x00, 0x00])
      (movM64R64Effect pc 10 (.sib 4 none 0 (.d32 0xb8))) := by
  exact mov_m64_r64_effect_step_of_readable pc 0x4c (by unfold RexWPrefix; decide +kernel)
    2 (.sib 4 none 0 (.d32 0xb8))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_100210 [Bindings] (pc : BitVec 64) :
    StepEffect (LoadPre pc
      (fun s ↦ ((.sib 4 none 0 (.d8 0x60)) : AddrMode).addr s (pc + 5)) 8)
      (codeRange pc [0x48, 0x33, 0x74, 0x24, 0x60])
      (xorR64M64Effect pc 6 (.sib 4 none 0 (.d8 0x60))) := by
  exact xor_r64_m64_effect_step pc 0x48 (by unfold RexWPrefix; decide +kernel)
    6 (.sib 4 none 0 (.d8 0x60))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_100218 [Bindings] (pc : BitVec 64) :
    StepEffect (StorePreReadable pc
      (storeAddrAt pc (.sib 4 none 0 (.d8 0x30)) 5) 8)
      (codeRange pc [0x48, 0x31, 0x54, 0x24, 0x30])
      (xorMREffect pc 5 64 2 (.sib 4 none 0 (.d8 0x30))) := by
  exact xor_m64_r64_effect_step_of_readable pc 0x48 (by unfold RexWPrefix; decide +kernel)
    2 (.sib 4 none 0 (.d8 0x30))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_100220 [Bindings] (pc : BitVec 64) :
    StepEffect (StorePreReadable pc
      (storeAddrAt pc (.sib 4 none 0 (.d8 0x48)) 5) 8)
      (codeRange pc [0x48, 0x31, 0x54, 0x24, 0x48])
      (xorMREffect pc 5 64 2 (.sib 4 none 0 (.d8 0x48))) := by
  exact xor_m64_r64_effect_step_of_readable pc 0x48 (by unfold RexWPrefix; decide +kernel)
    2 (.sib 4 none 0 (.d8 0x48))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_100225 [Bindings] (pc : BitVec 64) :
    StepEffect (LoadPre pc
      (fun s ↦ ((.sib 4 none 0 (.d8 0x58)) : AddrMode).addr s (pc + 5)) 8)
      (codeRange pc [0x48, 0x33, 0x54, 0x24, 0x58])
      (xorR64M64Effect pc 2 (.sib 4 none 0 (.d8 0x58))) := by
  exact xor_r64_m64_effect_step pc 0x48 (by unfold RexWPrefix; decide +kernel)
    2 (.sib 4 none 0 (.d8 0x58))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_10022d [Bindings] (pc : BitVec 64) :
    StepEffect (LoadPre pc
      (fun s ↦ ((.sib 4 none 0 (.d8 0x78)) : AddrMode).addr s (pc + 5)) 8)
      (codeRange pc [0x4c, 0x8b, 0x54, 0x24, 0x78])
      (movR64M64Effect pc 10 (.sib 4 none 0 (.d8 0x78))) := by
  exact mov_r64_m64_effect_step pc 0x4c (by unfold RexWPrefix; decide +kernel)
    2 (.sib 4 none 0 (.d8 0x78))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_100238 [Bindings] (pc : BitVec 64) :
    StepEffect (StorePreReadable pc
      (storeAddrAt pc (.sib 4 none 0 (.d8 0x38)) 5) 8)
      (codeRange pc [0x48, 0x31, 0x7c, 0x24, 0x38])
      (xorMREffect pc 5 64 7 (.sib 4 none 0 (.d8 0x38))) := by
  exact xor_m64_r64_effect_step_of_readable pc 0x48 (by unfold RexWPrefix; decide +kernel)
    7 (.sib 4 none 0 (.d8 0x38))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_10023d [Bindings] (pc : BitVec 64) :
    StepEffect (LoadPre pc
      (fun s ↦ ((.sib 4 none 0 (.d8 0x8)) : AddrMode).addr s (pc + 5)) 8)
      (codeRange pc [0x48, 0x8b, 0x54, 0x24, 0x08])
      (movR64M64Effect pc 2 (.sib 4 none 0 (.d8 0x8))) := by
  exact mov_r64_m64_effect_step pc 0x48 (by unfold RexWPrefix; decide +kernel)
    2 (.sib 4 none 0 (.d8 0x8))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_100248 [Bindings] (pc : BitVec 64) :
    StepEffect (LoadPre pc
      (fun s ↦ ((.sib 4 none 0 (.d8 0x68)) : AddrMode).addr s (pc + 5)) 8)
      (codeRange pc [0x48, 0x33, 0x7c, 0x24, 0x68])
      (xorR64M64Effect pc 7 (.sib 4 none 0 (.d8 0x68))) := by
  exact xor_r64_m64_effect_step pc 0x48 (by unfold RexWPrefix; decide +kernel)
    7 (.sib 4 none 0 (.d8 0x68))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_10024d [Bindings] (pc : BitVec 64) :
    StepEffect (StorePreReadable pc
      (storeAddrAt pc (.sib 4 none 0 (.d8 0x8)) 5) 8)
      (codeRange pc [0x48, 0x89, 0x7c, 0x24, 0x08])
      (movM64R64Effect pc 7 (.sib 4 none 0 (.d8 0x8))) := by
  exact mov_m64_r64_effect_step_of_readable pc 0x48 (by unfold RexWPrefix; decide +kernel)
    7 (.sib 4 none 0 (.d8 0x8))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_100255 [Bindings] (pc : BitVec 64) :
    StepEffect (LoadPre pc
      (fun s ↦ ((.sib 4 none 0 (.d8 0x70)) : AddrMode).addr s (pc + 5)) 8)
      (codeRange pc [0x48, 0x8b, 0x44, 0x24, 0x70])
      (movR64M64Effect pc 0 (.sib 4 none 0 (.d8 0x70))) := by
  exact mov_r64_m64_effect_step pc 0x48 (by unfold RexWPrefix; decide +kernel)
    0 (.sib 4 none 0 (.d8 0x70))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_100260 [Bindings] (pc : BitVec 64) :
    StepEffect (StorePreReadable pc
      (storeAddrAt pc (.sib 4 none 0 (.d8 0x10)) 5) 8)
      (codeRange pc [0x4c, 0x89, 0x74, 0x24, 0x10])
      (movM64R64Effect pc 14 (.sib 4 none 0 (.d8 0x10))) := by
  exact mov_m64_r64_effect_step_of_readable pc 0x4c (by unfold RexWPrefix; decide +kernel)
    6 (.sib 4 none 0 (.d8 0x10))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_100265 [Bindings] (pc : BitVec 64) :
    StepEffect (LoadPre pc
      (fun s ↦ ((.sib 4 none 0 (.d8 0x40)) : AddrMode).addr s (pc + 5)) 8)
      (codeRange pc [0x48, 0x8b, 0x7c, 0x24, 0x40])
      (movR64M64Effect pc 7 (.sib 4 none 0 (.d8 0x40))) := by
  exact mov_r64_m64_effect_step pc 0x48 (by unfold RexWPrefix; decide +kernel)
    7 (.sib 4 none 0 (.d8 0x40))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_10026d [Bindings] (pc : BitVec 64) :
    StepEffect (StorePreReadable pc
      (storeAddrAt pc (.sib 4 none 0 (.d32 0x98)) 8) 8)
      (codeRange pc [0x4c, 0x31, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00])
      (xorMREffect pc 8 64 8 (.sib 4 none 0 (.d32 0x98))) := by
  exact xor_m64_r64_effect_step_of_readable pc 0x4c (by unfold RexWPrefix; decide +kernel)
    0 (.sib 4 none 0 (.d32 0x98))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_100279 [Bindings] (pc : BitVec 64) :
    StepEffect (LoadPre pc
      (fun s ↦ ((.sib 4 none 0 .none) : AddrMode).addr s (pc + 4)) 8)
      (codeRange pc [0x4c, 0x33, 0x04, 0x24])
      (xorR64M64Effect pc 8 (.sib 4 none 0 .none)) := by
  exact xor_r64_m64_effect_step pc 0x4c (by unfold RexWPrefix; decide +kernel)
    0 (.sib 4 none 0 .none)
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_10028d [Bindings] (pc : BitVec 64) :
    StepEffect (StorePreReadable pc
      (storeAddrAt pc (.sib 4 none 0 (.d8 0x40)) 5) 8)
      (codeRange pc [0x48, 0x89, 0x5c, 0x24, 0x40])
      (movM64R64Effect pc 3 (.sib 4 none 0 (.d8 0x40))) := by
  exact mov_m64_r64_effect_step_of_readable pc 0x48 (by unfold RexWPrefix; decide +kernel)
    3 (.sib 4 none 0 (.d8 0x40))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_1002a1 [Bindings] (pc : BitVec 64) :
    StepEffect (StorePreReadable pc
      (storeAddrAt pc (.sib 4 none 0 (.d32 0xb0)) 8) 8)
      (codeRange pc [0x48, 0x89, 0x84, 0x24, 0xb0, 0x00, 0x00, 0x00])
      (movM64R64Effect pc 0 (.sib 4 none 0 (.d32 0xb0))) := by
  exact mov_m64_r64_effect_step_of_readable pc 0x48 (by unfold RexWPrefix; decide +kernel)
    0 (.sib 4 none 0 (.d32 0xb0))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_1002b6 [Bindings] (pc : BitVec 64) :
    StepEffect (StorePreReadable pc
      (storeAddrAt pc (.sib 4 none 0 (.d8 0x18)) 5) 8)
      (codeRange pc [0x48, 0x89, 0x44, 0x24, 0x18])
      (movM64R64Effect pc 0 (.sib 4 none 0 (.d8 0x18))) := by
  exact mov_m64_r64_effect_step_of_readable pc 0x48 (by unfold RexWPrefix; decide +kernel)
    0 (.sib 4 none 0 (.d8 0x18))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_1002c7 [Bindings] (pc : BitVec 64) :
    StepEffect (StorePreReadable pc
      (storeAddrAt pc (.sib 4 none 0 (.d32 0x88)) 8) 8)
      (codeRange pc [0x48, 0x89, 0x94, 0x24, 0x88, 0x00, 0x00, 0x00])
      (movM64R64Effect pc 2 (.sib 4 none 0 (.d32 0x88))) := by
  exact mov_m64_r64_effect_step_of_readable pc 0x48 (by unfold RexWPrefix; decide +kernel)
    2 (.sib 4 none 0 (.d32 0x88))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_1002db [Bindings] (pc : BitVec 64) :
    StepEffect (StorePreReadable pc
      (storeAddrAt pc (.sib 4 none 0 (.d32 0x80)) 8) 8)
      (codeRange pc [0x4c, 0x89, 0xa4, 0x24, 0x80, 0x00, 0x00, 0x00])
      (movM64R64Effect pc 12 (.sib 4 none 0 (.d32 0x80))) := by
  exact mov_m64_r64_effect_step_of_readable pc 0x4c (by unfold RexWPrefix; decide +kernel)
    4 (.sib 4 none 0 (.d32 0x80))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_1002e3 [Bindings] (pc : BitVec 64) :
    StepEffect (LoadPre pc
      (fun s ↦ ((.sib 4 none 0 (.d32 0x90)) : AddrMode).addr s (pc + 8)) 8)
      (codeRange pc [0x4c, 0x8b, 0xa4, 0x24, 0x90, 0x00, 0x00, 0x00])
      (movR64M64Effect pc 12 (.sib 4 none 0 (.d32 0x90))) := by
  exact mov_r64_m64_effect_step pc 0x4c (by unfold RexWPrefix; decide +kernel)
    4 (.sib 4 none 0 (.d32 0x90))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_100300 [Bindings] (pc : BitVec 64) :
    StepEffect (StorePreReadable pc
      (storeAddrAt pc (.sib 4 none 0 (.d8 0x50)) 5) 8)
      (codeRange pc [0x48, 0x89, 0x54, 0x24, 0x50])
      (movM64R64Effect pc 2 (.sib 4 none 0 (.d8 0x50))) := by
  exact mov_m64_r64_effect_step_of_readable pc 0x48 (by unfold RexWPrefix; decide +kernel)
    2 (.sib 4 none 0 (.d8 0x50))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_10030b [Bindings] (pc : BitVec 64) :
    StepEffect (StorePreReadable pc
      (storeAddrAt pc (.sib 4 none 0 (.d32 0xa8)) 8) 8)
      (codeRange pc [0x48, 0x89, 0xb4, 0x24, 0xa8, 0x00, 0x00, 0x00])
      (movM64R64Effect pc 6 (.sib 4 none 0 (.d32 0xa8))) := by
  exact mov_m64_r64_effect_step_of_readable pc 0x48 (by unfold RexWPrefix; decide +kernel)
    6 (.sib 4 none 0 (.d32 0xa8))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_100319 [Bindings] (pc : BitVec 64) :
    StepEffect (StorePreReadable pc
      (storeAddrAt pc (.sib 4 none 0 (.d8 0x58)) 5) 8)
      (codeRange pc [0x48, 0x89, 0x54, 0x24, 0x58])
      (movM64R64Effect pc 2 (.sib 4 none 0 (.d8 0x58))) := by
  exact mov_m64_r64_effect_step_of_readable pc 0x48 (by unfold RexWPrefix; decide +kernel)
    2 (.sib 4 none 0 (.d8 0x58))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_10032a [Bindings] (pc : BitVec 64) :
    StepEffect (StorePreReadable pc
      (storeAddrAt pc (.sib 4 none 0 (.d8 0x60)) 5) 8)
      (codeRange pc [0x4c, 0x89, 0x7c, 0x24, 0x60])
      (movM64R64Effect pc 15 (.sib 4 none 0 (.d8 0x60))) := by
  exact mov_m64_r64_effect_step_of_readable pc 0x4c (by unfold RexWPrefix; decide +kernel)
    7 (.sib 4 none 0 (.d8 0x60))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_10033e [Bindings] (pc : BitVec 64) :
    StepEffect (StorePreReadable pc
      (storeAddrAt pc (.sib 4 none 0 .none) 4) 8)
      (codeRange pc [0x48, 0x89, 0x0c, 0x24])
      (movM64R64Effect pc 1 (.sib 4 none 0 .none)) := by
  exact mov_m64_r64_effect_step_of_readable pc 0x48 (by unfold RexWPrefix; decide +kernel)
    1 (.sib 4 none 0 .none)
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_100342 [Bindings] (pc : BitVec 64) :
    StepEffect (LoadPre pc
      (fun s ↦ ((.sib 4 none 0 (.d32 0xc0)) : AddrMode).addr s (pc + 8)) 8)
      (codeRange pc [0x48, 0x8b, 0x84, 0x24, 0xc0, 0x00, 0x00, 0x00])
      (movR64M64Effect pc 0 (.sib 4 none 0 (.d32 0xc0))) := by
  exact mov_r64_m64_effect_step pc 0x48 (by unfold RexWPrefix; decide +kernel)
    0 (.sib 4 none 0 (.d32 0xc0))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_100355 [Bindings] (pc : BitVec 64) :
    StepEffect (LoadPre pc
      (fun s ↦ ((.sib 4 none 0 (.d8 0x20)) : AddrMode).addr s (pc + 5)) 8)
      (codeRange pc [0x48, 0x8b, 0x4c, 0x24, 0x20])
      (movR64M64Effect pc 1 (.sib 4 none 0 (.d8 0x20))) := by
  exact mov_r64_m64_effect_step pc 0x48 (by unfold RexWPrefix; decide +kernel)
    1 (.sib 4 none 0 (.d8 0x20))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_10035a [Bindings] (pc : BitVec 64) :
    StepEffect (LoadPre pc
      (fun s ↦ ((.sib 4 none 0 (.d32 0xb8)) : AddrMode).addr s (pc + 8)) 8)
      (codeRange pc [0x4c, 0x8b, 0x94, 0x24, 0xb8, 0x00, 0x00, 0x00])
      (movR64M64Effect pc 10 (.sib 4 none 0 (.d32 0xb8))) := by
  exact mov_r64_m64_effect_step pc 0x4c (by unfold RexWPrefix; decide +kernel)
    2 (.sib 4 none 0 (.d32 0xb8))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_10036a [Bindings] (pc : BitVec 64) :
    StepEffect (LoadPre pc
      (fun s ↦ ((.sib 4 none 0 (.d8 0x10)) : AddrMode).addr s (pc + 5)) 8)
      (codeRange pc [0x4c, 0x8b, 0x7c, 0x24, 0x10])
      (movR64M64Effect pc 15 (.sib 4 none 0 (.d8 0x10))) := by
  exact mov_r64_m64_effect_step pc 0x4c (by unfold RexWPrefix; decide +kernel)
    7 (.sib 4 none 0 (.d8 0x10))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_10037f [Bindings] (pc : BitVec 64) :
    StepEffect (StorePreReadable pc
      (storeAddrAt pc (.sib 4 none 0 (.d8 0x20)) 5) 8)
      (codeRange pc [0x4c, 0x89, 0x4c, 0x24, 0x20])
      (movM64R64Effect pc 9 (.sib 4 none 0 (.d8 0x20))) := by
  exact mov_m64_r64_effect_step_of_readable pc 0x4c (by unfold RexWPrefix; decide +kernel)
    1 (.sib 4 none 0 (.d8 0x20))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_1003ab [Bindings] (pc : BitVec 64) :
    StepEffect (StorePreReadable pc
      (storeAddrAt pc (.sib 4 none 0 (.d8 0x78)) 5) 8)
      (codeRange pc [0x48, 0x89, 0x74, 0x24, 0x78])
      (movM64R64Effect pc 6 (.sib 4 none 0 (.d8 0x78))) := by
  exact mov_m64_r64_effect_step_of_readable pc 0x48 (by unfold RexWPrefix; decide +kernel)
    6 (.sib 4 none 0 (.d8 0x78))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_1003b3 [Bindings] (pc : BitVec 64) :
    StepEffect (StorePreReadable pc
      (storeAddrAt pc (.sib 4 none 0 (.d8 0x70)) 5) 8)
      (codeRange pc [0x48, 0x89, 0x5c, 0x24, 0x70])
      (movM64R64Effect pc 3 (.sib 4 none 0 (.d8 0x70))) := by
  exact mov_m64_r64_effect_step_of_readable pc 0x48 (by unfold RexWPrefix; decide +kernel)
    3 (.sib 4 none 0 (.d8 0x70))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_1003b8 [Bindings] (pc : BitVec 64) :
    StepEffect (LoadPre pc
      (fun s ↦ ((.sib 4 none 0 (.d8 0x30)) : AddrMode).addr s (pc + 5)) 8)
      (codeRange pc [0x48, 0x8b, 0x74, 0x24, 0x30])
      (movR64M64Effect pc 6 (.sib 4 none 0 (.d8 0x30))) := by
  exact mov_r64_m64_effect_step pc 0x48 (by unfold RexWPrefix; decide +kernel)
    6 (.sib 4 none 0 (.d8 0x30))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_1003c9 [Bindings] (pc : BitVec 64) :
    StepEffect (StorePreReadable pc
      (storeAddrAt pc (.sib 4 none 0 (.d8 0x30)) 5) 8)
      (codeRange pc [0x48, 0x89, 0x5c, 0x24, 0x30])
      (movM64R64Effect pc 3 (.sib 4 none 0 (.d8 0x30))) := by
  exact mov_m64_r64_effect_step_of_readable pc 0x48 (by unfold RexWPrefix; decide +kernel)
    3 (.sib 4 none 0 (.d8 0x30))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_1003d4 [Bindings] (pc : BitVec 64) :
    StepEffect (StorePreReadable pc
      (storeAddrAt pc (.sib 4 none 0 (.d8 0x10)) 5) 8)
      (codeRange pc [0x4c, 0x89, 0x7c, 0x24, 0x10])
      (movM64R64Effect pc 15 (.sib 4 none 0 (.d8 0x10))) := by
  exact mov_m64_r64_effect_step_of_readable pc 0x4c (by unfold RexWPrefix; decide +kernel)
    7 (.sib 4 none 0 (.d8 0x10))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_1003dc [Bindings] (pc : BitVec 64) :
    StepEffect (StorePreReadable pc
      (storeAddrAt pc (.sib 4 none 0 (.d8 0x68)) 5) 8)
      (codeRange pc [0x48, 0x89, 0x7c, 0x24, 0x68])
      (movM64R64Effect pc 7 (.sib 4 none 0 (.d8 0x68))) := by
  exact mov_m64_r64_effect_step_of_readable pc 0x48 (by unfold RexWPrefix; decide +kernel)
    7 (.sib 4 none 0 (.d8 0x68))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_1003e1 [Bindings] (pc : BitVec 64) :
    StepEffect (LoadPre pc
      (fun s ↦ ((.sib 4 none 0 (.d8 0x28)) : AddrMode).addr s (pc + 5)) 8)
      (codeRange pc [0x48, 0x8b, 0x44, 0x24, 0x28])
      (movR64M64Effect pc 0 (.sib 4 none 0 (.d8 0x28))) := by
  exact mov_r64_m64_effect_step pc 0x48 (by unfold RexWPrefix; decide +kernel)
    0 (.sib 4 none 0 (.d8 0x28))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_1003ea [Bindings] (pc : BitVec 64) :
    StepEffect (LoadPre pc
      (fun s ↦ ((.sib 4 none 0 (.d8 0x48)) : AddrMode).addr s (pc + 5)) 8)
      (codeRange pc [0x48, 0x8b, 0x5c, 0x24, 0x48])
      (movR64M64Effect pc 3 (.sib 4 none 0 (.d8 0x48))) := by
  exact mov_r64_m64_effect_step pc 0x48 (by unfold RexWPrefix; decide +kernel)
    3 (.sib 4 none 0 (.d8 0x48))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_1003fa [Bindings] (pc : BitVec 64) :
    StepEffect (StorePreReadable pc
      (storeAddrAt pc (.sib 4 none 0 (.d8 0x48)) 5) 8)
      (codeRange pc [0x48, 0x89, 0x6c, 0x24, 0x48])
      (movM64R64Effect pc 5 (.sib 4 none 0 (.d8 0x48))) := by
  exact mov_m64_r64_effect_step_of_readable pc 0x48 (by unfold RexWPrefix; decide +kernel)
    5 (.sib 4 none 0 (.d8 0x48))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_1003ff [Bindings] (pc : BitVec 64) :
    StepEffect (LoadPre pc
      (fun s ↦ ((.sib 4 none 0 (.d32 0xb0)) : AddrMode).addr s (pc + 8)) 8)
      (codeRange pc [0x4c, 0x8b, 0x84, 0x24, 0xb0, 0x00, 0x00, 0x00])
      (movR64M64Effect pc 8 (.sib 4 none 0 (.d32 0xb0))) := by
  exact mov_r64_m64_effect_step pc 0x4c (by unfold RexWPrefix; decide +kernel)
    0 (.sib 4 none 0 (.d32 0xb0))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_10040b [Bindings] (pc : BitVec 64) :
    StepEffect (LoadPre pc
      (fun s ↦ ((.sib 4 none 0 (.d8 0x8)) : AddrMode).addr s (pc + 5)) 8)
      (codeRange pc [0x48, 0x8b, 0x54, 0x24, 0x08])
      (movR64M64Effect pc 2 (.sib 4 none 0 (.d8 0x8))) := by
  exact mov_r64_m64_effect_step pc 0x48 (by unfold RexWPrefix; decide +kernel)
    2 (.sib 4 none 0 (.d8 0x8))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_100414 [Bindings] (pc : BitVec 64) :
    StepEffect (StorePreReadable pc
      (storeAddrAt pc (.sib 4 none 0 (.d8 0x8)) 5) 8)
      (codeRange pc [0x48, 0x89, 0x54, 0x24, 0x08])
      (movM64R64Effect pc 2 (.sib 4 none 0 (.d8 0x8))) := by
  exact mov_m64_r64_effect_step_of_readable pc 0x48 (by unfold RexWPrefix; decide +kernel)
    2 (.sib 4 none 0 (.d8 0x8))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_100440 [Bindings] (pc : BitVec 64) :
    StepEffect (LoadPre pc
      (fun s ↦ ((.sib 4 none 0 (.d8 0x40)) : AddrMode).addr s (pc + 5)) 8)
      (codeRange pc [0x48, 0x8b, 0x54, 0x24, 0x40])
      (movR64M64Effect pc 2 (.sib 4 none 0 (.d8 0x40))) := by
  exact mov_r64_m64_effect_step pc 0x48 (by unfold RexWPrefix; decide +kernel)
    2 (.sib 4 none 0 (.d8 0x40))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_10044c [Bindings] (pc : BitVec 64) :
    StepEffect (LoadPre pc
      (fun s ↦ ((.sib 4 none 0 (.d32 0x98)) : AddrMode).addr s (pc + 8)) 8)
      (codeRange pc [0x48, 0x8b, 0xbc, 0x24, 0x98, 0x00, 0x00, 0x00])
      (movR64M64Effect pc 7 (.sib 4 none 0 (.d32 0x98))) := by
  exact mov_r64_m64_effect_step pc 0x48 (by unfold RexWPrefix; decide +kernel)
    7 (.sib 4 none 0 (.d32 0x98))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_100458 [Bindings] (pc : BitVec 64) :
    StepEffect (LoadPre pc
      (fun s ↦ ((.sib 4 none 0 (.d8 0x38)) : AddrMode).addr s (pc + 5)) 8)
      (codeRange pc [0x48, 0x8b, 0x5c, 0x24, 0x38])
      (movR64M64Effect pc 3 (.sib 4 none 0 (.d8 0x38))) := by
  exact mov_r64_m64_effect_step pc 0x48 (by unfold RexWPrefix; decide +kernel)
    3 (.sib 4 none 0 (.d8 0x38))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_100461 [Bindings] (pc : BitVec 64) :
    StepEffect (LoadPre pc
      (fun s ↦ ((.sib 4 none 0 (.d32 0xc8)) : AddrMode).addr s (pc + 8)) 8)
      (codeRange pc [0x4c, 0x8b, 0x94, 0x24, 0xc8, 0x00, 0x00, 0x00])
      (movR64M64Effect pc 10 (.sib 4 none 0 (.d32 0xc8))) := by
  exact mov_r64_m64_effect_step pc 0x4c (by unfold RexWPrefix; decide +kernel)
    2 (.sib 4 none 0 (.d32 0xc8))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_100494 [Bindings] (pc : BitVec 64) :
    StepEffect (StorePreReadable pc
      (storeAddrAt pc (.sib 4 none 0 (.d8 0x38)) 5) 8)
      (codeRange pc [0x4c, 0x89, 0x6c, 0x24, 0x38])
      (movM64R64Effect pc 13 (.sib 4 none 0 (.d8 0x38))) := by
  exact mov_m64_r64_effect_step_of_readable pc 0x4c (by unfold RexWPrefix; decide +kernel)
    5 (.sib 4 none 0 (.d8 0x38))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_10049f [Bindings] (pc : BitVec 64) :
    StepEffect (StorePreReadable pc
      (storeAddrAt pc (.sib 4 none 0 (.d8 0x28)) 5) 8)
      (codeRange pc [0x48, 0x89, 0x5c, 0x24, 0x28])
      (movM64R64Effect pc 3 (.sib 4 none 0 (.d8 0x28))) := by
  exact mov_m64_r64_effect_step_of_readable pc 0x48 (by unfold RexWPrefix; decide +kernel)
    3 (.sib 4 none 0 (.d8 0x28))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_1004b3 [Bindings] (pc : BitVec 64) :
    StepEffect (LoadPre pc
      (fun s ↦ ((.sib 4 none 0 (.d8 0x48)) : AddrMode).addr s (pc + 5)) 8)
      (codeRange pc [0x48, 0x8b, 0x54, 0x24, 0x48])
      (movR64M64Effect pc 2 (.sib 4 none 0 (.d8 0x48))) := by
  exact mov_r64_m64_effect_step pc 0x48 (by unfold RexWPrefix; decide +kernel)
    2 (.sib 4 none 0 (.d8 0x48))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_1004c1 [Bindings] (pc : BitVec 64) :
    StepEffect (LoadPre pc
      (fun s ↦ ((.sib 4 none 0 (.d32 0xd0)) : AddrMode).addr s (pc + 8)) 8)
      (codeRange pc [0x48, 0x8b, 0x94, 0x24, 0xd0, 0x00, 0x00, 0x00])
      (movR64M64Effect pc 2 (.sib 4 none 0 (.d32 0xd0))) := by
  exact mov_r64_m64_effect_step pc 0x48 (by unfold RexWPrefix; decide +kernel)
    2 (.sib 4 none 0 (.d32 0xd0))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_1004cc [Bindings] (pc : BitVec 64) :
    StepEffect (LoadPre pc
      (fun s ↦ ((.sib 4 none 0 (.d8 0x8)) : AddrMode).addr s (pc + 5)) 8)
      (codeRange pc [0x48, 0x33, 0x5c, 0x24, 0x08])
      (xorR64M64Effect pc 3 (.sib 4 none 0 (.d8 0x8))) := by
  exact xor_r64_m64_effect_step pc 0x48 (by unfold RexWPrefix; decide +kernel)
    3 (.sib 4 none 0 (.d8 0x8))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_1004d1 [Bindings] (pc : BitVec 64) :
    StepEffect (LoadPre pc
      (fun s ↦ ((.sib 4 none 0 (.d8 0x18)) : AddrMode).addr s (pc + 5)) 8)
      (codeRange pc [0x48, 0x8b, 0x74, 0x24, 0x18])
      (movR64M64Effect pc 6 (.sib 4 none 0 (.d8 0x18))) := by
  exact mov_r64_m64_effect_step pc 0x48 (by unfold RexWPrefix; decide +kernel)
    6 (.sib 4 none 0 (.d8 0x18))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_1004d6 [Bindings] (copy : Copy) (pc : BitVec 64) :
    StepEffect (LoadPre pc
      (fun s ↦ ((.base 2 (.d32 ((constantBase copy).setWidth 32))) : AddrMode).addr s (pc + 7)) 8)
      (codeRange pc
        [0x48, 0x33, 0xb2, if copy = .absorb then 0x00 else 0xc0, 0x00, 0x20, 0x00])
      (xorR64M64Effect pc 6 (.base 2 (.d32 ((constantBase copy).setWidth 32)))) := by
  cases copy <;>
    exact xor_r64_m64_effect_step pc 0x48 (by unfold RexWPrefix; decide +kernel)
      6 (.base 2 (.d32 _))
      (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_1004dd [Bindings] (pc : BitVec 64) :
    StepEffect (LoadPre pc
      (fun s ↦ ((.sib 4 none 0 .none) : AddrMode).addr s (pc + 4)) 8)
      (codeRange pc [0x48, 0x8b, 0x3c, 0x24])
      (movR64M64Effect pc 7 (.sib 4 none 0 .none)) := by
  exact mov_r64_m64_effect_step pc 0x48 (by unfold RexWPrefix; decide +kernel)
    7 (.sib 4 none 0 .none)
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_1004e1 [Bindings] (pc : BitVec 64) :
    StepEffect (LoadPre pc
      (fun s ↦ ((.sib 4 none 0 (.d32 0xa8)) : AddrMode).addr s (pc + 8)) 8)
      (codeRange pc [0x48, 0x33, 0xbc, 0x24, 0xa8, 0x00, 0x00, 0x00])
      (xorR64M64Effect pc 7 (.sib 4 none 0 (.d32 0xa8))) := by
  exact xor_r64_m64_effect_step pc 0x48 (by unfold RexWPrefix; decide +kernel)
    7 (.sib 4 none 0 (.d32 0xa8))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_1004e9 [Bindings] (pc : BitVec 64) :
    StepEffect (StorePreReadable pc
      (storeAddrAt pc (.sib 4 none 0 .none) 4) 8)
      (codeRange pc [0x48, 0x89, 0x3c, 0x24])
      (movM64R64Effect pc 7 (.sib 4 none 0 .none)) := by
  exact mov_m64_r64_effect_step_of_readable pc 0x48 (by unfold RexWPrefix; decide +kernel)
    7 (.sib 4 none 0 .none)
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_1004ed [Bindings] (pc : BitVec 64) :
    StepEffect (LoadPre pc
      (fun s ↦ ((.sib 4 none 0 (.d32 0x90)) : AddrMode).addr s (pc + 8)) 8)
      (codeRange pc [0x48, 0x33, 0xb4, 0x24, 0x90, 0x00, 0x00, 0x00])
      (xorR64M64Effect pc 6 (.sib 4 none 0 (.d32 0x90))) := by
  exact xor_r64_m64_effect_step pc 0x48 (by unfold RexWPrefix; decide +kernel)
    6 (.sib 4 none 0 (.d32 0x90))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_1004f5 [Bindings] (pc : BitVec 64) :
    StepEffect (StorePreReadable pc
      (storeAddrAt pc (.sib 4 none 0 (.d8 0x18)) 5) 8)
      (codeRange pc [0x48, 0x89, 0x74, 0x24, 0x18])
      (movM64R64Effect pc 6 (.sib 4 none 0 (.d8 0x18))) := by
  exact mov_m64_r64_effect_step_of_readable pc 0x48 (by unfold RexWPrefix; decide +kernel)
    6 (.sib 4 none 0 (.d8 0x18))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

end Sha3.Proofs.Permutation.RoundMachine
