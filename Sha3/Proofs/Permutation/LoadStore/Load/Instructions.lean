import Sha3.Proofs.Image
import Sha3.Proofs.Permutation.Layout
import Sha3.Proofs.Permutation.InstructionEffects
import Sha3.Proofs.Permutation.LoadStore.Memory

namespace Sha3.Proofs.Permutation.Load

open X86 X86.Machine X86.UserProcess X86Proofs Sha3.Spec.Program

def loadInstructionBytes (copy : Copy) : List (BitVec 64 × List UInt8) :=
  [
    ((entryAddress copy + 0xa), encodeSubR64Imm32 4 216),
    ((entryAddress copy + 0x11), encodeMovR64M64 0 (.base 7 .none)),
    ((entryAddress copy + 0x14), encodeMovM64R64 0 (.sib 4 none 0 (.d8 0x18))),
    ((entryAddress copy + 0x19), encodeMovR64M64 0 (.base 7 (.d8 0x8))),
    ((entryAddress copy + 0x1d), encodeMovM64R64 0 (.sib 4 none 0 (.d32 0x80))),
    ((entryAddress copy + 0x25), encodeMovR64M64 0 (.base 7 (.d8 0x50))),
    ((entryAddress copy + 0x29), encodeMovR64M64 5 (.base 7 (.d8 0x78))),
    ((entryAddress copy + 0x2d), encodeMovR64M64 1 (.base 7 (.d32 0xa0))),
    ((entryAddress copy + 0x34), encodeMovM64R64 1 (.sib 4 none 0 (.d8 0x50))),
    ((entryAddress copy + 0x39), encodeMovR64M64 1 (.base 7 (.d8 0x58))),
    ((entryAddress copy + 0x3d), encodeMovM64R64 1 (.sib 4 none 0 (.d8 0x28))),
    ((entryAddress copy + 0x42), encodeMovR64M64 1 (.base 7 (.d32 0x80))),
    ((entryAddress copy + 0x49), encodeMovR64M64 2 (.base 7 (.d32 0xa8))),
    ((entryAddress copy + 0x50), encodeMovM64R64 2 (.sib 4 none 0 (.d8 0x60))),
    ((entryAddress copy + 0x55), encodeMovR64M64 12 (.base 7 (.d8 0x60))),
    ((entryAddress copy + 0x59), encodeMovR64M64 15 (.base 7 (.d32 0x88))),
    ((entryAddress copy + 0x60), encodeMovR64M64 2 (.base 7 (.d32 0xb0))),
    ((entryAddress copy + 0x67), encodeMovM64R64 2 (.sib 4 none 0 (.d8 0x58))),
    ((entryAddress copy + 0x6c), encodeMovR64M64 2 (.base 7 (.d8 0x68))),
    ((entryAddress copy + 0x70), encodeMovM64R64 2 (.sib 4 none 0 (.d8 0x38))),
    ((entryAddress copy + 0x75), encodeMovR64M64 14 (.base 7 (.d32 0x90))),
    ((entryAddress copy + 0x7c), encodeMovR64M64 2 (.base 7 (.d32 0xb8))),
    ((entryAddress copy + 0x83), encodeMovM64R64 2 (.sib 4 none 0 (.d8 0x68))),
    ((entryAddress copy + 0x88), encodeMovR64M64 13 (.base 7 (.d8 0x70))),
    ((entryAddress copy + 0x8c), encodeMovR64M64 3 (.base 7 (.d32 0x98))),
    ((entryAddress copy + 0x93), encodeMovR64M64 2 (.base 7 (.d32 0xc0))),
    ((entryAddress copy + 0x9a), encodeMovM64R64 2 (.sib 4 none 0 .none)),
    ((entryAddress copy + 0x9e), encodeMovR64M64 11 (.base 7 (.d8 0x40))),
    ((entryAddress copy + 0xa2), encodeMovR64M64 2 (.base 7 (.d8 0x48))),
    ((entryAddress copy + 0xa6), encodeMovM64R64 2 (.sib 4 none 0 (.d8 0x10))),
    ((entryAddress copy + 0xab), encodeMovR64M64 6 (.base 7 (.d8 0x28))),
    ((entryAddress copy + 0xaf), encodeMovM64R64 6 (.sib 4 none 0 (.d8 0x20))),
    ((entryAddress copy + 0xb4), encodeMovR64M64 9 (.base 7 (.d8 0x30))),
    ((entryAddress copy + 0xb8), encodeMovR64M64 6 (.base 7 (.d8 0x10))),
    ((entryAddress copy + 0xbc), encodeMovM64R64 6 (.sib 4 none 0 (.d32 0x88))),
    ((entryAddress copy + 0xc4), encodeMovR64M64 6 (.base 7 (.d8 0x38))),
    ((entryAddress copy + 0xc8), encodeMovM64R64 6 (.sib 4 none 0 (.d8 0x30))),
    ((entryAddress copy + 0xcd), encodeMovR64M64 6 (.base 7 (.d8 0x18))),
    ((entryAddress copy + 0xd1), encodeMovM64R64 6 (.sib 4 none 0 (.d8 0x78))),
    ((entryAddress copy + 0xd6), encodeMovM64R64 7 (.sib 4 none 0 (.d32 0xa0))),
    ((entryAddress copy + 0xde), encodeMovR64M64 6 (.base 7 (.d8 0x20))),
    ((entryAddress copy + 0xe2), encodeMovM64R64 6 (.sib 4 none 0 (.d8 0x70))),
    ((entryAddress copy + 0xe7), encodeXorR32R32 2 2),
    ((entryAddress copy + 0xe9), encodeNopM [] (.base 0 (.d32 0)))
  ]

def loadBytes (copy : Copy) : List UInt8 := (loadInstructionBytes copy).flatMap Prod.snd

def loadCode (copy : Copy) : CodeMap := codeRange (entryAddress copy + 0xa) (loadBytes copy)

theorem loadInstructionBytes_length (copy : Copy) :
    (loadInstructionBytes copy).length = 44 := by
  cases copy <;> decide +kernel

theorem loadBytes_length (copy : Copy) : (loadBytes copy).length = 230 := by
  cases copy <;> decide +kernel

theorem loadBytes_extracted (copy : Copy) :
    Extracted.textBytes.toListFrom ((entryAddress copy).toNat - 0x100000 + 0xa) 230 =
      loadBytes copy := by
  cases copy <;> decide +kernel

theorem loadCode_subset_programImage (copy : Copy) :
    ∀ x ∈ loadCode copy, x ∈ Extracted.programImage := by
  cases copy with
  | absorb =>
    exact textSlice_subset_programImage (by decide +kernel) (loadBytes_extracted .absorb)
  | finalize =>
    exact textSlice_subset_programImage (by decide +kernel) (loadBytes_extracted .finalize)

set_option maxRecDepth 2048 in
theorem loadInstruction_code_subset (copy : Copy) :
    ∀ instruction ∈ loadInstructionBytes copy,
      ∀ x ∈ codeRange instruction.1 instruction.2, x ∈ loadCode copy := by
  cases copy <;> decide +kernel

theorem loadInstruction_next_inProgram (copy : Copy) {pc : BitVec 64} {bytes : List UInt8}
    (h : (pc, bytes) ∈ loadInstructionBytes copy) :
    InProgram (pc + BitVec.ofNat 64 bytes.length) := by
  have hnext : ∀ instruction ∈ loadInstructionBytes copy,
      (Extracted.programSections.fetchByte
        (instruction.1 + BitVec.ofNat 64 instruction.2.length)).isSome := by
    cases copy <;> decide +kernel
  obtain ⟨byte, hb⟩ := Option.isSome_iff_exists.mp (hnext (pc, bytes) h)
  exact ⟨byte, imageSections_mem_toCodeMap_of_fetchByte hb⟩

theorem step_00a (copy : Copy) [Bindings] :
    StepEffect (fun s ↦ s.RIP = (entryAddress copy + 0xa : BitVec 64))
      (codeRange (entryAddress copy + 0xa) (encodeSubR64Imm32 4 216))
      (subR64Imm32Effect (entryAddress copy + 0xa) 4 216) := by
  exact sub_r64_imm32_effect_step (entryAddress copy + 0xa) 0x48 0xec 216
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_011 (copy : Copy) [Bindings] :
    StepEffect (LoadPre (entryAddress copy + 0x11)
      (fun s ↦ ((.base 7 .none) : AddrMode).addr s (entryAddress copy + 0x14)) 8)
      (codeRange (entryAddress copy + 0x11) (encodeMovR64M64 0 (.base 7 .none)))
      (movR64M64Effect (entryAddress copy + 0x11) 0 (.base 7 .none)) := by
  exact mov_r64_m64_effect_step (entryAddress copy + 0x11) 0x48
    (by unfold RexWPrefix; decide +kernel) 0 (.base 7 .none)
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_014 (copy : Copy) [Bindings] :
    StepEffect (StorePreReadable (entryAddress copy + 0x14)
      (storeAddrAt (entryAddress copy + 0x14) (.sib 4 none 0 (.d8 0x18)) 5) 8)
      (codeRange (entryAddress copy + 0x14) (encodeMovM64R64 0 (.sib 4 none 0 (.d8 0x18))))
      (movM64R64Effect (entryAddress copy + 0x14) 0 (.sib 4 none 0 (.d8 0x18))) := by
  exact mov_m64_r64_encoded_effect_step_of_readable (entryAddress copy + 0x14)
    0 (.sib 4 none 0 (.d8 0x18)) (by unfold AddrMode.Valid; decide +kernel)

theorem step_019 (copy : Copy) [Bindings] :
    StepEffect (LoadPre (entryAddress copy + 0x19)
      (fun s ↦ ((.base 7 (.d8 0x8)) : AddrMode).addr s (entryAddress copy + 0x1d)) 8)
      (codeRange (entryAddress copy + 0x19) (encodeMovR64M64 0 (.base 7 (.d8 0x8))))
      (movR64M64Effect (entryAddress copy + 0x19) 0 (.base 7 (.d8 0x8))) := by
  exact mov_r64_m64_effect_step (entryAddress copy + 0x19) 0x48
    (by unfold RexWPrefix; decide +kernel) 0 (.base 7 (.d8 0x8))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_01d (copy : Copy) [Bindings] :
    StepEffect (StorePreReadable (entryAddress copy + 0x1d)
      (storeAddrAt (entryAddress copy + 0x1d) (.sib 4 none 0 (.d32 0x80)) 8) 8)
      (codeRange (entryAddress copy + 0x1d) (encodeMovM64R64 0 (.sib 4 none 0 (.d32 0x80))))
      (movM64R64Effect (entryAddress copy + 0x1d) 0 (.sib 4 none 0 (.d32 0x80))) := by
  exact mov_m64_r64_encoded_effect_step_of_readable (entryAddress copy + 0x1d)
    0 (.sib 4 none 0 (.d32 0x80)) (by unfold AddrMode.Valid; decide +kernel)

theorem step_025 (copy : Copy) [Bindings] :
    StepEffect (LoadPre (entryAddress copy + 0x25)
      (fun s ↦ ((.base 7 (.d8 0x50)) : AddrMode).addr s (entryAddress copy + 0x29)) 8)
      (codeRange (entryAddress copy + 0x25) (encodeMovR64M64 0 (.base 7 (.d8 0x50))))
      (movR64M64Effect (entryAddress copy + 0x25) 0 (.base 7 (.d8 0x50))) := by
  exact mov_r64_m64_effect_step (entryAddress copy + 0x25) 0x48
    (by unfold RexWPrefix; decide +kernel) 0 (.base 7 (.d8 0x50))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_029 (copy : Copy) [Bindings] :
    StepEffect (LoadPre (entryAddress copy + 0x29)
      (fun s ↦ ((.base 7 (.d8 0x78)) : AddrMode).addr s (entryAddress copy + 0x2d)) 8)
      (codeRange (entryAddress copy + 0x29) (encodeMovR64M64 5 (.base 7 (.d8 0x78))))
      (movR64M64Effect (entryAddress copy + 0x29) 5 (.base 7 (.d8 0x78))) := by
  exact mov_r64_m64_effect_step (entryAddress copy + 0x29) 0x48
    (by unfold RexWPrefix; decide +kernel) 5 (.base 7 (.d8 0x78))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_02d (copy : Copy) [Bindings] :
    StepEffect (LoadPre (entryAddress copy + 0x2d)
      (fun s ↦ ((.base 7 (.d32 0xa0)) : AddrMode).addr s (entryAddress copy + 0x34)) 8)
      (codeRange (entryAddress copy + 0x2d) (encodeMovR64M64 1 (.base 7 (.d32 0xa0))))
      (movR64M64Effect (entryAddress copy + 0x2d) 1 (.base 7 (.d32 0xa0))) := by
  exact mov_r64_m64_effect_step (entryAddress copy + 0x2d) 0x48
    (by unfold RexWPrefix; decide +kernel) 1 (.base 7 (.d32 0xa0))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_034 (copy : Copy) [Bindings] :
    StepEffect (StorePreReadable (entryAddress copy + 0x34)
      (storeAddrAt (entryAddress copy + 0x34) (.sib 4 none 0 (.d8 0x50)) 5) 8)
      (codeRange (entryAddress copy + 0x34) (encodeMovM64R64 1 (.sib 4 none 0 (.d8 0x50))))
      (movM64R64Effect (entryAddress copy + 0x34) 1 (.sib 4 none 0 (.d8 0x50))) := by
  exact mov_m64_r64_encoded_effect_step_of_readable (entryAddress copy + 0x34)
    1 (.sib 4 none 0 (.d8 0x50)) (by unfold AddrMode.Valid; decide +kernel)

theorem step_039 (copy : Copy) [Bindings] :
    StepEffect (LoadPre (entryAddress copy + 0x39)
      (fun s ↦ ((.base 7 (.d8 0x58)) : AddrMode).addr s (entryAddress copy + 0x3d)) 8)
      (codeRange (entryAddress copy + 0x39) (encodeMovR64M64 1 (.base 7 (.d8 0x58))))
      (movR64M64Effect (entryAddress copy + 0x39) 1 (.base 7 (.d8 0x58))) := by
  exact mov_r64_m64_effect_step (entryAddress copy + 0x39) 0x48
    (by unfold RexWPrefix; decide +kernel) 1 (.base 7 (.d8 0x58))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_03d (copy : Copy) [Bindings] :
    StepEffect (StorePreReadable (entryAddress copy + 0x3d)
      (storeAddrAt (entryAddress copy + 0x3d) (.sib 4 none 0 (.d8 0x28)) 5) 8)
      (codeRange (entryAddress copy + 0x3d) (encodeMovM64R64 1 (.sib 4 none 0 (.d8 0x28))))
      (movM64R64Effect (entryAddress copy + 0x3d) 1 (.sib 4 none 0 (.d8 0x28))) := by
  exact mov_m64_r64_encoded_effect_step_of_readable (entryAddress copy + 0x3d)
    1 (.sib 4 none 0 (.d8 0x28)) (by unfold AddrMode.Valid; decide +kernel)

theorem step_042 (copy : Copy) [Bindings] :
    StepEffect (LoadPre (entryAddress copy + 0x42)
      (fun s ↦ ((.base 7 (.d32 0x80)) : AddrMode).addr s (entryAddress copy + 0x49)) 8)
      (codeRange (entryAddress copy + 0x42) (encodeMovR64M64 1 (.base 7 (.d32 0x80))))
      (movR64M64Effect (entryAddress copy + 0x42) 1 (.base 7 (.d32 0x80))) := by
  exact mov_r64_m64_effect_step (entryAddress copy + 0x42) 0x48
    (by unfold RexWPrefix; decide +kernel) 1 (.base 7 (.d32 0x80))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_049 (copy : Copy) [Bindings] :
    StepEffect (LoadPre (entryAddress copy + 0x49)
      (fun s ↦ ((.base 7 (.d32 0xa8)) : AddrMode).addr s (entryAddress copy + 0x50)) 8)
      (codeRange (entryAddress copy + 0x49) (encodeMovR64M64 2 (.base 7 (.d32 0xa8))))
      (movR64M64Effect (entryAddress copy + 0x49) 2 (.base 7 (.d32 0xa8))) := by
  exact mov_r64_m64_effect_step (entryAddress copy + 0x49) 0x48
    (by unfold RexWPrefix; decide +kernel) 2 (.base 7 (.d32 0xa8))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_050 (copy : Copy) [Bindings] :
    StepEffect (StorePreReadable (entryAddress copy + 0x50)
      (storeAddrAt (entryAddress copy + 0x50) (.sib 4 none 0 (.d8 0x60)) 5) 8)
      (codeRange (entryAddress copy + 0x50) (encodeMovM64R64 2 (.sib 4 none 0 (.d8 0x60))))
      (movM64R64Effect (entryAddress copy + 0x50) 2 (.sib 4 none 0 (.d8 0x60))) := by
  exact mov_m64_r64_encoded_effect_step_of_readable (entryAddress copy + 0x50)
    2 (.sib 4 none 0 (.d8 0x60)) (by unfold AddrMode.Valid; decide +kernel)

theorem step_055 (copy : Copy) [Bindings] :
    StepEffect (LoadPre (entryAddress copy + 0x55)
      (fun s ↦ ((.base 7 (.d8 0x60)) : AddrMode).addr s (entryAddress copy + 0x59)) 8)
      (codeRange (entryAddress copy + 0x55) (encodeMovR64M64 12 (.base 7 (.d8 0x60))))
      (movR64M64Effect (entryAddress copy + 0x55) 12 (.base 7 (.d8 0x60))) := by
  exact mov_r64_m64_effect_step (entryAddress copy + 0x55) 0x4c
    (by unfold RexWPrefix; decide +kernel) 4 (.base 7 (.d8 0x60))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_059 (copy : Copy) [Bindings] :
    StepEffect (LoadPre (entryAddress copy + 0x59)
      (fun s ↦ ((.base 7 (.d32 0x88)) : AddrMode).addr s (entryAddress copy + 0x60)) 8)
      (codeRange (entryAddress copy + 0x59) (encodeMovR64M64 15 (.base 7 (.d32 0x88))))
      (movR64M64Effect (entryAddress copy + 0x59) 15 (.base 7 (.d32 0x88))) := by
  exact mov_r64_m64_effect_step (entryAddress copy + 0x59) 0x4c
    (by unfold RexWPrefix; decide +kernel) 7 (.base 7 (.d32 0x88))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_060 (copy : Copy) [Bindings] :
    StepEffect (LoadPre (entryAddress copy + 0x60)
      (fun s ↦ ((.base 7 (.d32 0xb0)) : AddrMode).addr s (entryAddress copy + 0x67)) 8)
      (codeRange (entryAddress copy + 0x60) (encodeMovR64M64 2 (.base 7 (.d32 0xb0))))
      (movR64M64Effect (entryAddress copy + 0x60) 2 (.base 7 (.d32 0xb0))) := by
  exact mov_r64_m64_effect_step (entryAddress copy + 0x60) 0x48
    (by unfold RexWPrefix; decide +kernel) 2 (.base 7 (.d32 0xb0))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_067 (copy : Copy) [Bindings] :
    StepEffect (StorePreReadable (entryAddress copy + 0x67)
      (storeAddrAt (entryAddress copy + 0x67) (.sib 4 none 0 (.d8 0x58)) 5) 8)
      (codeRange (entryAddress copy + 0x67) (encodeMovM64R64 2 (.sib 4 none 0 (.d8 0x58))))
      (movM64R64Effect (entryAddress copy + 0x67) 2 (.sib 4 none 0 (.d8 0x58))) := by
  exact mov_m64_r64_encoded_effect_step_of_readable (entryAddress copy + 0x67)
    2 (.sib 4 none 0 (.d8 0x58)) (by unfold AddrMode.Valid; decide +kernel)

theorem step_06c (copy : Copy) [Bindings] :
    StepEffect (LoadPre (entryAddress copy + 0x6c)
      (fun s ↦ ((.base 7 (.d8 0x68)) : AddrMode).addr s (entryAddress copy + 0x70)) 8)
      (codeRange (entryAddress copy + 0x6c) (encodeMovR64M64 2 (.base 7 (.d8 0x68))))
      (movR64M64Effect (entryAddress copy + 0x6c) 2 (.base 7 (.d8 0x68))) := by
  exact mov_r64_m64_effect_step (entryAddress copy + 0x6c) 0x48
    (by unfold RexWPrefix; decide +kernel) 2 (.base 7 (.d8 0x68))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_070 (copy : Copy) [Bindings] :
    StepEffect (StorePreReadable (entryAddress copy + 0x70)
      (storeAddrAt (entryAddress copy + 0x70) (.sib 4 none 0 (.d8 0x38)) 5) 8)
      (codeRange (entryAddress copy + 0x70) (encodeMovM64R64 2 (.sib 4 none 0 (.d8 0x38))))
      (movM64R64Effect (entryAddress copy + 0x70) 2 (.sib 4 none 0 (.d8 0x38))) := by
  exact mov_m64_r64_encoded_effect_step_of_readable (entryAddress copy + 0x70)
    2 (.sib 4 none 0 (.d8 0x38)) (by unfold AddrMode.Valid; decide +kernel)

theorem step_075 (copy : Copy) [Bindings] :
    StepEffect (LoadPre (entryAddress copy + 0x75)
      (fun s ↦ ((.base 7 (.d32 0x90)) : AddrMode).addr s (entryAddress copy + 0x7c)) 8)
      (codeRange (entryAddress copy + 0x75) (encodeMovR64M64 14 (.base 7 (.d32 0x90))))
      (movR64M64Effect (entryAddress copy + 0x75) 14 (.base 7 (.d32 0x90))) := by
  exact mov_r64_m64_effect_step (entryAddress copy + 0x75) 0x4c
    (by unfold RexWPrefix; decide +kernel) 6 (.base 7 (.d32 0x90))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_07c (copy : Copy) [Bindings] :
    StepEffect (LoadPre (entryAddress copy + 0x7c)
      (fun s ↦ ((.base 7 (.d32 0xb8)) : AddrMode).addr s (entryAddress copy + 0x83)) 8)
      (codeRange (entryAddress copy + 0x7c) (encodeMovR64M64 2 (.base 7 (.d32 0xb8))))
      (movR64M64Effect (entryAddress copy + 0x7c) 2 (.base 7 (.d32 0xb8))) := by
  exact mov_r64_m64_effect_step (entryAddress copy + 0x7c) 0x48
    (by unfold RexWPrefix; decide +kernel) 2 (.base 7 (.d32 0xb8))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_083 (copy : Copy) [Bindings] :
    StepEffect (StorePreReadable (entryAddress copy + 0x83)
      (storeAddrAt (entryAddress copy + 0x83) (.sib 4 none 0 (.d8 0x68)) 5) 8)
      (codeRange (entryAddress copy + 0x83) (encodeMovM64R64 2 (.sib 4 none 0 (.d8 0x68))))
      (movM64R64Effect (entryAddress copy + 0x83) 2 (.sib 4 none 0 (.d8 0x68))) := by
  exact mov_m64_r64_encoded_effect_step_of_readable (entryAddress copy + 0x83)
    2 (.sib 4 none 0 (.d8 0x68)) (by unfold AddrMode.Valid; decide +kernel)

theorem step_088 (copy : Copy) [Bindings] :
    StepEffect (LoadPre (entryAddress copy + 0x88)
      (fun s ↦ ((.base 7 (.d8 0x70)) : AddrMode).addr s (entryAddress copy + 0x8c)) 8)
      (codeRange (entryAddress copy + 0x88) (encodeMovR64M64 13 (.base 7 (.d8 0x70))))
      (movR64M64Effect (entryAddress copy + 0x88) 13 (.base 7 (.d8 0x70))) := by
  exact mov_r64_m64_effect_step (entryAddress copy + 0x88) 0x4c
    (by unfold RexWPrefix; decide +kernel) 5 (.base 7 (.d8 0x70))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_08c (copy : Copy) [Bindings] :
    StepEffect (LoadPre (entryAddress copy + 0x8c)
      (fun s ↦ ((.base 7 (.d32 0x98)) : AddrMode).addr s (entryAddress copy + 0x93)) 8)
      (codeRange (entryAddress copy + 0x8c) (encodeMovR64M64 3 (.base 7 (.d32 0x98))))
      (movR64M64Effect (entryAddress copy + 0x8c) 3 (.base 7 (.d32 0x98))) := by
  exact mov_r64_m64_effect_step (entryAddress copy + 0x8c) 0x48
    (by unfold RexWPrefix; decide +kernel) 3 (.base 7 (.d32 0x98))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_093 (copy : Copy) [Bindings] :
    StepEffect (LoadPre (entryAddress copy + 0x93)
      (fun s ↦ ((.base 7 (.d32 0xc0)) : AddrMode).addr s (entryAddress copy + 0x9a)) 8)
      (codeRange (entryAddress copy + 0x93) (encodeMovR64M64 2 (.base 7 (.d32 0xc0))))
      (movR64M64Effect (entryAddress copy + 0x93) 2 (.base 7 (.d32 0xc0))) := by
  exact mov_r64_m64_effect_step (entryAddress copy + 0x93) 0x48
    (by unfold RexWPrefix; decide +kernel) 2 (.base 7 (.d32 0xc0))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_09a (copy : Copy) [Bindings] :
    StepEffect (StorePreReadable (entryAddress copy + 0x9a)
      (storeAddrAt (entryAddress copy + 0x9a) (.sib 4 none 0 .none) 4) 8)
      (codeRange (entryAddress copy + 0x9a) (encodeMovM64R64 2 (.sib 4 none 0 .none)))
      (movM64R64Effect (entryAddress copy + 0x9a) 2 (.sib 4 none 0 .none)) := by
  exact mov_m64_r64_encoded_effect_step_of_readable (entryAddress copy + 0x9a)
    2 (.sib 4 none 0 .none) (by unfold AddrMode.Valid; decide +kernel)

theorem step_09e (copy : Copy) [Bindings] :
    StepEffect (LoadPre (entryAddress copy + 0x9e)
      (fun s ↦ ((.base 7 (.d8 0x40)) : AddrMode).addr s (entryAddress copy + 0xa2)) 8)
      (codeRange (entryAddress copy + 0x9e) (encodeMovR64M64 11 (.base 7 (.d8 0x40))))
      (movR64M64Effect (entryAddress copy + 0x9e) 11 (.base 7 (.d8 0x40))) := by
  exact mov_r64_m64_effect_step (entryAddress copy + 0x9e) 0x4c
    (by unfold RexWPrefix; decide +kernel) 3 (.base 7 (.d8 0x40))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_0a2 (copy : Copy) [Bindings] :
    StepEffect (LoadPre (entryAddress copy + 0xa2)
      (fun s ↦ ((.base 7 (.d8 0x48)) : AddrMode).addr s (entryAddress copy + 0xa6)) 8)
      (codeRange (entryAddress copy + 0xa2) (encodeMovR64M64 2 (.base 7 (.d8 0x48))))
      (movR64M64Effect (entryAddress copy + 0xa2) 2 (.base 7 (.d8 0x48))) := by
  exact mov_r64_m64_effect_step (entryAddress copy + 0xa2) 0x48
    (by unfold RexWPrefix; decide +kernel) 2 (.base 7 (.d8 0x48))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_0a6 (copy : Copy) [Bindings] :
    StepEffect (StorePreReadable (entryAddress copy + 0xa6)
      (storeAddrAt (entryAddress copy + 0xa6) (.sib 4 none 0 (.d8 0x10)) 5) 8)
      (codeRange (entryAddress copy + 0xa6) (encodeMovM64R64 2 (.sib 4 none 0 (.d8 0x10))))
      (movM64R64Effect (entryAddress copy + 0xa6) 2 (.sib 4 none 0 (.d8 0x10))) := by
  exact mov_m64_r64_encoded_effect_step_of_readable (entryAddress copy + 0xa6)
    2 (.sib 4 none 0 (.d8 0x10)) (by unfold AddrMode.Valid; decide +kernel)

theorem step_0ab (copy : Copy) [Bindings] :
    StepEffect (LoadPre (entryAddress copy + 0xab)
      (fun s ↦ ((.base 7 (.d8 0x28)) : AddrMode).addr s (entryAddress copy + 0xaf)) 8)
      (codeRange (entryAddress copy + 0xab) (encodeMovR64M64 6 (.base 7 (.d8 0x28))))
      (movR64M64Effect (entryAddress copy + 0xab) 6 (.base 7 (.d8 0x28))) := by
  exact mov_r64_m64_effect_step (entryAddress copy + 0xab) 0x48
    (by unfold RexWPrefix; decide +kernel) 6 (.base 7 (.d8 0x28))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_0af (copy : Copy) [Bindings] :
    StepEffect (StorePreReadable (entryAddress copy + 0xaf)
      (storeAddrAt (entryAddress copy + 0xaf) (.sib 4 none 0 (.d8 0x20)) 5) 8)
      (codeRange (entryAddress copy + 0xaf) (encodeMovM64R64 6 (.sib 4 none 0 (.d8 0x20))))
      (movM64R64Effect (entryAddress copy + 0xaf) 6 (.sib 4 none 0 (.d8 0x20))) := by
  exact mov_m64_r64_encoded_effect_step_of_readable (entryAddress copy + 0xaf)
    6 (.sib 4 none 0 (.d8 0x20)) (by unfold AddrMode.Valid; decide +kernel)

theorem step_0b4 (copy : Copy) [Bindings] :
    StepEffect (LoadPre (entryAddress copy + 0xb4)
      (fun s ↦ ((.base 7 (.d8 0x30)) : AddrMode).addr s (entryAddress copy + 0xb8)) 8)
      (codeRange (entryAddress copy + 0xb4) (encodeMovR64M64 9 (.base 7 (.d8 0x30))))
      (movR64M64Effect (entryAddress copy + 0xb4) 9 (.base 7 (.d8 0x30))) := by
  exact mov_r64_m64_effect_step (entryAddress copy + 0xb4) 0x4c
    (by unfold RexWPrefix; decide +kernel) 1 (.base 7 (.d8 0x30))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_0b8 (copy : Copy) [Bindings] :
    StepEffect (LoadPre (entryAddress copy + 0xb8)
      (fun s ↦ ((.base 7 (.d8 0x10)) : AddrMode).addr s (entryAddress copy + 0xbc)) 8)
      (codeRange (entryAddress copy + 0xb8) (encodeMovR64M64 6 (.base 7 (.d8 0x10))))
      (movR64M64Effect (entryAddress copy + 0xb8) 6 (.base 7 (.d8 0x10))) := by
  exact mov_r64_m64_effect_step (entryAddress copy + 0xb8) 0x48
    (by unfold RexWPrefix; decide +kernel) 6 (.base 7 (.d8 0x10))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_0bc (copy : Copy) [Bindings] :
    StepEffect (StorePreReadable (entryAddress copy + 0xbc)
      (storeAddrAt (entryAddress copy + 0xbc) (.sib 4 none 0 (.d32 0x88)) 8) 8)
      (codeRange (entryAddress copy + 0xbc) (encodeMovM64R64 6 (.sib 4 none 0 (.d32 0x88))))
      (movM64R64Effect (entryAddress copy + 0xbc) 6 (.sib 4 none 0 (.d32 0x88))) := by
  exact mov_m64_r64_encoded_effect_step_of_readable (entryAddress copy + 0xbc)
    6 (.sib 4 none 0 (.d32 0x88)) (by unfold AddrMode.Valid; decide +kernel)

theorem step_0c4 (copy : Copy) [Bindings] :
    StepEffect (LoadPre (entryAddress copy + 0xc4)
      (fun s ↦ ((.base 7 (.d8 0x38)) : AddrMode).addr s (entryAddress copy + 0xc8)) 8)
      (codeRange (entryAddress copy + 0xc4) (encodeMovR64M64 6 (.base 7 (.d8 0x38))))
      (movR64M64Effect (entryAddress copy + 0xc4) 6 (.base 7 (.d8 0x38))) := by
  exact mov_r64_m64_effect_step (entryAddress copy + 0xc4) 0x48
    (by unfold RexWPrefix; decide +kernel) 6 (.base 7 (.d8 0x38))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_0c8 (copy : Copy) [Bindings] :
    StepEffect (StorePreReadable (entryAddress copy + 0xc8)
      (storeAddrAt (entryAddress copy + 0xc8) (.sib 4 none 0 (.d8 0x30)) 5) 8)
      (codeRange (entryAddress copy + 0xc8) (encodeMovM64R64 6 (.sib 4 none 0 (.d8 0x30))))
      (movM64R64Effect (entryAddress copy + 0xc8) 6 (.sib 4 none 0 (.d8 0x30))) := by
  exact mov_m64_r64_encoded_effect_step_of_readable (entryAddress copy + 0xc8)
    6 (.sib 4 none 0 (.d8 0x30)) (by unfold AddrMode.Valid; decide +kernel)

theorem step_0cd (copy : Copy) [Bindings] :
    StepEffect (LoadPre (entryAddress copy + 0xcd)
      (fun s ↦ ((.base 7 (.d8 0x18)) : AddrMode).addr s (entryAddress copy + 0xd1)) 8)
      (codeRange (entryAddress copy + 0xcd) (encodeMovR64M64 6 (.base 7 (.d8 0x18))))
      (movR64M64Effect (entryAddress copy + 0xcd) 6 (.base 7 (.d8 0x18))) := by
  exact mov_r64_m64_effect_step (entryAddress copy + 0xcd) 0x48
    (by unfold RexWPrefix; decide +kernel) 6 (.base 7 (.d8 0x18))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_0d1 (copy : Copy) [Bindings] :
    StepEffect (StorePreReadable (entryAddress copy + 0xd1)
      (storeAddrAt (entryAddress copy + 0xd1) (.sib 4 none 0 (.d8 0x78)) 5) 8)
      (codeRange (entryAddress copy + 0xd1) (encodeMovM64R64 6 (.sib 4 none 0 (.d8 0x78))))
      (movM64R64Effect (entryAddress copy + 0xd1) 6 (.sib 4 none 0 (.d8 0x78))) := by
  exact mov_m64_r64_encoded_effect_step_of_readable (entryAddress copy + 0xd1)
    6 (.sib 4 none 0 (.d8 0x78)) (by unfold AddrMode.Valid; decide +kernel)

theorem step_0d6 (copy : Copy) [Bindings] :
    StepEffect (StorePreReadable (entryAddress copy + 0xd6)
      (storeAddrAt (entryAddress copy + 0xd6) (.sib 4 none 0 (.d32 0xa0)) 8) 8)
      (codeRange (entryAddress copy + 0xd6) (encodeMovM64R64 7 (.sib 4 none 0 (.d32 0xa0))))
      (movM64R64Effect (entryAddress copy + 0xd6) 7 (.sib 4 none 0 (.d32 0xa0))) := by
  exact mov_m64_r64_encoded_effect_step_of_readable (entryAddress copy + 0xd6)
    7 (.sib 4 none 0 (.d32 0xa0)) (by unfold AddrMode.Valid; decide +kernel)

theorem step_0de (copy : Copy) [Bindings] :
    StepEffect (LoadPre (entryAddress copy + 0xde)
      (fun s ↦ ((.base 7 (.d8 0x20)) : AddrMode).addr s (entryAddress copy + 0xe2)) 8)
      (codeRange (entryAddress copy + 0xde) (encodeMovR64M64 6 (.base 7 (.d8 0x20))))
      (movR64M64Effect (entryAddress copy + 0xde) 6 (.base 7 (.d8 0x20))) := by
  exact mov_r64_m64_effect_step (entryAddress copy + 0xde) 0x48
    (by unfold RexWPrefix; decide +kernel) 6 (.base 7 (.d8 0x20))
    (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)

theorem step_0e2 (copy : Copy) [Bindings] :
    StepEffect (StorePreReadable (entryAddress copy + 0xe2)
      (storeAddrAt (entryAddress copy + 0xe2) (.sib 4 none 0 (.d8 0x70)) 5) 8)
      (codeRange (entryAddress copy + 0xe2) (encodeMovM64R64 6 (.sib 4 none 0 (.d8 0x70))))
      (movM64R64Effect (entryAddress copy + 0xe2) 6 (.sib 4 none 0 (.d8 0x70))) := by
  exact mov_m64_r64_encoded_effect_step_of_readable (entryAddress copy + 0xe2)
    6 (.sib 4 none 0 (.d8 0x70)) (by unfold AddrMode.Valid; decide +kernel)

theorem step_0e7 (copy : Copy) [Bindings] :
    StepEffect (fun s ↦ s.RIP = (entryAddress copy + 0xe7 : BitVec 64))
      (codeRange (entryAddress copy + 0xe7) (encodeXorR32R32 2 2))
      (xorR32R32Effect (entryAddress copy + 0xe7) 2 2 2) := by
  exact xor_r32_r32_effect_step (entryAddress copy + 0xe7) 0xd2 (by decide +kernel)

theorem step_0e9 (copy : Copy) [Bindings] :
    StepEffect (fun s ↦ s.RIP = (entryAddress copy + 0xe9 : BitVec 64))
      (codeRange (entryAddress copy + 0xe9) (encodeNopM [] (.base 0 (.d32 0))))
      (fun _ ↦ nopEffect (entryAddress copy + 0xe9) 7) := by
  exact nop_m_effect_step (entryAddress copy + 0xe9) [] (by decide +kernel) (by decide +kernel)
    (.base 0 (.d32 0)) (by unfold AddrMode.Valid; decide +kernel) rfl rfl

theorem sub_stack_writes (copy : Copy) (s : RamState) :
    (subR64Imm32Effect (entryAddress copy + 0xa) 4 216 s).writes =
      [⟨(Operand.reg 4 : Operand 64), (Operand.reg 4 : Operand 64).read s - 216⟩] := rfl

theorem zero_counter_effect (copy : Copy) (s : RamState) :
    xorR32R32Effect (entryAddress copy + 0xe7) 2 2 2 s =
      { rip := entryAddress copy + 0xe9
        writes := [⟨(Operand.reg 2 : Operand 64), 0⟩]
        flags := some (xorFlags (0 : BitVec 32)) } := by
  simp only [xorR32R32Effect, BitVec.xor_self, BitVec.add_assoc]
  rfl

end Sha3.Proofs.Permutation.Load
