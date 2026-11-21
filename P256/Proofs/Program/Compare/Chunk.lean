import P256.Proofs.Program.Compare.Execution
import P256.Proofs.Program.Compare.Model
import P256.Proofs.Common.Field.Operations.Neg.Borrow.Or
namespace P256.Proofs.Program.Compare

open P256.Proofs.Common.Field.FieldNeg.Instructions (orR64R64Effect or_r64_r64_effect_step)

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Spec.Program P256.Spec.Program.Routines

def leftAddress (s : RamState) : BitVec 64 :=
  (Operand.reg 6 : Operand 64).read s + (Operand.reg 11 : Operand 64).read s

def rightAddress (s : RamState) : BitVec 64 :=
  (Operand.reg 2 : Operand 64).read s + (Operand.reg 11 : Operand 64).read s

def leftWord (s : RamState) (offset : BitVec 64) : BitVec 64 :=
  (Operand.mem (leftAddress s + offset) : Operand 64).read s

def rightWord (s : RamState) (offset : BitVec 64) : BitVec 64 :=
  (Operand.mem (rightAddress s + offset) : Operand 64).read s

structure ChunkPre (s : RamState) : Prop where
  rip : s.RIP = 0x11c890
  leftFirst : MemReadable s (leftAddress s) 8
  leftSecond : MemReadable s (leftAddress s + 8) 8
  rightFirst : MemReadable s (rightAddress s) 8
  rightSecond : MemReadable s (rightAddress s + 8) 8

def chunkDifference (s : RamState) : BitVec 64 :=
  (leftWord s 0 ^^^ rightWord s 0) ||| (leftWord s 8 ^^^ rightWord s 8)

def chunkEffect (s : RamState) : Effect :=
  { rip := 0x11c8b1
    writes := [⟨(Operand.reg 0 : Operand 64), leftWord s 0⟩,
      ⟨(Operand.reg 3 : Operand 64), leftWord s 8⟩,
      ⟨(Operand.reg 7 : Operand 64), rightWord s 0⟩,
      ⟨(Operand.reg 14 : Operand 64), rightWord s 8⟩,
      ⟨(Operand.reg 15 : Operand 64), leftWord s 8 ^^^ rightWord s 8⟩,
      ⟨(Operand.reg 12 : Operand 64), chunkDifference s⟩]
    flags := some (andFlags (chunkDifference s)) }

def chunkBytes : List UInt8 :=
  [0x4a, 0x8b, 0x04, 0x1e, 0x4a, 0x8b, 0x5c, 0x1e, 0x08,
    0x4a, 0x8b, 0x3c, 0x1a, 0x4e, 0x8b, 0x74, 0x1a, 0x08,
    0x49, 0x89, 0xdf, 0x4d, 0x31, 0xf7, 0x49, 0x89, 0xc4,
    0x49, 0x31, 0xfc, 0x4d, 0x09, 0xfc]

private theorem orR64R64Effect_local (p : BitVec 64) (dst src : BitVec 5) :
    Effect.Local (orR64R64Effect p dst src) := by
  refine ⟨fun _ _ _ ↦ rfl, ?_, fun _ _ _ ↦ rfl, ?_, ?_⟩
  · intro s t h
    simp only [orR64R64Effect, h.read_reg]
  · intro s t h i hi
    simp only [Effect.flag, orR64R64Effect, h.read_reg]
  · intro s
    simp [orR64R64Effect, Write.Full, Operand.Full]

attribute [local x86_local] orR64R64Effect_local
attribute [local x86_compose] orR64R64Effect leftAddress rightAddress leftWord rightWord
  chunkDifference BitVec.shiftLeft_zero BitVec.add_zero

def chunkLoadEffect (s : RamState) : Effect :=
  { rip := 0x11c8a2
    writes := [⟨(Operand.reg 0 : Operand 64), leftWord s 0⟩,
      ⟨(Operand.reg 3 : Operand 64), leftWord s 8⟩,
      ⟨(Operand.reg 7 : Operand 64), rightWord s 0⟩,
      ⟨(Operand.reg 14 : Operand 64), rightWord s 8⟩] }

attribute [local x86_compose] chunkLoadEffect

set_option maxRecDepth 2048 in
theorem chunk_load [Bindings] : RegisterBlock ChunkPre (codeRange 0x11c890 chunkBytes)
    chunkLoadEffect := by
  unfold chunkBytes
  p256_memcmp_run_begin mov_r64_m64_effect_step 0x11c890 0x4a
    (by unfold RexWPrefix; decide) 0 (.sib 6 (some 11) 0 .none)
    (by decide) (by decide) (by decide)
  case pre =>
    intro s hP
    refine ⟨hP.rip, ?_⟩
    x86_norm
    exact hP.leftFirst
  p256_memcmp_run_then mov_r64_m64_effect_step 0x11c894 0x4a
    (by unfold RexWPrefix; decide) 3 (.sib 6 (some 11) 0 (.d8 8))
    (by decide) (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x11c890) (all := chunkBytes) 4 (by decide +kernel)
  try (case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
    · x86_norm
      simpa only [leftAddress, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using hP.leftSecond
    · x86_avoid)
  p256_memcmp_run_then mov_r64_m64_effect_step 0x11c899 0x4a
    (by unfold RexWPrefix; decide) 7 (.sib 2 (some 11) 0 .none)
    (by decide) (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x11c890) (all := chunkBytes) 9 (by decide +kernel)
  try (case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
    · x86_norm
      exact hP.rightFirst
    · x86_avoid)
  p256_memcmp_run_then mov_r64_m64_effect_step 0x11c89d 0x4e
    (by unfold RexWPrefix; decide) 6 (.sib 2 (some 11) 0 (.d8 8))
    (by decide) (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x11c890) (all := chunkBytes) 13 (by decide +kernel)
  try (case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
    · x86_norm
      simpa only [rightAddress, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using hP.rightSecond
    · x86_avoid)
  p256_memcmp_run_finish [chunkLoadEffect]

set_option maxRecDepth 2048 in
theorem chunk_compare [Bindings] : RegisterBlock ChunkPre (codeRange 0x11c890 chunkBytes)
    chunkEffect := by
  suffices continuation : RegisterBlock ChunkPre (codeRange 0x11c890 chunkBytes) chunkLoadEffect →
      RegisterBlock ChunkPre (codeRange 0x11c890 chunkBytes) chunkEffect from continuation chunk_load
  unfold chunkBytes
  p256_memcmp_run_then mov_r64_r64_effect_step 0x11c8a2 0x49 0xdf
    (by unfold RexWPrefix; decide) (by decide)
  try (case mid => intro s t hP hH hO; refine ⟨?_, ?_⟩; · exact hH.rip_of (by x86_norm [chunkLoadEffect]); · x86_avoid)
  case sub => exact codeRange_mem_of_drop (p := 0x11c890) (all := chunkBytes) 18 (by decide +kernel)
  p256_memcmp_run_then xor_r64_r64_effect_step 0x11c8a5 0x4d 0xf7
    (by unfold RexWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x11c890) (all := chunkBytes) 21 (by decide +kernel)
  p256_memcmp_run_then mov_r64_r64_effect_step 0x11c8a8 0x49 0xc4
    (by unfold RexWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x11c890) (all := chunkBytes) 24 (by decide +kernel)
  p256_memcmp_run_then xor_r64_r64_effect_step 0x11c8ab 0x49 0xfc
    (by unfold RexWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x11c890) (all := chunkBytes) 27 (by decide +kernel)
  p256_memcmp_run_then or_r64_r64_effect_step 0x11c8ae 0x4d 0xfc
    (by unfold RexWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x11c890) (all := chunkBytes) 30 (by decide +kernel)
  p256_memcmp_run_finish [chunkEffect, chunkLoadEffect]

theorem chunkDifference_zero_iff (s : RamState) :
    chunkDifference s = 0 ↔ BytesEqual s (leftAddress s) (rightAddress s) 16 := by
  rw [show 16 = 8 + 8 from rfl, bytesEqual_append]
  have hfirst := bytesEqual_iff_load (s := s) (left := leftAddress s)
    (right := rightAddress s) (width := 64)
  have hsecond := bytesEqual_iff_load (s := s) (left := leftAddress s + 8)
    (right := rightAddress s + 8) (width := 64)
  simp only [chunkDifference, BitVec.ofNat_eq_ofNat]
  rw [BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff, BitVec.xor_eq_zero_iff]
  simpa only [leftWord, rightWord, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using (and_congr hfirst hsecond).symm

end P256.Proofs.Program.Compare
