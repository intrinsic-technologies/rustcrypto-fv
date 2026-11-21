import P256.Proofs.Program.Compare.Execution
import P256.Proofs.Program.Compare.Model

namespace P256.Proofs.Program.Compare.Tail

open X86 X86.Machine X86.UserProcess X86Proofs

private theorem cmp32_local (p : BitVec 64) (len : Nat) (dst src : BitVec 5) :
    Effect.Local (cmpR32R32Effect p len dst src) := by
  refine ⟨fun _ _ _ ↦ rfl, fun _ _ _ ↦ rfl, fun _ _ _ ↦ rfl,
    fun s t h i _ ↦ ?_, fun _ ↦ by simp [cmpR32R32Effect]⟩
  simp only [cmpR32R32Effect, Effect.flag, h.read_reg]

attribute [local x86_local] cmp32_local
attribute [local x86_compose] cmpR32R32Effect BitVec.shiftLeft_zero BitVec.add_zero

def eightLeft (s : RamState) : BitVec 64 :=
  (Operand.reg 6 : Operand 64).read s + (Operand.reg 11 : Operand 64).read s

def eightRight (s : RamState) : BitVec 64 :=
  (Operand.reg 2 : Operand 64).read s + (Operand.reg 11 : Operand 64).read s

structure EightComparePre (s : RamState) : Prop where
  rip : s.RIP = 0x11cd50
  left : MemReadable s (eightLeft s) 8
  right : MemReadable s (eightRight s) 8

def eightCompareBytes : List UInt8 :=
  [0x4a, 0x8b, 0x4, 0x1e, 0x4a, 0x8b, 0x3c, 0x1a, 0x48, 0x39, 0xf8]

def eightCompareEffect (s : RamState) : Effect :=
  { rip := 0x11cd5b
    writes := [⟨(Operand.reg 0 : Operand 64),
      ((Operand.mem (eightLeft s) : Operand 64).read s).setWidth 64⟩,
      ⟨(Operand.reg 7 : Operand 64),
      ((Operand.mem (eightRight s) : Operand 64).read s).setWidth 64⟩]
    flags := some (.ofStatusFlags (cmpSpec
      ((Operand.mem (eightLeft s) : Operand 64).read s)
      ((Operand.mem (eightRight s) : Operand 64).read s))) }

attribute [local x86_compose] eightLeft eightRight

set_option maxRecDepth 2048 in
theorem eight_compare [Bindings] :
    RegisterBlock EightComparePre (codeRange 0x11cd50 eightCompareBytes)
      eightCompareEffect := by
  unfold eightCompareBytes
  p256_memcmp_run_begin mov_r64_m64_effect_step 0x11cd50 0x4a
    (by unfold RexWPrefix; decide) 0 (.sib 6 (some 11) 0 .none)
    (by decide) (by decide) (by decide)
  case pre =>
    intro s hP
    refine ⟨hP.rip, ?_⟩
    x86_norm
    exact hP.left
  p256_memcmp_run_then mov_r64_m64_effect_step 0x11cd54 0x4a
    (by unfold RexWPrefix; decide) 7 (.sib 2 (some 11) 0 .none)
    (by decide) (by decide) (by decide)
  case sub =>
    exact codeRange_mem_of_drop (p := 0x11cd50) (all := eightCompareBytes) 4
      (by decide +kernel)
  try (case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
    · x86_norm
      exact hP.right
    · x86_avoid)
  p256_memcmp_run_then cmp_r64_r64_effect_step 0x11cd58 0x48 0xf8
    (by unfold RexWPrefix; decide) (by decide)
  case sub =>
    exact codeRange_mem_of_drop (p := 0x11cd50) (all := eightCompareBytes) 8
      (by decide +kernel)
  p256_memcmp_run_finish [eightCompareEffect]

theorem eight_compare_zero_iff [Bindings] {s t : RamState}
    (h : (eightCompareEffect s).Holds s t) :
    (StatusFlags.ofRFLAGS t.RFLAGS).ZF = true ↔
      BytesEqual s (eightLeft s) (eightRight s) 8 := by
  have hz := h.flags.2.2.2.1
  change (StatusFlags.ofRFLAGS t.RFLAGS).ZF =
    (((Operand.mem (eightLeft s) : Operand 64).read s -
      (Operand.mem (eightRight s) : Operand 64).read s) == 0) at hz
  rw [hz, beq_iff_eq, BitVec.sub_eq_iff_eq_add]
  simpa using bytesEqual_iff_load.symm

def fourLeft (s : RamState) : BitVec 64 :=
  (Operand.reg 8 : Operand 64).read s + (Operand.reg 11 : Operand 64).read s

def fourRight (s : RamState) : BitVec 64 :=
  (Operand.reg 2 : Operand 64).read s + (Operand.reg 11 : Operand 64).read s

structure FourComparePre (s : RamState) : Prop where
  rip : s.RIP = 0x11cd90
  left : MemReadable s (fourLeft s) 4
  right : MemReadable s (fourRight s) 4

def fourCompareBytes : List UInt8 :=
  [0x43, 0x8b, 0x34, 0x18, 0x42, 0x8b, 0x3c, 0x1a, 0x39, 0xfe]

def fourCompareEffect (s : RamState) : Effect :=
  { rip := 0x11cd9a
    writes := [⟨(Operand.reg 6 : Operand 64),
      ((Operand.mem (fourLeft s) : Operand 32).read s).setWidth 64⟩,
      ⟨(Operand.reg 7 : Operand 64),
      ((Operand.mem (fourRight s) : Operand 32).read s).setWidth 64⟩]
    flags := some (.ofStatusFlags (cmpSpec
      ((Operand.mem (fourLeft s) : Operand 32).read s)
      ((Operand.mem (fourRight s) : Operand 32).read s))) }

attribute [local x86_compose] fourLeft fourRight

set_option maxRecDepth 2048 in
theorem four_compare [Bindings] :
    RegisterBlock FourComparePre (codeRange 0x11cd90 fourCompareBytes)
      fourCompareEffect := by
  unfold fourCompareBytes
  p256_memcmp_run_begin mov_r32_m32_effect_step 0x11cd90 0x43
    (by unfold RexNoWPrefix; decide) 6 (.sib 8 (some 11) 0 .none)
    (by decide) (by decide) (by decide)
  case pre =>
    intro s hP
    refine ⟨hP.rip, ?_⟩
    x86_norm
    exact hP.left
  p256_memcmp_run_then mov_r32_m32_effect_step 0x11cd94 0x42
    (by unfold RexNoWPrefix; decide) 7 (.sib 2 (some 11) 0 .none)
    (by decide) (by decide) (by decide)
  case sub =>
    exact codeRange_mem_of_drop (p := 0x11cd90) (all := fourCompareBytes) 4
      (by decide +kernel)
  try (case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
    · x86_norm
      exact hP.right
    · x86_avoid)
  p256_memcmp_run_then cmp_r32_r32_effect_step 0x11cd98 0xfe
    (by decide)
  case sub =>
    exact codeRange_mem_of_drop (p := 0x11cd90) (all := fourCompareBytes) 8
      (by decide +kernel)
  p256_memcmp_run_finish [fourCompareEffect, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]

theorem four_compare_zero_iff [Bindings] {s t : RamState}
    (h : (fourCompareEffect s).Holds s t) :
    (StatusFlags.ofRFLAGS t.RFLAGS).ZF = true ↔
      BytesEqual s (fourLeft s) (fourRight s) 4 := by
  have hz := h.flags.2.2.2.1
  change (StatusFlags.ofRFLAGS t.RFLAGS).ZF =
    (((Operand.mem (fourLeft s) : Operand 32).read s -
      (Operand.mem (fourRight s) : Operand 32).read s) == 0) at hz
  rw [hz, beq_iff_eq, BitVec.sub_eq_iff_eq_add]
  simpa using bytesEqual_iff_load.symm

end P256.Proofs.Program.Compare.Tail
