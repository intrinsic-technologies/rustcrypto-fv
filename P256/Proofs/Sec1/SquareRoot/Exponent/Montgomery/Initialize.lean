import P256.Proofs.Common.Instructions.CrossPageStore.Range
import P256.Proofs.Program.Stack
import P256.Proofs.Program.Interface
import P256.Proofs.Program.Memory
import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Reduction.Common
import P256.Proofs.Common.Field.Montgomery.Schoolbook.Compose
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Not.Generated.R.Triple
import X86Proofs.Instructions.Rol.Generated.R.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Xor.Generated.RM.Triple
import X86Proofs.Instructions.Xor.Generated.MR.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Movs.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple

set_option autoImplicit false

open P256.Proofs.Program (CalleePre memoryRegion_contains_add memoryRegion_memReadable)

namespace P256.Proofs.Sec1.SquareRoot.Montgomery

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

private theorem stackPtr_read (s : RamState) :
    stackPtr s = (Operand.reg 4#5 : Operand 64).read s := rfl

attribute [local x86_compose] stackPtr_read

def initializeBytes : List UInt8 :=
  [0x4d, 0x89, 0xc6, 0x4c, 0x89, 0x44, 0x24, 0x50, 0x49, 0x89, 0xd1, 0x48, 0x89, 0x74, 0x24, 0x18, 0x48, 0x8b, 0x12, 0x48, 0x89, 0x54, 0x24, 0x48, 0x4d, 0x8b, 0x51, 0x8, 0x4c, 0x89, 0x54, 0x24, 0x10, 0x4c, 0x8b, 0x39, 0x4c, 0x89, 0x7c, 0x24, 0x20, 0x4c, 0x8b, 0x1e]

structure InitializePre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  memory : Reduction.MemoryPre s
  codeApart : RangeApart (stackPtr s) 112 p initializeBytes.length
  left : MemReadable s ((Operand.reg 6#5 : Operand 64).read s) 32
  right : MemReadable s ((Operand.reg 2#5 : Operand 64).read s) 32
  modulus : MemReadable s ((Operand.reg 1#5 : Operand 64).read s) 32
  leftApart : RangeApart (stackPtr s) 112 ((Operand.reg 6#5 : Operand 64).read s) 32
  rightApart : RangeApart (stackPtr s) 112 ((Operand.reg 2#5 : Operand 64).read s) 32
  modulusApart : RangeApart (stackPtr s) 112 ((Operand.reg 1#5 : Operand 64).read s) 32

theorem InitializePre.apart {p : BitVec 64} {s : RamState} (h : InitializePre p s)
    (offset off len : Nat) (hs : offset+8 ≤ 112) (hc : off+len ≤ initializeBytes.length) :
    RangeApart (stackPtr s+BitVec.ofNat 64 offset) 8 (p+BitVec.ofNat 64 off) len := by
  intro i hi j hj
  simpa only [BitVec.add_assoc, ← BitVec.ofNat_add] using
    h.codeApart (offset+i) (by omega) (off+j) (by omega)

theorem readable_limb {s : RamState} {a : BitVec 64} (h : MemReadable s a 32)
    (offset : Nat) (ho : offset+8 ≤ 32) : MemReadable s (a+BitVec.ofNat 64 offset) 8 := by
  refine ⟨?_, ?_⟩
  · have := h.low
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  · intro i hi
    simpa only [BitVec.add_assoc, ← BitVec.ofNat_add] using h.mem (offset+i) (by omega)

theorem scratch_load_store {a b : BitVec 64} (apart : RangeApart a 112 b 32)
    (mem : Ram) (c d v : BitVec 64) (hc : c.toNat+8 ≤ 112) (hd : d.toNat+8 ≤ 32) :
    memLoad (memStore mem (a+c) v) (b+d) 64 = memLoad mem (b+d) 64 := by
  apply P256.Proofs.Common.Field.Montgomery.Schoolbook.memLoad_memStore_rangeApart
  intro i hi j hj
  simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_assoc] using
    apart (c.toNat+i) (by omega) (d.toNat+j) (by omega)

def initializeEffect (p : BitVec 64) (s : RamState) : Effect :=
  let a0 := (Operand.mem ((Operand.reg 6#5 : Operand 64).read s) : Operand 64).read s
  let b0 := (Operand.mem ((Operand.reg 2#5 : Operand 64).read s) : Operand 64).read s
  let b1 := (Operand.mem ((Operand.reg 2#5 : Operand 64).read s+8) : Operand 64).read s
  let p0 := (Operand.mem ((Operand.reg 1#5 : Operand 64).read s) : Operand 64).read s
  { rip := p+44
    writes := [
      ⟨(Operand.reg 14#5 : Operand 64), (Operand.reg 8#5 : Operand 64).read s⟩,
      ⟨(Operand.reg 9#5 : Operand 64), (Operand.reg 2#5 : Operand 64).read s⟩,
      ⟨(Operand.reg 2#5 : Operand 64), b0⟩,
      ⟨(Operand.reg 10#5 : Operand 64), b1⟩,
      ⟨(Operand.reg 15#5 : Operand 64), p0⟩,
      ⟨(Operand.reg 11#5 : Operand 64), a0⟩,
      ⟨(Operand.mem (stackPtr s+80) : Operand 64), (Operand.reg 8#5 : Operand 64).read s⟩,
      ⟨(Operand.mem (stackPtr s+24) : Operand 64), (Operand.reg 6#5 : Operand 64).read s⟩,
      ⟨(Operand.mem (stackPtr s+72) : Operand 64), b0⟩,
      ⟨(Operand.mem (stackPtr s+16) : Operand 64), b1⟩,
      ⟨(Operand.mem (stackPtr s+32) : Operand 64), p0⟩] }

theorem initialize_correct [Bindings] (p : BitVec 64) (boundary : ReturnBoundary)
    (next : ∀ offset : Nat, 0 < offset → offset ≤ 44 →
      p+BitVec.ofNat 64 offset ≠ boundary.rip) :
    AdvanceTriple boundary (InitializePre p) (codeRange p initializeBytes)
      (Effect.post (initializeEffect p)) := by
  advance_begin (show StepEffect _ _ (movR64R64Effect p 14#5 8#5) from
    mov_r64_r64_effect_step p 0x4d 0xc6 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p initializeBytes 0 3)
  case next =>
    intro s hP
    exact next 3 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movM64R64Effect (p+3) 8#5 (.sib 4 none 0 (.d8 80))) from
    mov_m64_r64_effect_step (p+3) 0x4c (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 80)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p initializeBytes 3 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine StorePre.of_holds hH (hO true) (by x86_norm [BitVec.add_assoc]) (by x86_addr_obs) ?_ ?_
      · x86_norm
        exact hP.memory.scratch 80 8 (by decide) (by decide) (by decide)
      · x86_norm
        exact hP.apart 80 3 5 (by decide) (by decide)
    · apply Effect.avoids_codeRange
      x86_norm
      exact P256.Proofs.Common.Instructions.RangeApart.add_left (h := hP.codeApart) 80 (by decide)
    · x86_norm [BitVec.add_assoc]
      exact next 8 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movR64R64Effect (p+8) 9#5 2#5) from
    mov_r64_r64_effect_step (p+8) 0x49 0xd1 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset p initializeBytes 8 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm [BitVec.add_assoc])
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 11 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movM64R64Effect (p+11) 6#5 (.sib 4 none 0 (.d8 24))) from
    mov_m64_r64_effect_step (p+11) 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p initializeBytes 11 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine StorePre.of_holds hH (hO true) (by x86_norm [BitVec.add_assoc]) (by x86_addr_obs) ?_ ?_
      · x86_norm
        exact hP.memory.scratch 24 8 (by decide) (by decide) (by decide)
      · x86_norm
        exact hP.apart 24 11 5 (by decide) (by decide)
    · apply Effect.avoids_codeRange
      x86_norm
      exact P256.Proofs.Common.Instructions.RangeApart.add_left (h := hP.codeApart) 24 (by decide)
    · x86_norm [BitVec.add_assoc]
      exact next 16 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movR64M64Effect (p+16) 2#5 (.base 2 .none)) from
    mov_r64_m64_effect_step (p+16) 0x48 (by simp [RexWPrefix]) 2 (.base 2 .none) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p initializeBytes 16 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine LoadPre.of_holds hH (hO true) (by x86_norm [BitVec.add_assoc]) (by x86_addr_obs) ?_
      x86_norm
      simpa only [BitVec.add_zero] using readable_limb hP.right 0 (by decide)
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 19 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movM64R64Effect (p+19) 2#5 (.sib 4 none 0 (.d8 72))) from
    mov_m64_r64_effect_step (p+19) 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 72)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p initializeBytes 19 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine StorePre.of_holds hH (hO true) (by x86_norm [BitVec.add_assoc]) (by x86_addr_obs) ?_ ?_
      · x86_norm
        exact hP.memory.scratch 72 8 (by decide) (by decide) (by decide)
      · x86_norm
        exact hP.apart 72 19 5 (by decide) (by decide)
    · apply Effect.avoids_codeRange
      x86_norm
      exact P256.Proofs.Common.Instructions.RangeApart.add_left (h := hP.codeApart) 72 (by decide)
    · x86_norm [BitVec.add_assoc]
      exact next 24 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movR64M64Effect (p+24) 10#5 (.base 9 (.d8 8))) from
    mov_r64_m64_effect_step (p+24) 0x4d (by simp [RexWPrefix]) 2 (.base 9 (.d8 8)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p initializeBytes 24 4)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine LoadPre.of_holds hH (hO true) (by x86_norm [BitVec.add_assoc]) (by x86_addr_obs) ?_
      x86_norm
      simpa only [BitVec.add_zero] using readable_limb hP.right 8 (by decide)
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 28 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movM64R64Effect (p+28) 10#5 (.sib 4 none 0 (.d8 16))) from
    mov_m64_r64_effect_step (p+28) 0x4c (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p initializeBytes 28 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine StorePre.of_holds hH (hO true) (by x86_norm [BitVec.add_assoc]) (by x86_addr_obs) ?_ ?_
      · x86_norm
        exact hP.memory.scratch 16 8 (by decide) (by decide) (by decide)
      · x86_norm
        exact hP.apart 16 28 5 (by decide) (by decide)
    · apply Effect.avoids_codeRange
      x86_norm
      exact P256.Proofs.Common.Instructions.RangeApart.add_left (h := hP.codeApart) 16 (by decide)
    · x86_norm [BitVec.add_assoc]
      exact next 33 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movR64M64Effect (p+33) 15#5 (.base 1 .none)) from
    mov_r64_m64_effect_step (p+33) 0x4c (by simp [RexWPrefix]) 7 (.base 1 .none) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p initializeBytes 33 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine LoadPre.of_holds hH (hO true) (by x86_norm [BitVec.add_assoc]) (by x86_addr_obs) ?_
      x86_norm
      simpa only [BitVec.add_zero] using readable_limb hP.modulus 0 (by decide)
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 36 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movM64R64Effect (p+36) 15#5 (.sib 4 none 0 (.d8 32))) from
    mov_m64_r64_effect_step (p+36) 0x4c (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 32)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p initializeBytes 36 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine StorePre.of_holds hH (hO true) (by x86_norm [BitVec.add_assoc]) (by x86_addr_obs) ?_ ?_
      · x86_norm
        exact hP.memory.scratch 32 8 (by decide) (by decide) (by decide)
      · x86_norm
        exact hP.apart 32 36 5 (by decide) (by decide)
    · apply Effect.avoids_codeRange
      x86_norm
      exact P256.Proofs.Common.Instructions.RangeApart.add_left (h := hP.codeApart) 32 (by decide)
    · x86_norm [BitVec.add_assoc]
      exact next 41 (by decide) (by decide)
  advance_then (show StepEffect _ _ (movR64M64Effect (p+41) 11#5 (.base 6 .none)) from
    mov_r64_m64_effect_step (p+41) 0x4c (by simp [RexWPrefix]) 3 (.base 6 .none) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset p initializeBytes 41 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine LoadPre.of_holds hH (hO true) (by x86_norm [BitVec.add_assoc]) (by x86_addr_obs) ?_
      x86_norm
      simpa only [BitVec.add_zero] using readable_limb hP.left 0 (by decide)
    · x86_avoid
    · x86_norm [BitVec.add_assoc]
      exact next 44 (by decide) (by decide)
  apply AdvanceTriple.block_end
  intro s t hP hH
  have hl := hP.leftApart
  have hr := hP.rightApart
  have hm := hP.modulusApart
  x86_norm at hl hr hm
  apply hH.weaken
  · x86_norm [initializeEffect, BitVec.add_assoc]
  · simp (config := { decide := true }) (disch := decide +kernel) only
      [x86_compose, initializeEffect, scratch_load_store hl, scratch_load_store hr,
        scratch_load_store hm]
    all_goals simp only [BitVec.add_zero, and_self]
  · intro i; cases i <;> x86_norm [initializeEffect]
  · x86_norm [initializeEffect]

theorem initialize_bytes :
    Extracted.textBytes.toListFrom 0x145ee initializeBytes.length = initializeBytes := by
  decide +kernel


end P256.Proofs.Sec1.SquareRoot.Montgomery
