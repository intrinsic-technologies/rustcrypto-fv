import Hkdf.Proofs.Common.Field.Operations.Run.Compose
import Hkdf.Proofs.Common.Instructions.ByteStore
import Hkdf.Proofs.Common.Machine.Code
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Program.ReadWrite.Bytes

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Expand.Info

open Hkdf.Spec.Program Hkdf.Proofs.Program Hkdf.Proofs.Common
open Hkdf.Proofs.Common.Field Hkdf.Proofs.Common.Machine
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

private def residualArithmeticBytes : List UInt8 :=
  [0x4c, 0x89, 0xf8, 0x48, 0xb9, 0xc0, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f,
   0x48, 0x21, 0xc8, 0x41, 0x83, 0xe7, 0x3f, 0x48, 0x01, 0xc3]

private def residualArithmeticEffect (s : RamState) : Effect :=
  let full := (Operand.reg 15 : Operand 64).read s &&& 0x7fffffffffffffc0
  { rip := 0x10f7c5
    writes := [⟨(.reg 0 : Operand 64), full⟩,
      ⟨(.reg 1 : Operand 64), 0x7fffffffffffffc0⟩,
      ⟨(.reg 15 : Operand 64), ((Operand.reg 15 : Operand 32).read s &&& 63).setWidth 64⟩,
      ⟨(.reg 3 : Operand 64), (Operand.reg 3 : Operand 64).read s + full⟩]
    flags := some (.ofStatusFlags (addSpec ((Operand.reg 3 : Operand 64).read s) full).2) }

private theorem residualArithmetic [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s ↦ s.RIP = 0x10f7ae)
      (codeRange 0x10f7ae residualArithmeticBytes) (Effect.post residualArithmeticEffect) := by
  advance_begin (show StepEffect (fun s ↦ s.RIP = 0x10f7ae)
    (codeRange 0x10f7ae [0x4c, 0x89, 0xf8]) (movR64R64Effect 0x10f7ae 0 15) from
    mov_r64_r64_effect_step 0x10f7ae 0x4c 0xf8 (by simp [RexWPrefix]) rfl)
  case next => exact fun _ _ ↦ boundary_ne_program outside (inProgram_of_textOffset 0xf7b1 (by decide))
  advance_then (show StepEffect (fun s ↦ s.RIP = 0x10f7b1)
    (codeRange 0x10f7b1 [0x48, 0xb9, 0xc0, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f])
    (movR64Imm64Effect 0x10f7b1 1 0x7fffffffffffffc0) from
    mov_r64_imm64_effect_step 0x10f7b1 0x48 0xb9 (by simp [RexWPrefix]) (by decide)
      0x7fffffffffffffc0)
  case sub => exact codeRange_slice_subset 0x10f7ae residualArithmeticBytes 3 10
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0xf7bb (by decide))⟩
  advance_then (show StepEffect (fun s ↦ s.RIP = 0x10f7bb)
    (codeRange 0x10f7bb [0x48, 0x21, 0xc8]) (andR64R64Effect 0x10f7bb 0 1) from
    and_r64_r64_effect_step 0x10f7bb 0x48 0xc8 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10f7ae residualArithmeticBytes 13 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0xf7be (by decide))⟩
  advance_then (show StepEffect (fun s ↦ s.RIP = 0x10f7be)
    (codeRange 0x10f7be [0x41, 0x83, 0xe7, 0x3f]) (andR32Imm8Effect 0x10f7be 4 15 63) from
    and_r32_imm8_rex_effect_step 0x10f7be 0x41 0xe7 63 (by simp [RexNoWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10f7ae residualArithmeticBytes 16 4
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0xf7c2 (by decide))⟩
  advance_then (show StepEffect (fun s ↦ s.RIP = 0x10f7c2)
    (codeRange 0x10f7c2 [0x48, 0x01, 0xc3]) (addR64R64Effect 0x10f7c2 3 0) from
    add_r64_r64_effect_step 0x10f7c2 0x48 0xc3 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10f7ae residualArithmeticBytes 20 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0xf7c5 (by decide))⟩
  advance_finish [residualArithmeticEffect]

private def residualCopyBytes : List UInt8 :=
  [0x48, 0x8d, 0xbc, 0x24, 0x10, 1, 0, 0, 0x48, 0x89, 0xde, 0x4c, 0x89, 0xfa]

private def residualCopyEffect (s : RamState) : Effect :=
  { rip := 0x10f7db
    writes := [⟨(.reg 7 : Operand 64), rspOf s + 272⟩,
      ⟨(.reg 6 : Operand 64), s.regValue .rbx⟩,
      ⟨(.reg 2 : Operand 64), s.regValue .r15⟩] }

private theorem residualCopy [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s ↦ s.RIP = 0x10f7cd)
      (codeRange 0x10f7cd residualCopyBytes) (Effect.post residualCopyEffect) := by
  advance_begin (lea_r64_effect_step 0x10f7cd 0x48 (by simp [RexWPrefix]) 7
    (.sib 4 none 0 (.d32 272)) (by decide) rfl rfl)
  case next => exact fun _ _ ↦ boundary_ne_program outside (inProgram_of_textOffset 0xf7d5 (by decide))
  advance_then (mov_r64_r64_effect_step 0x10f7d5 0x48 0xde (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10f7cd residualCopyBytes 8 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0xf7d8 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10f7d8 0x4c 0xfa (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10f7cd residualCopyBytes 11 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0xf7db (by decide))⟩
  advance_finish [residualCopyEffect, BitVec.shiftLeft_zero, BitVec.add_zero]

private theorem residualFullLength (n : BitVec 64) (low : n.toNat < 2 ^ 32) :
    n &&& 0x7fffffffffffffc0 = BitVec.ofNat 64 (64 * (n.toNat / 64)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, Nat.and_comm]
  have div := Nat.and_div_two_pow (a := 0x7fffffffffffffc0) (b := n.toNat) (n := 6)
  change (0x7fffffffffffffc0 &&& n.toNat) / 64 = (2^57-1) &&& (n.toNat / 64) at div
  rw [Nat.and_comm (2^57-1) (n.toNat / 64), Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_eq_of_lt (by omega)] at div
  have rem := Nat.and_mod_two_pow (a := 0x7fffffffffffffc0) (b := n.toNat) (n := 6)
  change (0x7fffffffffffffc0 &&& n.toNat) % 64 = 0 &&& (n.toNat % 64) at rem
  rw [Nat.zero_and] at rem
  change (0x7fffffffffffffc0 &&& n.toNat) = (64 * (n.toNat / 64)) % 2^64
  omega

private theorem residualTailLength (n : BitVec 64) :
    (n.setWidth 32 &&& 63).setWidth 64 = BitVec.ofNat 64 (n.toNat % 64) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth_of_le (by decide), BitVec.toNat_and]
  change (n.setWidth 32).toNat &&& (2^6-1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.mod_mod_of_dvd _ (show 64 ∣ 2^32 by decide)]
  have := Nat.mod_lt n.toNat (by decide : 0 < 64)
  omega

theorem residualArguments [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (outside : ¬ InProgram boundary.rip)
    (pc : s.RIP = 0x10f7ae) (writable : MemWritable s (rspOf s + 335) 1)
    (apart : RangeApart (rspOf s + 335) 1 0x10f7c5 22)
    (low : (s.regValue .r15).toNat < 2 ^ 32) :
    let n := (s.regValue .r15).toNat
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ t.RIP = 0x10f7db ∧
      t.regValue .rdi = rspOf s + 272 ∧
      t.regValue .rsi = s.regValue .rbx + BitVec.ofNat 64 (64 * (n / 64)) ∧
      t.regValue .rdx = BitVec.ofNat 64 (n % 64) ∧
      t.regValue .rbx = t.regValue .rsi ∧ t.regValue .r15 = t.regValue .rdx ∧
      t.regValue .rax = BitVec.ofNat 64 (64 * (n / 64)) ∧
      t.regValue .rcx = 0x7fffffffffffffc0 ∧
      t.external[rspOf s + 335]? = some (UInt8.ofNat (n % 64)) ∧
      (t.regValue .rax).toNat = 64 * (n / 64) ∧ (t.regValue .rdx).toNat = n % 64 ∧
      AgreesExcept [.reg 0, .reg 1, .reg 2, .reg 3, .reg 6, .reg 7, .reg 15,
        .mem (rspOf s + 335) 1, .flags, .rip] s t := by
  dsimp only
  have arithmeticCode := programText_slice (programLoaded_codeIn loaded) 0xf7ae
    residualArithmeticBytes (by decide) (by decide +kernel)
  obtain ⟨fuelU, u, runU, readyU, _, arithmetic⟩ := residualArithmetic boundary outside s ready arithmeticCode pc
  have agU : AgreesExcept [.reg 0, .reg 1, .reg 15, .reg 3, .flags, .rip] s u := arithmetic.agrees
  have spU : rspOf u = rspOf s := agU.read (by decide)
  have extU := agU.external (by simp [Component.Covers])
  have codeStore := programText_slice (programLoaded_codeIn loaded) 0xf7c5
    [0x44, 0x88, 0xbc, 0x24, 0x4f, 1, 0, 0] (by decide) (by decide +kernel)
  have store : StepEffect (StorePre 0x10f7c5 8 (fun u ↦ rspOf u + 335) 1)
      (codeRange 0x10f7c5 [0x44, 0x88, 0xbc, 0x24, 0x4f, 1, 0, 0])
      (storeEffect 0x10f7c5 8 (fun u ↦ rspOf u + 335)
        (fun u ↦ (Operand.reg 15 : Operand 8).read u)) :=
    Instructions.mov_m8_r8_effect_step 0x10f7c5 0x44 (by simp [RexPrefix])
      7 (.sib 4 none 0 (.d32 335)) (by decide) rfl rfl
  have wU : MemWritable u (rspOf u + 335) 1 := by
    rw [spU]
    exact writable.of_external_eq extU
  obtain ⟨v, runV, readyV, save⟩ := store.advances readyU (codeStore.of_external_eq extU)
    ⟨arithmetic.rip, wU, by rw [spU]; exact apart.sub0 8 (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0xf7cd (by decide)))
  have agV : AgreesExcept [.mem (rspOf s + 335) 1, .rip] u v := by
    simpa only [storeEffect_components, Nat.reduceDiv, spU] using save.agrees
  have spV : rspOf v = rspOf s := (agV.read (by simp)).trans spU
  have codeCopy := programText_slice (programLoaded_codeIn loaded) 0xf7cd
    residualCopyBytes (by decide) (by decide +kernel)
  have codeV : CodeIn (codeRange 0x10f7cd residualCopyBytes) v := by
    apply save.codeIn _ (codeCopy.of_external_eq extU)
    apply Effect.avoids_codeRange
    intro c hc a len eq
    simp only [storeEffect_components, Nat.reduceDiv, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · cases eq
      rw [spU]
      exact apart.sub 8 14 (by decide)
    · cases eq
  obtain ⟨fuelT, t, runT, readyT, _, copy⟩ := residualCopy boundary outside v readyV codeV save.rip
  have agT : AgreesExcept [.reg 7, .reg 6, .reg 2, .rip] v t := copy.agrees
  have kept := agV.trans agT
  have full := residualFullLength (s.regValue .r15) low
  have tail := residualTailLength (s.regValue .r15)
  obtain ⟨ax, cx, r15, bx⟩ := arithmetic.writes
  have r15Nat : u.regValue .r15 = BitVec.ofNat 64 ((s.regValue .r15).toNat % 64) := r15.trans tail
  have bxNat : u.regValue .rbx = s.regValue .rbx +
      BitVec.ofNat 64 (64 * ((s.regValue .r15).toNat / 64)) :=
    bx.trans (congrArg (s.regValue .rbx + ·) full)
  have argRdi : t.regValue .rdi = rspOf s + 272 :=
    (show t.regValue .rdi = rspOf v + 272 from copy.writes.1).trans (congrArg (· + 272) spV)
  have argRsi : t.regValue .rsi = u.regValue .rbx :=
    (show t.regValue .rsi = v.regValue .rbx from copy.writes.2.1).trans (agV.read (n := 64) (r := 3) (by simp))
  have argRdx : t.regValue .rdx = u.regValue .r15 :=
    (show t.regValue .rdx = v.regValue .r15 from copy.writes.2.2).trans (agV.read (n := 64) (r := 15) (by simp))
  have byte : memLoad v.external (rspOf s + 335) 8 =
      BitVec.ofNat 8 ((s.regValue .r15).toNat % 64) := by
    rw [← spU]
    have stored : memLoad v.external (rspOf u + 335) 8 = (Operand.reg 15 : Operand 8).read u :=
      save.writes
    rw [stored]
    change (u.regValue .r15).setWidth 8 = _
    rw [r15Nat, BitVec.setWidth_ofNat_of_le (by decide)]
  have present : ∀ i < 1, (v.external[rspOf s + 335 + BitVec.ofNat 64 i]?).isSome :=
    fun i hi ↦ agV.grow _ (agU.grow _ (writable.mem i hi))
  have storedByteEq := Bytes.of_memLoad (n := 8) present 0 (by decide)
  rw [byte] at storedByteEq
  have axT : t.regValue .rax = BitVec.ofNat 64 (64 * ((s.regValue .r15).toNat / 64)) :=
    (kept.read (n := 64) (r := 0) (by simp)).trans (ax.trans full)
  have dxT := argRdx.trans r15Nat
  have remainderBound := Nat.mod_lt (s.regValue .r15).toNat (by decide : 0 < 64)
  have byteBound : (s.regValue .r15).toNat % 64 < 2^8 := by omega
  have extT := agT.external (by simp [Component.Covers])
  refine ⟨fuelU + 1 + fuelT, t, (runU.trans runV).trans runT, readyT, copy.rip,
    argRdi, argRsi.trans bxNat, dxT, ?_, ?_, axT, ?_, ?_, ?_, ?_, ?_⟩
  · exact (kept.read (n := 64) (r := 3) (by simp)).trans argRsi.symm
  · exact (kept.read (n := 64) (r := 15) (by simp)).trans argRdx.symm
  · exact (kept.read (n := 64) (r := 1) (by simp)).trans cx
  · rw [extT]
    simpa only [storedByte, BitVec.toNat_ofNat, Nat.mul_zero, Nat.shiftRight_zero,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.mod_eq_of_lt byteBound] using
      storedByteEq
  · rw [axT, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    omega
  · rw [dxT, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    omega
  · exact (agU.trans kept).mono (by simp)

end Hkdf.Proofs.NewExpand.Expand.Info
