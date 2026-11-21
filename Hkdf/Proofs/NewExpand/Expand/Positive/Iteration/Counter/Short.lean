import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Counter.Store
import Hkdf.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.Inc.Generated.R.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Mov.Generated.M8R8.Triple
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Expand.Counter

open Hkdf.Spec.Program Hkdf.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Field Hkdf.Proofs.Common.Machine

private def shortBytes : List UInt8 :=
  [0xff,0xc0,0x4c,0x89,0xe3,0x4c,0x8d,0xb4,0x24,0x10,1,0,0]

private def shortEffect (s : RamState) : Effect :=
  { rip := 0x10f934
    writes := [⟨(.reg 0 : Operand 64), (((s.regValue .rax).setWidth 32) + 1).setWidth 64⟩,
      ⟨(.reg 3 : Operand 64), s.regValue .r12⟩,
      ⟨(.reg 14 : Operand 64), stackPtr s + 272⟩]
    flags := some (.ofStatusFlags (incSpec (StatusFlags.ofRFLAGS s.RFLAGS) ((s.regValue .rax).setWidth 32)).2) }

private theorem short_run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s ↦ s.RIP = 0x10f927)
      (codeRange 0x10f927 shortBytes) (Effect.post shortEffect) := by
  advance_begin (inc_r32_effect_step 0x10f927 0xc0 rfl rfl)
  case next => exact fun _ _ ↦ boundary_ne_program outside (inProgram_of_textOffset 0xf929 (by decide))
  advance_then (mov_r64_r64_effect_step 0x10f929 0x4c 0xe3 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10f927 shortBytes 2 3
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0xf92c (by decide))⟩
  advance_then (lea_r64_effect_step 0x10f92c 0x4c (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d32 272)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10f927 shortBytes 5 8
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0xf934 (by decide))⟩
  advance_finish [shortEffect, incR32Effect]

theorem short [Bindings] {entry s : RamState} {length tail : Nat} {b : UInt8}
    {boundary : ReturnBoundary} (ctx : StackContext entry boundary length)
    (running : RunningFrame entry boundary length s) (sp : stackPtr s = base entry)
    (pc : s.RIP = 0x10f920) (tailBound : tail < 63)
    (ax : s.regValue .rax = BitVec.ofNat 64 tail) (cl : (s.regValue .rcx).setWidth 8 = b.toBitVec) :
    ∃ t, RunningFrame entry boundary length t ∧ stackPtr t = base entry ∧ t.RIP = 0x10f934 ∧
      t.regValue .rax = BitVec.ofNat 64 (tail + 1) ∧
      t.regValue .rbx = s.regValue .r12 ∧ t.regValue .r14 = base entry + 272 ∧
      t.external[base entry + BitVec.ofNat 64 (272 + tail)]? = some b ∧
      AgreesExcept [.reg 0, .reg 3, .reg 14, .flags, .mem (base entry + BitVec.ofNat 64 (272 + tail)) 1, .rip] s t := by
  have step := mov_m8_r8_effect_step 0x10f920 1 (by decide) (.sib 4 (some 0) 0 (.d32 272))
    (by decide) rfl rfl
  have code := programText_slice (programLoaded_codeIn running.loaded) 0xf920
    [0x88,0x8c,0x04,0x10,1,0,0] (by decide) (by decide +kernel)
  obtain ⟨u, ru, readyU, pcU, write, frameU⟩ := store_stack ctx running
    (codeOff := 0xf920) (codeSize := 7) (width := 8) (off := 272 + tail) pc
    (by change stackPtr s + (s.regValue .rax <<< 0) + 272 = _
        rw [BitVec.shiftLeft_zero, sp, ax, BitVec.ofNat_add]
        bv_omega)
    (by omega) (by decide) (write_byte ctx running (by omega)) step code
  have spU : stackPtr u = base entry := (frameU.read (n := 64) (r := 4) (by simp)).trans sp
  have val : memLoad u.external (base entry + BitVec.ofNat 64 (272 + tail)) 8 = b.toBitVec :=
    write.trans cl
  have byte := byte_of_load (read_stack ctx ru (off := 272 + tail) (by omega) (by omega)) val
  obtain ⟨fuel, t, runT, readyT, _, effect⟩ := short_run boundary ctx.outside u readyU
    (programText_slice (programLoaded_codeIn ru.loaded) 0xf927 shortBytes (by decide) (by decide +kernel)) pcU
  have frameT : AgreesExcept [.reg 0, .reg 3, .reg 14, .flags, .rip] u t := effect.agrees
  have values := effect.writes
  change t.regValue .rax = (((u.regValue .rax).setWidth 32) + 1).setWidth 64 ∧
    t.regValue .rbx = u.regValue .r12 ∧ t.regValue .r14 = stackPtr u + 272 at values
  have axT : t.regValue .rax = BitVec.ofNat 64 (tail + 1) := by
    have axU : u.regValue .rax = BitVec.ofNat 64 tail :=
      (frameU.read (n := 64) (r := 0) (by simp)).trans ax
    rw [values.1, axU]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat]
    omega
  exact ⟨t, no_memory ctx ru runT readyT frameT (by simp [Component.Covers]) (by simp),
    (frameT.read (n := 64) (r := 4) (by simp)).trans spU, effect.rip, axT,
    values.2.1.trans (frameU.read (n := 64) (r := 12) (by simp)),
    values.2.2.trans (by rw [spU]), (frameT.byte (by simp [Component.Covers])).trans byte,
    (frameU.trans frameT).mono (by simp)⟩

end Hkdf.Proofs.NewExpand.Expand.Counter
