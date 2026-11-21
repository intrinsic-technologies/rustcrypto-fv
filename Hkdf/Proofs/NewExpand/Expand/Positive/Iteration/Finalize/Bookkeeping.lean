import Hkdf.Proofs.NewExpand.Expand.Frame
import Hkdf.Proofs.Common.CallFrame.Stack
import Hkdf.Proofs.Common.EffectCompose.Advance
import X86Proofs.Instructions.Inc.Generated.M.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Expand.Finalize

open Hkdf.Spec.Program Hkdf.Proofs.Common Hkdf.Proofs.Common.Machine Hkdf.Proofs.Common.CallFrame
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Field (AdvanceTriple)

private def pointerBytes : List UInt8 :=
  [0x4c,0x8b,0xb4,0x24,0xb0,1,0,0,0x48,0x8b,0x9c,0x24,8,1,0,0,0x49,0x8d,0x2c,0x1e]

private def pointerEffect (s : RamState) : Effect :=
  { rip := 0x10f334
    writes := [⟨(.reg 14 : Operand 64), (.mem (rspOf s + 432) : Operand 64).read s⟩, ⟨(.reg 3 : Operand 64), (.mem (rspOf s + 264) : Operand 64).read s⟩,
      ⟨(.reg 5 : Operand 64), (.mem (rspOf s + 432) : Operand 64).read s + (.mem (rspOf s + 264) : Operand 64).read s⟩] }

private theorem pointers [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s ↦ s.RIP = 0x10f320 ∧ MemReadable s (rspOf s + 432) 8 ∧
      MemReadable s (rspOf s + 264) 8) (codeRange 0x10f320 pointerBytes) (Effect.post pointerEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x10f320 0x4c (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d32 432)) (by decide) rfl rfl)
  case pre => exact fun _ h => ⟨h.1, h.2.1⟩
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0xf328 (by decide))
  advance_then (mov_r64_m64_effect_step 0x10f328 0x48 (by simp [RexWPrefix]) 3
    (.sib 4 none 0 (.d32 264)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10f320 pointerBytes 8 8
  case mid =>
    intro s t hp hh ho
    refine ⟨LoadPre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_, by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0xf330 (by decide))⟩
    x86_norm
    exact hp.2.2
  advance_then (lea_r64_effect_step 0x10f330 0x49 (by simp [RexWPrefix]) 5
    (.sib 14 (some 3) 0 .none) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10f320 pointerBytes 16 4
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by x86_norm), by x86_avoid,
      boundary_ne_program outside (inProgram_of_textOffset 0xf334 (by decide))⟩
  advance_finish [pointerEffect, BitVec.shiftLeft_zero, BitVec.add_zero]

theorem bookkeeping [Bindings] {entry s : RamState} {boundary : ReturnBoundary}
    {key info : ByteArray} {ptr : BitVec 64} {length : Nat}
    (pre : ExpandPre entry boundary key info ptr length) (frame : SavedFrame entry s boundary length)
    (pc : s.RIP = 0x10f320) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ t.RIP = 0x10f33c ∧
      t.regValue .r14 = slot s 432 ∧ t.regValue .rbx = slot s 264 ∧
      t.regValue .rbp = slot s 432 + slot s 264 ∧ slot t 256 = slot s 256 + 1 ∧
      AgreesExcept [.reg 14,.reg 3,.reg 5,.mem (stackPtr s + 256) 8,.flags,.rip] s t := by
  have sp : stackPtr s = stackPtr entry - 536 := frame.sp
  have addr (i j : Nat) (eq : i + j = 536) :
      rspOf s + BitVec.ofNat 64 i = stackPtr entry - BitVec.ofNat 64 j := by
    rw [show rspOf s = stackPtr s from Operand.read_reg64 s 4, sp]
    change stackPtr entry - BitVec.ofNat 64 536 + _ = _
    rw [← eq, BitVec.ofNat_add]
    bv_omega
  have stack := pre.call.stack
  obtain ⟨fuel,u,run,readyU,_,eff⟩ := pointers boundary pre.call.outerBoundary s
    (supportedMachine_readyToStep frame.machine)
    (programText_slice (programLoaded_codeIn frame.loaded) 0xf320 pointerBytes (by decide) (by decide +kernel))
    ⟨pc, addr 432 104 (by decide) ▸ stack_readable stack frame.allocated (offset := 104) (by decide) (by decide),
      addr 264 272 (by decide) ▸ stack_readable stack frame.allocated (offset := 272) (by decide) (by decide)⟩
  have a : AgreesExcept [.reg 14,.reg 3,.reg 5,.rip] s u := eff.agrees
  have su : rspOf u = rspOf s := a.read (r := 4) (n := 64) (by decide)
  have atCounter : rspOf u + 256 = stackPtr entry - 280 := su ▸ addr 256 280 (by decide)
  have step := inc_m64_effect_step 0x10f334 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d32 256)) (by decide) rfl rfl
  have p : RmwPre 0x10f334 (.sib 4 none 0 (.d32 256)) 8 8 u := by
    refine ⟨eff.rip, ?_, ?_⟩
    · change MemWritable u (rspOf u + 256) 8
      rw [atCounter]
      exact stack_writable8 stack pre.call.stackAvoid (fun x hx => a.grow x (frame.allocated x hx))
        (offset := 280) (by decide) (by decide)
    · change RangeApart (rspOf u + 256) 8 0x10f334 8
      rw [atCounter]
      exact stack_codeApart stack (fun x h hp => pre.call.stackAvoid x h (.inl hp))
        (offset := 280) (codeOffset := 0xf334) (by decide) (by decide) (by decide)
  obtain ⟨t,increment,readyT,h⟩ := step.advances readyU
    (programText_slice (a.codeIn (by simp [Component.Covers]) (programLoaded_codeIn frame.loaded))
      0xf334 [0x48,0xff,0x84,0x24,0,1,0,0] (by decide) (by decide +kernel))
    p (boundary_ne_program pre.call.outerBoundary (inProgram_of_textOffset 0xf33c (by decide)))
  have b : AgreesExcept [.mem (rspOf u + 256) 8,.flags,.rip] u t := by
    have keep := h.agrees
    rw [incMEffect_components] at keep
    exact keep
  have st : t.regValue .rsp = u.regValue .rsp := b.read (r := 4) (n := 64) (by simp)
  have mem : slot u 256 = slot s 256 := by
    change memLoad u.external (rspOf u + 256) 64 = memLoad s.external (rspOf s + 256) 64
    rw [su]
    apply agrees_memLoad
    intro i hi
    exact a.byte (by simp [Component.Covers])
  refine ⟨_,t,run.trans increment,readyT,h.rip,
    (b.read (r := 14) (n := 64) (by simp)).trans eff.writes.1,
    (b.read (r := 3) (n := 64) (by simp)).trans eff.writes.2.1,
    (b.read (r := 5) (n := 64) (by simp)).trans eff.writes.2.2, ?_, ?_⟩
  · unfold slot
    rw [st]
    exact h.writes.trans (congrArg (· + 1) mem)
  · rw [su, show rspOf s = stackPtr s from Operand.read_reg64 s 4] at b
    exact (a.trans b).mono (by simp)

end Hkdf.Proofs.NewExpand.Expand.Finalize
