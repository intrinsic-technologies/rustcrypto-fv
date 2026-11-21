import Hkdf.Proofs.NewExpand.Wrapper.Frame
import Hkdf.Proofs.Common.CallFrame.Stack
import Hkdf.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.Add.Generated.Imm32.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Movzx.Generated.RR8.Triple
import X86Proofs.Instructions.Pop.Triple

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Wrapper

open Hkdf.Spec Hkdf.Spec.Program Hkdf.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Field (AdvanceTriple)
open Hkdf.Proofs.Common.Machine

private def returnBytes : List UInt8 :=
  [0x0f, 0xb6, 0xc0, 0x01, 0xc0, 0x48, 0x81, 0xc4, 0x40, 1, 0, 0,
   0x5b, 0x41, 0x5c, 0x41, 0x5d, 0x41, 0x5e, 0x41, 0x5f, 0xc3]

private structure ReturnPre (s : RamState) : Prop where
  rip : s.RIP = 0x102044
  readable : ∀ offset : BitVec 64, offset.toNat ≤ 360 →
    MemReadable s (stackPtr s + offset) 8

private def returnPrefixEffect (s : RamState) : Effect where
  rip := 0x102059
  writes :=
    [⟨rax, (((Operand.byteReg 0).read s).setWidth 32 +
      ((Operand.byteReg 0).read s).setWidth 32).setWidth 64⟩,
     ⟨(Operand.reg 4 : Operand 64), stackPtr s + 360⟩,
     ⟨(Operand.reg 3 : Operand 64), (Operand.mem (stackPtr s + 320) : Operand 64).read s⟩,
     ⟨(Operand.reg 12 : Operand 64), (Operand.mem (stackPtr s + 328) : Operand 64).read s⟩,
     ⟨(Operand.reg 13 : Operand 64), (Operand.mem (stackPtr s + 336) : Operand 64).read s⟩,
     ⟨(Operand.reg 14 : Operand 64), (Operand.mem (stackPtr s + 344) : Operand 64).read s⟩,
     ⟨(Operand.reg 15 : Operand 64), (Operand.mem (stackPtr s + 352) : Operand 64).read s⟩]
  flags := some (.ofStatusFlags (addSpec (stackPtr s) 320).2)

local macro "epilogue_next " outside:term "," offset:term : tactic =>
  `(tactic| exact boundary_ne_program $outside (inProgram_of_textOffset $offset (by decide)))

local macro "epilogue_pop_mid " outside:term "," offset:term "," site:term : tactic => `(tactic| (
  intro s t hp hh ho
  refine ⟨⟨hh.rip_of (by x86_norm), ?_⟩,
    Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
  · have hsp : stackPtr t = stackPtr s + $offset := by
      have hs := (ho true).read_reg (n := 64) 4
      x86_norm at hs
      exact hs.symm
    rw [hsp]
    exact (hp.readable $offset (by decide)).of_holds hh
  · epilogue_next $outside, $site))

private theorem returnPrefix [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary ReturnPre (codeRange 0x102044 returnBytes)
      (Effect.post returnPrefixEffect) := by
  advance_begin (show StepEffect (fun s => s.RIP = 0x102044)
    (codeRange 0x102044 [0x0f, 0xb6, 0xc0]) (movzxR32R8NoRexEffect 0x102044 3 0 0) from
    movzx_r32_r8_norex_effect_step 0x102044 0xc0 (by decide))
  case next => intro s hp; epilogue_next outside, 0x2047
  advance_then (show StepEffect (fun s => s.RIP = 0x102047)
    (codeRange 0x102047 [0x01, 0xc0]) (addR32R32Effect 0x102047 2 0 0) from
    add_r32_r32_effect_step 0x102047 0xc0 (by decide))
  case sub => exact codeRange_slice_subset 0x102044 returnBytes 3 2
  case mid =>
    intro s t hp hh _
    exact ⟨hh.rip, Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x2049 (by decide))⟩
  advance_then (show StepEffect (fun s => s.RIP = 0x102049)
    (codeRange 0x102049 [0x48, 0x81, 0xc4, 0x40, 1, 0, 0]) (addR64Imm32Effect 0x102049 4 320) from
    add_r64_imm32_effect_step 0x102049 0x48 0xc4 320 (by simp [RexWPrefix]) (by decide) (by decide))
  case sub => exact codeRange_slice_subset 0x102044 returnBytes 5 7
  case mid =>
    intro s t hp hh _
    exact ⟨hh.rip, Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0x2050 (by decide))⟩
  advance_then pop_r64_effect_step 0x102050 0x5b (by decide) (by decide)
  case sub => exact codeRange_slice_subset 0x102044 returnBytes 12 1
  case mid => epilogue_pop_mid outside, 320, 0x2051
  advance_then pop_r64_rex_effect_step 0x102051 0x41 0x5c (by simp [RexPrefix]) (by decide) (by decide)
  case sub => exact codeRange_slice_subset 0x102044 returnBytes 13 2
  case mid => epilogue_pop_mid outside, 328, 0x2053
  advance_then pop_r64_rex_effect_step 0x102053 0x41 0x5d (by simp [RexPrefix]) (by decide) (by decide)
  case sub => exact codeRange_slice_subset 0x102044 returnBytes 15 2
  case mid => epilogue_pop_mid outside, 336, 0x2055
  advance_then pop_r64_rex_effect_step 0x102055 0x41 0x5e (by simp [RexPrefix]) (by decide) (by decide)
  case sub => exact codeRange_slice_subset 0x102044 returnBytes 17 2
  case mid => epilogue_pop_mid outside, 344, 0x2057
  advance_then pop_r64_rex_effect_step 0x102057 0x41 0x5f (by simp [RexPrefix]) (by decide) (by decide)
  case sub => exact codeRange_slice_subset 0x102044 returnBytes 19 2
  case mid => epilogue_pop_mid outside, 352, 0x2059
  advance_finish [returnPrefixEffect, stackPtr, rspOf, Operand.read_reg64, BitVec.setWidth_setWidth]

theorem finishReturn [bindings : Bindings] {initial s : RamState}
    (stack : Stack.Valid initial hkdfSha256NewExpandMinStackBytes)
    (ret : ValidReturnAddress initial) (regs : SavedFrame initial s)
    (rsp : stackPtr s = stackPtr initial - 360) (rip : s.RIP = 0x102044)
    (machine : SupportedMachine bindings s) (loaded : ProgramLoaded s)
    (direction : DirectionFlagUnset s)
    (allocated : ∀ a : BitVec 64, (initial.external[a]?).isSome → (s.external[a]?).isSome) :
    ∃ fuel t, Returns (returnBoundary initial) fuel s t ∧
      SupportedMachine bindings t ∧ CalleeSavedRegistersUnchanged initial t ∧
      DirectionFlagUnset t ∧ t.external = s.external ∧
      (t.regValue .rax).setWidth 32 =
        ((s.regValue .rax).setWidth 8).setWidth 32 + ((s.regValue .rax).setWidth 8).setWidth 32 := by
  obtain ⟨address, word, low, outside⟩ := ret
  have addressEq : (returnBoundary initial).rip = address := by
    have loadedWord := word.2
    change X86.Machine.loadBytes _ (BitVec.ofNat 64 (stackPtr initial).toNat) 8 = _ at loadedWord
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq] at loadedWord
    exact Hkdf.Proofs.Common.Memory.memLoad_of_loadBytes64 loadedWord
  have stackAddr (offset : BitVec 64) (bound : offset.toNat ≤ 360) :
      stackPtr s + offset = stackPtr initial - BitVec.ofNat 64 (360 - offset.toNat) := by
    have hsub : BitVec.ofNat 64 (360 - offset.toNat) = 360 - offset := by
      rw [← BitVec.ofNat_sub_ofNat_of_le 360 offset.toNat (by omega) bound, BitVec.ofNat_toNat]
      rfl
    rw [rsp, hsub, BitVec.sub_eq_add_neg (360 : BitVec 64) offset, ← BitVec.sub_sub, BitVec.sub_neg]
  have readable (offset : BitVec 64) (bound : offset.toNat ≤ 360) :
      MemReadable s (stackPtr s + offset) 8 := by
    rw [stackAddr offset bound]
    exact Hkdf.Proofs.Common.CallFrame.stack_readable stack allocated
      (show 360 - offset.toNat ≤ 2632 by omega) (by omega)
  have code : CodeIn (codeRange 0x102044 returnBytes) s :=
    programText_slice (programLoaded_codeIn loaded) 0x2044 returnBytes
      (by decide +kernel) (by decide +kernel)
  obtain ⟨fuel, u, run, ready, code', prefixEffect⟩ :=
    returnPrefix (returnBoundary initial) (by rw [addressEq]; exact outside) s
      (supportedMachine_readyToStep machine) code ⟨rip, readable⟩
  have mem : u.external = s.external :=
    prefixEffect.agrees.external (by simp [returnPrefixEffect, Effect.components, Component.Covers])
  have prefixRsp : stackPtr u = stackPtr s + 360 := prefixEffect.writes.2.1
  have sp : stackPtr u = stackPtr initial := by
    rw [prefixRsp, rsp, BitVec.sub_add_cancel]
  have top : stackTop u = (returnBoundary initial).rip := by
    change memLoad u.external (stackPtr u) 64 = _
    rw [sp, mem]
    exact regs.ret
  have retCode : CodeIn (codeRange 0x102059 [0xc3]) u :=
    code'.mono (codeRange_slice_subset 0x102044 returnBytes 21 1)
  have retPre : RetPre 0x102059 u := by
    refine ⟨⟨prefixEffect.rip, ?_⟩, ?_⟩
    · rw [prefixRsp]
      exact (readable 360 (by decide)).of_external_eq mem
    · rwa [top, addressEq]
  obtain ⟨t, step, ready', effect⟩ := ret_effect_step 0x102059 u ready retCode retPre
  have returned : Returns (returnBoundary initial) 1 u t := by
    apply Returns.of_step step (effect.rip.trans top)
    have hsp : stackPtr t = stackPtr u + 8 := effect.writes
    exact hsp.trans (congrArg (· + 8) sp)
  have agrees := prefixEffect.agrees.trans effect.agrees
  refine ⟨fuel + 1, t, run.returns returned,
    supportedMachine_of_ready_agrees machine ready' agrees, ?_,
    agrees.directionFlagClear (by rw [retEffect_components]; simp [returnPrefixEffect, Effect.components]) direction,
    (effect.agrees.external (by simp [Component.Covers])).trans mem, ?_⟩
  · have restore (r : BitVec 5) (offset : BitVec 64) (other : r ≠ 4)
        (bound : offset.toNat ≤ 360)
        (value : (Operand.reg r : Operand 64).read u =
          (Operand.mem (stackPtr s + offset) : Operand 64).read s) :
        (Operand.reg r : Operand 64).read t =
          memLoad s.external (stackPtr initial - BitVec.ofNat 64 (360 - offset.toNat)) 64 := by
      rw [effect.agrees.read (by simpa using other), value]
      change memLoad s.external (stackPtr s + offset) 64 = _
      rw [stackAddr offset bound]
    intro reg hreg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hreg
    rcases hreg with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (restore 3 320 (by decide) (by decide) prefixEffect.writes.2.2.1).trans regs.rbx
    · exact (agrees.read (n := 64) (r := 5)
        (by rw [retEffect_components]; simp [returnPrefixEffect, Effect.components])).trans regs.rbp
    · exact (restore 12 328 (by decide) (by decide) prefixEffect.writes.2.2.2.1).trans regs.r12
    · exact (restore 13 336 (by decide) (by decide) prefixEffect.writes.2.2.2.2.1).trans regs.r13
    · exact (restore 14 344 (by decide) (by decide) prefixEffect.writes.2.2.2.2.2.1).trans regs.r14
    · exact (restore 15 352 (by decide) (by decide) prefixEffect.writes.2.2.2.2.2.2).trans regs.r15
  · have status := (effect.agrees.read (n := 64) (r := 0) (by simp)).trans prefixEffect.writes.1
    change t.regValue .rax = _ at status
    rw [status, BitVec.setWidth_setWidth (by decide : ¬ (64 < 32 ∧ 64 < 32))]
    rfl

end Hkdf.Proofs.NewExpand.Wrapper
