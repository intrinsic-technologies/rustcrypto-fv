import Sha2.Proofs.Wrapper512.Dispatch.Run
import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.Encoding.Serialize.Prologue
import Sha2.Proofs.Common.Encoding.Serialize.Stack
import X86Proofs.Instructions.Push.Triple
import Sha2.Proofs.Common.Machine.CallMemory

set_option autoImplicit false
namespace Sha2.Proofs.Wrapper512.Dispatch
open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.Encoding.Serialize
open Sha2.Proofs.Wrapper512
open Sha2.Proofs.Wrapper

 theorem stack_bounds512 [Bindings] {v : Variant} {form : Form} {initial : RamState} {inputs : Array Input}
    (ctx : Context v initial inputs form) :
    (v.routine form).minStackBytes ≤ (stackPtr initial).toNat ∧ (stackPtr initial).toNat + 8 < 2^32 := by
  refine ⟨ctx.stack.2.2.1, ?_⟩
  have hb := ctx.stack.1
  change (Stack.region initial (v.routine form).minStackBytes).start +
    (Stack.region initial (v.routine form).minStackBytes).size < 2^32 at hb
  rwa [stack_region_end] at hb

theorem stack_sub_toNat512 [Bindings] {v : Variant} {form : Form} {initial : RamState} {inputs : Array Input}
    (ctx : Context v initial inputs form) {offset : Nat} (hoffset : offset ≤ (v.routine form).minStackBytes) :
    (stackPtr initial - BitVec.ofNat 64 offset).toNat = (stackPtr initial).toNat - offset := by
  have hn := (stack_bounds512 ctx).1
  have ho : offset < 2^64 := by omega
  rw [BitVec.toNat_sub_of_le (by
    rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho]
    omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho]

theorem stack_sub_readable512 [Bindings] {v : Variant} {form : Form} {initial : RamState} {inputs : Array Input}
    (ctx : Context v initial inputs form) {offset len : Nat} (hoffset : offset ≤ (v.routine form).minStackBytes)
    (hlen : len ≤ offset + 8) : MemReadable initial (stackPtr initial - BitVec.ofNat 64 offset) len := by
  apply memoryRegion_memReadable ctx.stack.1 ctx.stack.2.1
  · rw [stack_sub_toNat512 ctx hoffset]
    change (stackPtr initial).toNat - (v.routine form).minStackBytes ≤ (stackPtr initial).toNat - offset
    omega
  · rw [stack_region_end, stack_sub_toNat512 ctx hoffset]
    have h := (stack_bounds512 ctx).1
    omega

theorem stack_sub_writable8_512 [Bindings] {v : Variant} {form : Form} {initial : RamState} {inputs : Array Input}
    (ctx : Context v initial inputs form) {offset : Nat} (hoffset : offset ≤ (v.routine form).minStackBytes)
    (halign : offset % 8 = 0) :
    MemWritable initial (stackPtr initial - BitVec.ofNat 64 offset) 8 := by
  have hr := stack_sub_readable512 ctx hoffset (show 8 ≤ offset + 8 by omega)
  refine MemWritable.of_not_reserved (by decide) hr.low hr.mem ?_
  intro i hi hreserved
  apply (ctx.separation.2 (Stack.region initial (v.routine form).minStackBytes) (by cases form <;> simp [Variant.writeRegions, Variant.routine, Vector.toList, Form.writeRegionCount])).2
    (stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i) ?_ (.inr hreserved)
  apply memoryRegion_contains_add ctx.stack.1 (len := 8) _ _ hi
  · rw [stack_sub_toNat512 ctx hoffset]
    change (stackPtr initial).toNat - (v.routine form).minStackBytes ≤ (stackPtr initial).toNat - offset
    omega
  · rw [stack_region_end, stack_sub_toNat512 ctx hoffset]
    have h := (stack_bounds512 ctx).1
    omega

end Sha2.Proofs.Wrapper512.Dispatch

namespace Sha2.Proofs.Wrapper512.Dispatch

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.Encoding.Serialize

 theorem push_loaded512 [Bindings] {v : Variant} {form : Form} {initial t : RamState} {inputs : Array Input} (ctx : Context v initial inputs form)
    (loaded : ProgramLoaded t) (src : BitVec 4) {offset : Nat}
    (hoffset : offset ≤ (v.routine form).minStackBytes)
    (haddr : pushAddr t = stackPtr initial - BitVec.ofNat 64 offset) :
    ProgramLoaded (pushAfter t src) := by
  intro address byte hfetch
  have hf : AgreesExcept [.reg 4, .mem (pushAddr t) 8, .rip] t (pushAfter t src) :=
    AgreesExcept.afterStep_push t _ _ _
  rw [hf.memory address]
  · exact loaded address byte hfetch
  · intro c hc hcover
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact hcover
    · obtain ⟨i, hi, he⟩ := hcover
      apply (ctx.separation.2 (Stack.region initial (v.routine form).minStackBytes) (by cases form <;> simp [Variant.writeRegions, Variant.routine, Vector.toList, Form.writeRegionCount])).2 address _ (.inl ⟨byte, hfetch⟩)
      rw [he, haddr]
      apply memoryRegion_contains_add ctx.stack.1 (len := 8) _ _ hi
      · rw [stack_sub_toNat512 ctx hoffset]
        change (stackPtr initial).toNat - (v.routine form).minStackBytes ≤ (stackPtr initial).toNat - offset
        omega
      · rw [stack_region_end, stack_sub_toNat512 ctx hoffset]
        have h := (stack_bounds512 ctx).1
        omega
    · exact hcover

 theorem push_checked512 [Bindings] {v : Variant} {form : Form} {initial t : RamState} {inputs : Array Input} (ctx : Context v initial inputs form)
    (ready : ReadyToStep t) (loaded : ProgramLoaded t)
    (grow : ∀ a : BitVec 64, (initial.external[a]?).isSome → (t.external[a]?).isSome)
    (src : BitVec 4) (offset codeOffset : Nat)
    (hsp : stackPtr t = stackPtr initial - BitVec.ofNat 64 offset)
    (hip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 codeOffset)
    (hoffset : offset + 8 ≤ (v.routine form).minStackBytes) (halign : (offset + 8) % 8 = 0)
    (hsize : codeOffset + (encodePushR64 src).length < 71757)
    (hbytes : Extracted.textBytes.toListFrom codeOffset (encodePushR64 src).length =
      encodePushR64 src) :
    Advances (returnBoundary initial) 1 t (pushAfter t src) ∧ ReadyToStep (pushAfter t src) ∧
      ProgramLoaded (pushAfter t src) ∧
      (pushAfter t src).RIP =
        Extracted.textAddress + BitVec.ofNat 64 (codeOffset + (encodePushR64 src).length) ∧
      stackPtr (pushAfter t src) = stackPtr initial - BitVec.ofNat 64 (offset + 8) := by
  have haddr : pushAddr t = stackPtr initial - BitVec.ofNat 64 (offset + 8) := by
    rw [pushAddr, hsp, BitVec.sub_sub, BitVec.ofNat_add]
    rfl
  have hw : MemWritable t (pushAddr t) 8 := by
    rw [haddr]
    exact writable_of_grow (stack_sub_writable8_512 ctx hoffset halign) grow
  have hc := programText_slice (programLoaded_codeIn loaded) codeOffset
    (encodePushR64 src) (by omega) hbytes
  have hs : X86.Machine.step t = some (.next (pushAfter t src)) := by
    apply push_r64_step_of_register t ready src
    · rw [hip]; exact hc.bytesAt
    · rw [hip]
      exact hc.low (by
        rcases encodePushR64_spec src with ⟨op, hb, _⟩ | ⟨rex, op, hb, _⟩ <;> simp [hb])
        (by rcases encodePushR64_spec src with ⟨op, hb, _⟩ | ⟨rex, op, hb, _⟩ <;> simp [hb])
    · exact hw
  have hrip : (pushAfter t src).RIP =
      Extracted.textAddress + BitVec.ofNat 64 (codeOffset + (encodePushR64 src).length) := by
    rw [show (pushAfter t src).RIP = BitVec.add t.RIP (BitVec.ofNat 64 (encodePushR64 src).length) from
      afterStep_push_rip ready _ _ _, hip]
    change (Extracted.textAddress + BitVec.ofNat 64 codeOffset) +
      BitVec.ofNat 64 (encodePushR64 src).length = _
    rw [BitVec.add_assoc, BitVec.ofNat_add]
  refine ⟨Advances.of_step hs (.inl ?_), ready.afterStep_push _ _ _ hw.low hw.tables,
    push_loaded512 ctx loaded src hoffset haddr, hrip, ?_⟩
  · rw [hrip]
    exact boundary_ne_program (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2 (inProgram_of_textOffset _ hsize)
  · exact (pushAfter_rsp t src).trans haddr

 theorem push_exists512 [Bindings] {v : Variant} {form : Form} {initial t : RamState} {inputs : Array Input} (ctx : Context v initial inputs form)
    (ready : ReadyToStep t) (loaded : ProgramLoaded t)
    (grow : ∀ a : BitVec 64, (initial.external[a]?).isSome → (t.external[a]?).isSome)
    (src : BitVec 4) (offset codeOffset : Nat)
    (hsp : stackPtr t = stackPtr initial - BitVec.ofNat 64 offset)
    (hip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 codeOffset)
    (hoffset : offset + 8 ≤ (v.routine form).minStackBytes) (halign : (offset + 8) % 8 = 0)
    (hsize : codeOffset + (encodePushR64 src).length < 71757)
    (hbytes : Extracted.textBytes.toListFrom codeOffset (encodePushR64 src).length = encodePushR64 src) :
    ∃ u, Advances (returnBoundary initial) 1 t u ∧ ReadyToStep u ∧ ProgramLoaded u ∧
      u.RIP = Extracted.textAddress + BitVec.ofNat 64 (codeOffset + (encodePushR64 src).length) ∧
      stackPtr u = stackPtr initial - BitVec.ofNat 64 (offset + 8) ∧
      AgreesExcept [.reg 4, .mem (stackPtr initial - BitVec.ofNat 64 (offset + 8)) 8, .rip] t u ∧
      u.external = memStore t.external (stackPtr initial - BitVec.ofNat 64 (offset + 8))
        ((Operand.reg (src.setWidth 5) : Operand 64).read t) := by
  obtain ⟨ha, hr, hl, hip', hsp'⟩ :=
    push_checked512 ctx ready loaded grow src offset codeOffset hsp hip hoffset halign hsize hbytes
  have haddr : pushAddr t = stackPtr initial - BitVec.ofNat 64 (offset + 8) := by
    rw [pushAddr, hsp, BitVec.sub_sub, BitVec.ofNat_add]
    rfl
  refine ⟨pushAfter t src, ha, hr, hl, hip', hsp', ?_, ?_⟩
  · rw [← haddr]; exact AgreesExcept.afterStep_push t _ _ _
  · rw [← haddr]; rfl

end Sha2.Proofs.Wrapper512.Dispatch

namespace Sha2.Proofs.Wrapper512.Dispatch
open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.Encoding.Serialize
open Sha2.Proofs.Wrapper512

 theorem save_registers512 [Bindings] {v : Variant} {initial : RamState} {inputs : Array Input}
    (ctx : Context v initial inputs) :
    ∃ s, Advances (returnBoundary initial) 6 initial s ∧ ReadyToStep s ∧ ProgramLoaded s ∧
      s.RIP = v.pc 0xa ∧ stackPtr s = stackPtr initial - 48 ∧
      s.external = saveMemory initial ∧ AgreesExcept (saveFrame initial) initial s := by
  have push : PushSteps initial (returnBoundary initial) := ⟨by
    intro t ready loaded grow src offset codeOffset sp ip bound align size bytes
    have hv : v.routine.minStackBytes = 1184 := rfl
    exact push_exists512 ctx ready loaded grow src offset codeOffset sp ip (by omega) align size bytes⟩
  have entry : initial.RIP = Extracted.textAddress + BitVec.ofNat 64 v.textOffset := by
    simpa only [Variant.routine, Variant.pc, Nat.add_zero] using ctx.call.entry
  obtain ⟨s, run, ready, loaded, rip, rsp, memory, frame⟩ :=
    save_registers_of_push push (supportedMachine_readyToStep ctx.machine)
      ctx.call.programLoaded (codeOffset := v.textOffset) entry
      (by cases v <;> constructor <;> decide +kernel)
  have rip' : s.RIP = v.pc 0xa := by
    simpa only [Variant.pc, BitVec.ofNat_add] using rip
  refine ⟨s, run, ready, loaded, rip', rsp, memory, frame⟩

end Sha2.Proofs.Wrapper512.Dispatch

namespace Sha2.Proofs.Wrapper512.Dispatch
open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine
open Sha2.Proofs.Wrapper512

 theorem sub_frame512 [Bindings] {v : Variant} {initial s : RamState}
    (ctx : Context v initial #[]) (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (rip : s.RIP = v.pc 0xa) (rsp : stackPtr s = stackPtr initial - 48) :
    ∃ t, Advances (returnBoundary initial) 1 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = v.pc 0x11 ∧ stackPtr t = stackPtr initial - BitVec.ofNat 64 632 ∧
      AgreesExcept [.reg 4, .flags, .rip] s t := by
  obtain ⟨t, step, readyT, effect⟩ :=
    (sub_r64_imm32_effect_step (v.pc 0xa) 0x48 0xec 584
      (by constructor <;> decide) (by decide) (by decide)).advances ready
      (programText_slice (programLoaded_codeIn loaded) (v.textOffset + 0xa)
        [0x48,0x81,0xec,0x48,0x02,0x00,0x00]
        (by cases v <;> decide) (by cases v <;> decide +kernel)) rip
      (boundary_ne_program (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2 (by
        have hnext : InProgram (v.pc 0x11) := Variant.pc_inProgram v (by decide)
        simpa [subR64Imm32Effect, Variant.pc_add] using hnext))
  have agrees : AgreesExcept [.reg 4, .flags, .rip] s t := effect.agrees
  have loadedT : ProgramLoaded t := by
    intro address byte hfetch
    rw [agrees.external (by simp [Component.Covers])]
    exact loaded address byte hfetch
  have rspT : stackPtr t = stackPtr initial - BitVec.ofNat 64 632 := by
    have h := effect.writes
    simp only [subR64Imm32Effect, Write.AllHold, Operand.read] at h
    change t.regValue .rsp = s.regValue .rsp - BitVec.signExtend 64 584 at h
    rw [← stackPtr_eq_regValue_rsp t, ← stackPtr_eq_regValue_rsp s, rsp] at h
    rw [h]
    change stackPtr initial - BitVec.ofNat 64 48 - BitVec.signExtend 64 (BitVec.ofNat 32 584) = _
    have hs : BitVec.signExtend 64 (BitVec.ofNat 32 584) = BitVec.ofNat 64 584 := by decide +kernel
    rw [hs, BitVec.sub_sub]
    rfl
  have ripT : t.RIP = v.pc 0x11 := by
    rw [effect.rip]
    exact Variant.pc_add v 0xa 7
  exact ⟨t, step, readyT, loadedT, ripT, rspT, agrees⟩

end Sha2.Proofs.Wrapper512.Dispatch

