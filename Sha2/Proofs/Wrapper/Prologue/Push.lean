import Sha2.Proofs.Wrapper.Memory
import Sha2.Proofs.Common.Encoding.Serialize.Prologue

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper.Prologue

open Sha2.Spec Sha2.Proofs.Program Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.Encoding.Serialize (writable_of_grow)

variable {v : Variant} [bindings : Bindings] {s t : RamState} {inputs : Array Input}

theorem push_loaded (ctx : Context s inputs v)
    (loaded : ProgramLoaded t) (src : BitVec 4) {offset : Nat}
    (hoffset : offset ≤ 816)
    (haddr : pushAddr t = stackPtr s - BitVec.ofNat 64 offset) :
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
      apply (ctx.call.separation.2 (Stack.region s v.routine.minStackBytes) (by simp)).2 address _ (.inl ⟨byte, hfetch⟩)
      rw [he, haddr]
      apply memoryRegion_contains_add ctx.call.stack.1 (len := 8) _ _ hi
      · rw [validCall_stack_sub_toNat ctx.call hoffset]
        change (stackPtr s).toNat - 816 ≤ (stackPtr s).toNat - offset
        omega
      · rw [stack_region_end, validCall_stack_sub_toNat ctx.call hoffset]
        have := (validCall_stack_bounds ctx.call).1
        omega
    · exact hcover

theorem push_checked (ctx : Context s inputs v)
    (ready : ReadyToStep t) (loaded : ProgramLoaded t)
    (grow : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome)
    (src : BitVec 4) (offset codeOffset : Nat)
    (hsp : stackPtr t = stackPtr s - BitVec.ofNat 64 offset)
    (hip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 codeOffset)
    (hoffset : offset + 8 ≤ 816) (halign : (offset + 8) % 8 = 0)
    (hsize : codeOffset + (encodePushR64 src).length < 71757)
    (hbytes : Extracted.textBytes.toListFrom codeOffset (encodePushR64 src).length =
      encodePushR64 src) :
    Advances (returnBoundary s) 1 t (pushAfter t src) ∧ ReadyToStep (pushAfter t src) ∧
      ProgramLoaded (pushAfter t src) ∧
      (pushAfter t src).RIP =
        Extracted.textAddress + BitVec.ofNat 64 (codeOffset + (encodePushR64 src).length) ∧
      stackPtr (pushAfter t src) = stackPtr s - BitVec.ofNat 64 (offset + 8) := by
  have haddr : pushAddr t = stackPtr s - BitVec.ofNat 64 (offset + 8) := by
    rw [pushAddr, hsp, BitVec.sub_sub]
    rw [BitVec.ofNat_add]
    rfl
  have hw : MemWritable t (pushAddr t) 8 := by
    rw [haddr]
    exact writable_of_grow (validCall_stack_sub_writable8 ctx.call hoffset halign) grow
  have hc := programText_slice (programLoaded_codeIn loaded) codeOffset
    (encodePushR64 src) (by omega) hbytes
  have hs : X86.Machine.step t = some (.next (pushAfter t src)) := by
    apply push_r64_step_of_register t ready src
    · rw [hip]
      exact hc.bytesAt
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
    push_loaded ctx loaded src hoffset haddr, hrip, ?_⟩
  · rw [hrip]
    exact boundary_ne_program (validCall_returnBoundary ctx.machine ctx.call).2.2 (inProgram_of_textOffset _ hsize)
  · exact (pushAfter_rsp t src).trans haddr

theorem push_exists (ctx : Context s inputs v)
    (ready : ReadyToStep t) (loaded : ProgramLoaded t)
    (grow : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome)
    (src : BitVec 4) (offset codeOffset : Nat)
    (hsp : stackPtr t = stackPtr s - BitVec.ofNat 64 offset)
    (hip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 codeOffset)
    (hoffset : offset + 8 ≤ 816) (halign : (offset + 8) % 8 = 0)
    (hsize : codeOffset + (encodePushR64 src).length < 71757)
    (hbytes : Extracted.textBytes.toListFrom codeOffset (encodePushR64 src).length =
      encodePushR64 src) :
    ∃ u, Advances (returnBoundary s) 1 t u ∧ ReadyToStep u ∧ ProgramLoaded u ∧
      u.RIP = Extracted.textAddress +
        BitVec.ofNat 64 (codeOffset + (encodePushR64 src).length) ∧
      stackPtr u = stackPtr s - BitVec.ofNat 64 (offset + 8) ∧
      AgreesExcept [.reg 4, .mem (stackPtr s - BitVec.ofNat 64 (offset + 8)) 8, .rip] t u ∧
      u.external = memStore t.external (stackPtr s - BitVec.ofNat 64 (offset + 8))
        ((Operand.reg (src.setWidth 5) : Operand 64).read t) := by
  obtain ⟨ha, hr, hl, hip', hsp'⟩ :=
    push_checked ctx ready loaded grow src offset codeOffset hsp hip hoffset halign hsize hbytes
  have haddr : pushAddr t = stackPtr s - BitVec.ofNat 64 (offset + 8) := by
    rw [pushAddr, hsp, BitVec.sub_sub, BitVec.ofNat_add]
    rfl
  refine ⟨pushAfter t src, ha, hr, hl, hip', hsp', ?_, ?_⟩
  · rw [← haddr]
    exact AgreesExcept.afterStep_push t _ _ _
  · rw [← haddr]
    rfl

end Sha2.Proofs.Wrapper.Prologue
