import Hkdf.Proofs.Common.Encoding.Serialize.Stack
import Hkdf.Proofs.Common.Machine.Code
import X86Proofs.Instructions.Push.Triple

set_option autoImplicit false

open Hkdf.Proofs.Common.Machine (CalleePre boundary_ne_program inProgram_of_textOffset memoryRegion_contains_add programLoaded_codeIn programText_slice stack_region_end)

namespace Hkdf.Proofs.Common.Encoding.Serialize

open Hkdf.Spec Hkdf.Proofs.Program Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [bindings : Bindings] {s t : RamState} {boundary : ReturnBoundary}
  {entry : BitVec 64} {inputBytes outputBytes reserve : Nat}

theorem push_loaded (pre : CalleePre s boundary entry inputBytes outputBytes reserve)
    (loaded : ProgramLoaded t) (src : BitVec 4) {offset : Nat}
    (hoffset : offset ≤ reserve)
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
      apply pre.avoids (Stack.region s reserve) (by simp) address _ (.inl ⟨byte, hfetch⟩)
      rw [he, haddr]
      apply memoryRegion_contains_add pre.stack.1 (len := 8) _ _ hi
      · rw [stack_sub_toNat pre hoffset]
        change (stackPtr s).toNat - reserve ≤ (stackPtr s).toNat - offset
        omega
      · rw [stack_region_end, stack_sub_toNat pre hoffset]
        have := (stack_bounds pre).1
        omega
    · exact hcover

theorem push_checked (pre : CalleePre s boundary entry inputBytes outputBytes reserve)
    (ready : ReadyToStep t) (loaded : ProgramLoaded t)
    (grow : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome)
    (src : BitVec 4) (offset codeOffset : Nat)
    (hsp : stackPtr t = stackPtr s - BitVec.ofNat 64 offset)
    (hip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 codeOffset)
    (hoffset : offset + 8 ≤ reserve) (halign : (offset + 8) % 8 = 0)
    (hsize : codeOffset + (encodePushR64 src).length < 115149)
    (hbytes : Extracted.textBytes.toListFrom codeOffset (encodePushR64 src).length =
      encodePushR64 src) :
    Advances boundary 1 t (pushAfter t src) ∧ ReadyToStep (pushAfter t src) ∧
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
    exact writable_of_grow (stack_sub_writable8 pre hoffset halign) grow
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
    push_loaded pre loaded src hoffset haddr, hrip, ?_⟩
  · rw [hrip]
    exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset _ hsize)
  · exact (pushAfter_rsp t src).trans haddr

theorem push_exists (pre : CalleePre s boundary entry inputBytes outputBytes reserve)
    (ready : ReadyToStep t) (loaded : ProgramLoaded t)
    (grow : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome)
    (src : BitVec 4) (offset codeOffset : Nat)
    (hsp : stackPtr t = stackPtr s - BitVec.ofNat 64 offset)
    (hip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 codeOffset)
    (hoffset : offset + 8 ≤ reserve) (halign : (offset + 8) % 8 = 0)
    (hsize : codeOffset + (encodePushR64 src).length < 115149)
    (hbytes : Extracted.textBytes.toListFrom codeOffset (encodePushR64 src).length =
      encodePushR64 src) :
    ∃ u, Advances boundary 1 t u ∧ ReadyToStep u ∧ ProgramLoaded u ∧
      u.RIP = Extracted.textAddress +
        BitVec.ofNat 64 (codeOffset + (encodePushR64 src).length) ∧
      stackPtr u = stackPtr s - BitVec.ofNat 64 (offset + 8) ∧
      AgreesExcept [.reg 4, .mem (stackPtr s - BitVec.ofNat 64 (offset + 8)) 8, .rip] t u ∧
      u.external = memStore t.external (stackPtr s - BitVec.ofNat 64 (offset + 8))
        ((Operand.reg (src.setWidth 5) : Operand 64).read t) := by
  obtain ⟨ha, hr, hl, hip', hsp'⟩ :=
    push_checked pre ready loaded grow src offset codeOffset hsp hip hoffset halign hsize hbytes
  have haddr : pushAddr t = stackPtr s - BitVec.ofNat 64 (offset + 8) := by
    rw [pushAddr, hsp, BitVec.sub_sub, BitVec.ofNat_add]
    rfl
  refine ⟨pushAfter t src, ha, hr, hl, hip', hsp', ?_, ?_⟩
  · rw [← haddr]
    exact AgreesExcept.afterStep_push t _ _ _
  · rw [← haddr]
    rfl

end Hkdf.Proofs.Common.Encoding.Serialize
