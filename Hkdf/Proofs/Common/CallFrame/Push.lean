import Hkdf.Proofs.Common.CallFrame.Stack
import Hkdf.Proofs.Common.Encoding.Serialize.Prologue
import Hkdf.Proofs.Common.Machine.StackRegion

namespace Hkdf.Proofs.Common.CallFrame

open Hkdf.Spec.Program Hkdf.Proofs.Program Hkdf.Proofs.Common Hkdf.Proofs.Common.Machine
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem stack_avoids {initial : RamState} {reserve : Nat} (avoid : (Stack.region initial reserve).Avoids
    (fun a ↦ InProgram a ∨ InPageTables a)) :
    ∀ region ∈ #v[Stack.region initial reserve], region.Avoids InProgram := by
  intro region member a ha hp
  rcases Vector.mem_singleton.mp member with rfl
  exact avoid a ha (.inl hp)

theorem stack_slot_within {initial : RamState} {reserve offset len : Nat}
    (stack : Stack.Valid initial reserve) (low : offset ≤ reserve) (high : len ≤ offset)
    (components : List Component) (slots : ∀ c ∈ components, ∀ a, c.Covers a →
      (Component.mem (stackPtr initial - BitVec.ofNat 64 offset) len).Covers a) :
    WritesWithin components #v[Stack.region initial reserve] := by
  intro c hc a ha
  exact ⟨_, by simp, stackRegion_contains_sub stack.2.2.1 low high (slots c hc a ha)⟩

theorem push_steps [Bindings] {initial : RamState} {boundary : ReturnBoundary}
    {reserve : Nat} (stack : Stack.Valid initial reserve) (capacity : 48 ≤ reserve)
    (avoid : (Stack.region initial reserve).Avoids (fun a ↦ InProgram a ∨ InPageTables a))
    (outside : ¬ InProgram boundary.rip) : Encoding.Serialize.PushSteps initial boundary := by
  constructor
  intro s ready loaded grow src offset codeOffset rsp rip bound align size bytes
  have addr : pushAddr s = stackPtr initial - BitVec.ofNat 64 (offset + 8) := by
    rw [pushAddr, rsp, BitVec.sub_sub, BitVec.ofNat_add]
    rfl
  have writable : MemWritable s (pushAddr s) 8 := by
    rw [addr]
    exact stack_writable8 stack avoid grow (by omega) align
  have code := programText_slice (programLoaded_codeIn loaded) codeOffset
    (encodePushR64 src) (by omega) bytes
  have hstep : X86.Machine.step s = some (.next (pushAfter s src)) := by
    apply push_r64_step_of_register s ready src
    · rw [rip]
      exact code.bytesAt
    · rw [rip]
      exact code.low (by
        rcases encodePushR64_spec src with ⟨op, hb, _⟩ | ⟨rex, op, hb, _⟩ <;> simp [hb])
        (by rcases encodePushR64_spec src with ⟨op, hb, _⟩ | ⟨rex, op, hb, _⟩ <;> simp [hb])
    · exact writable
  have hip : (pushAfter s src).RIP =
      Extracted.textAddress + BitVec.ofNat 64 (codeOffset + (encodePushR64 src).length) := by
    rw [show (pushAfter s src).RIP = BitVec.add s.RIP (BitVec.ofNat 64 (encodePushR64 src).length) from
      afterStep_push_rip ready _ _ _, rip]
    change (Extracted.textAddress + BitVec.ofNat 64 codeOffset) +
      BitVec.ofNat 64 (encodePushR64 src).length = _
    rw [BitVec.add_assoc, BitVec.ofNat_add]
  have frame : AgreesExcept [.reg 4, .mem (pushAddr s) 8, .rip] s (pushAfter s src) :=
    AgreesExcept.afterStep_push s _ _ _
  have writes : WritesWithin [.reg 4, .mem (pushAddr s) 8, .rip] #v[Stack.region initial reserve] := by
    apply stack_slot_within stack (offset := offset + 8) (len := 8) (by omega) (by omega)
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact ha.elim
    · rwa [addr] at ha
    · exact ha.elim
  refine ⟨pushAfter s src, Advances.of_step hstep (.inl ?_),
    ready.afterStep_push _ _ _ writable.low writable.tables,
    programLoaded_of_memoryWriteFrame (frame.memoryWriteFrame writes) loaded (stack_avoids avoid),
    hip, (pushAfter_rsp s src).trans addr, ?_, ?_⟩
  · rw [hip]
    exact boundary_ne_program outside (inProgram_of_textOffset _ size)
  · rw [← addr]
    exact frame
  · rw [← addr]
    rfl

end Hkdf.Proofs.Common.CallFrame
