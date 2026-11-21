import Md5.Proofs.Buffered.Update.Slices.Full.Contracts
import Md5.Proofs.Buffered.Update.Counter

namespace Md5.Proofs.Buffered.Update.Slices

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Block

abbrev fillIncrementEffect (variant : Bool) :=
  Update.Counter.incM64Effect (pc variant 0x10038f) (.sib 4 none 0 (.d32 272))

theorem fillIncrementEffect_components {variant : Bool} (s : RamState) :
    (fillIncrementEffect variant s).components = [.mem (stackPtr s + 272) 8, .flags, .rip] := by
  x86_norm [fillIncrementEffect, Update.Counter.incM64Effect, stackPtr]
  rfl

theorem fill_increment {variant : Bool} [Bindings] {boundary : ReturnBoundary} {message input : ByteArray}
    {s u : RamState} {changes : List Component}
    (h : UpdatePre (kind variant) boundary message input s) (ha : AgreesExcept changes s u)
    (hsp : stackPtr u = stackPtr s) (hrip : u.RIP = (pc variant 0x10038f))
    (hready : ReadyToStep u) (hcode : CodeIn Extracted.programImage u) :
    ∃ v, Advances boundary 1 u v ∧ ReadyToStep v ∧ CodeIn Extracted.programImage v ∧
      (fillIncrementEffect variant u).Holds u v := by
  have hw : MemoryRoutines.WritableRange u (stackPtr u + 272) 8 := by
    rw [hsp]
    cases variant <;> exact h.contextWritable_of_agrees ha 80 8 (by decide)
  have hbytes : CodeIn (codeRange (pc variant 0x10038f) [0x48, 0xff, 0x84, 0x24, 0x10, 0x01, 0x00, 0x00]) u :=
    by
      cases variant with
      | false => exact program_text_slice hcode 0x38f 8 (by decide +kernel)
      | true => exact program_text_slice hcode 0x193f 8 (by decide +kernel)
  have hap : RangeApart (stackPtr u + 272) 8 (pc variant 0x10038f) 8 := by
    intro i hi j hj heq
    apply hw.code i hi
    rw [heq]
    cases variant with
    | false =>
      have ht := text_address_in_program (0x38f + j) (by
        have hs : 0x397 ≤ Extracted.textBytes.size := by decide +kernel
        omega)
      simpa [pc, Extracted.textAddress, BitVec.ofNat_add, ← BitVec.add_assoc] using ht
    | true =>
      have ht := text_address_in_program (0x193f + j) (by
        have hs : 0x1947 ≤ Extracted.textBytes.size := by decide +kernel
        omega)
      simpa [pc, Extracted.textAddress, BitVec.ofNat_add, ← BitVec.add_assoc] using ht
  obtain ⟨v, hv, hr, he⟩ := (Update.Counter.inc_m64_effect_step
    (pc variant 0x10038f) 0x48 (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d32 272))
    (by decide) (by decide) (by decide)).advances hready hbytes
    ⟨hrip, ⟨hw.readable.low, hw.readable.mem, hw.tables⟩, hap⟩
    (by
      cases variant with
      | false => exact text_address_ne_return h.boundaryOutside 0x397 (by decide +kernel)
      | true => exact text_address_ne_return h.boundaryOutside 0x1947 (by decide +kernel))
  refine ⟨v, hv, hr, ?_, he⟩
  apply CodeIn.of_agreesExcept he.agrees _ hcode
  intro x hx c hc hcover
  change c ∈ (fillIncrementEffect variant u).components at hc
  rw [fillIncrementEffect_components] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · obtain ⟨i, hi, heq⟩ := hcover
    exact hw.code i hi (heq ▸ ⟨x.2, hx⟩)
  · exact hcover.elim
  · exact hcover.elim

set_option maxRecDepth 4096 in
theorem fill_increment_agrees {variant : Bool} {s u v : RamState}
    (hsp : stackPtr u = stackPtr s) (he : (fillIncrementEffect variant u).Holds u v) :
    AgreesExcept ((kind variant).changes s) u v := by
  have ha : AgreesExcept [.mem (stackPtr u + 272) 8, .flags, .rip] u v := by
    rw [← fillIncrementEffect_components]
    exact he.agrees
  apply ha.widen
  · intro c hc hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    all_goals cases variant <;> simp_all [kind, Component.isMem, UpdateKind.changes]
  · intro address c hc hcover
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · refine ⟨.mem ((kind variant).context s) 88, by cases variant <;> simp [kind, UpdateKind.changes], ?_⟩
      obtain ⟨i, hi, rfl⟩ := hcover
      refine ⟨80 + i, by omega, ?_⟩
      rw [hsp, BitVec.ofNat_add]
      rw [kind_context]
      change stackPtr s + 272 + BitVec.ofNat 64 i =
        stackPtr s + 192 + (80 + BitVec.ofNat 64 i)
      rw [← BitVec.add_assoc (stackPtr s + 192) 80, BitVec.add_assoc (stackPtr s) 192 80]
      rfl
    · exact hcover.elim
    · exact hcover.elim

theorem fill_increment_write {variant : Bool} {u v : RamState} (he : (fillIncrementEffect variant u).Holds u v) :
    (Operand.mem (stackPtr u + 272) : Operand 64).read v =
      (Operand.mem (stackPtr u + 272) : Operand 64).read u + 1 := by
  have hw := he.writes
  x86_norm [fillIncrementEffect, Update.Counter.incM64Effect] at hw
  exact hw

end Md5.Proofs.Buffered.Update.Slices
