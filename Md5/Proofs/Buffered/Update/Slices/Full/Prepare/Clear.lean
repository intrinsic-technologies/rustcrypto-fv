import Md5.Proofs.Buffered.Update.Slices.Full.Contracts
import Md5.Proofs.Buffered.Stores.Effect

namespace Md5.Proofs.Buffered.Update.Slices

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Block

abbrev fillClearEffect (variant : Bool) :=
  movM8Imm8Effect (pc variant 0x1003b1) (.sib 4 none 0 (.d32 255)) 0

theorem fillClearEffect_components {variant : Bool} (s : RamState) :
    (fillClearEffect variant s).components = [.mem (stackPtr s + 255) 1, .rip] := by
  x86_norm [fillClearEffect, movM8Imm8Effect, storeEffect, stackPtr]
  rfl

theorem fill_clear {variant : Bool} [Bindings] {boundary : ReturnBoundary} {message input : ByteArray}
    {s u : RamState} {changes : List Component}
    (h : UpdatePre (kind variant) boundary message input s) (ha : AgreesExcept changes s u)
    (hsp : stackPtr u = stackPtr s) (hrip : u.RIP = (pc variant 0x1003b1))
    (hready : ReadyToStep u) (hcode : CodeIn Extracted.programImage u) :
    ∃ v, Advances boundary 1 u v ∧ ReadyToStep v ∧ CodeIn Extracted.programImage v ∧
      (fillClearEffect variant u).Holds u v := by
  have hw : MemoryRoutines.WritableRange u (stackPtr u + 255) 1 := by
    rw [hsp]
    cases variant <;> exact h.contextWritable_of_agrees ha 63 1 (by decide)
  have hbytes : CodeIn (codeRange (pc variant 0x1003b1) [0xc6, 0x84, 0x24, 0xff, 0x00, 0x00, 0x00, 0x00]) u :=
    by
      cases variant with
      | false => exact program_text_slice hcode 0x3b1 8 (by decide +kernel)
      | true => exact program_text_slice hcode 0x1961 8 (by decide +kernel)
  have hap : RangeApart (stackPtr u + 255) 1 (pc variant 0x1003b1) 8 := by
    intro i hi j hj heq
    apply hw.code i hi
    rw [heq]
    cases variant with
    | false =>
      have ht := text_address_in_program (0x3b1 + j) (by
        have hs : 0x3b9 ≤ Extracted.textBytes.size := by decide +kernel
        omega)
      simpa [pc, Extracted.textAddress, BitVec.ofNat_add, ← BitVec.add_assoc] using ht
    | true =>
      have ht := text_address_in_program (0x1961 + j) (by
        have hs : 0x1969 ≤ Extracted.textBytes.size := by decide +kernel
        omega)
      simpa [pc, Extracted.textAddress, BitVec.ofNat_add, ← BitVec.add_assoc] using ht
  obtain ⟨v, hv, hr, he⟩ := (Stores.mov_m8_imm8_effect_step
    (pc variant 0x1003b1) (.sib 4 none 0 (.d32 255))
    (by decide) (by decide) (by decide) 0).advances hready hbytes
    ⟨hrip, ⟨hw.readable.low, hw.readable.mem, hw.tables⟩, hap⟩
    (by
      cases variant with
      | false => exact text_address_ne_return h.boundaryOutside 0x3b9 (by decide +kernel)
      | true => exact text_address_ne_return h.boundaryOutside 0x1969 (by decide +kernel))
  refine ⟨v, hv, hr, ?_, he⟩
  apply CodeIn.of_agreesExcept he.agrees _ hcode
  intro x hx c hc hcover
  change c ∈ (fillClearEffect variant u).components at hc
  rw [fillClearEffect_components] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · obtain ⟨i, hi, heq⟩ := hcover
    exact hw.code i hi (heq ▸ ⟨x.2, hx⟩)
  · exact hcover.elim

set_option maxRecDepth 4096 in
theorem fill_clear_agrees {variant : Bool} {s u v : RamState}
    (hsp : stackPtr u = stackPtr s) (he : (fillClearEffect variant u).Holds u v) :
    AgreesExcept ((kind variant).changes s) u v := by
  have ha : AgreesExcept [.mem (stackPtr u + 255) 1, .rip] u v := by
    rw [← fillClearEffect_components]
    exact he.agrees
  apply ha.widen
  · intro c hc hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    all_goals cases variant <;> simp_all [kind, Component.isMem, UpdateKind.changes]
  · intro address c hc hcover
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · refine ⟨.mem ((kind variant).context s) 88, by cases variant <;> simp [kind, UpdateKind.changes], ?_⟩
      obtain ⟨i, hi, rfl⟩ := hcover
      refine ⟨63 + i, by omega, ?_⟩
      rw [hsp, BitVec.ofNat_add]
      rw [kind_context]
      change stackPtr s + 255 + BitVec.ofNat 64 i =
        stackPtr s + 192 + (63 + BitVec.ofNat 64 i)
      rw [← BitVec.add_assoc (stackPtr s + 192) 63, BitVec.add_assoc (stackPtr s) 192 63]
      rfl
    · exact hcover.elim

end Md5.Proofs.Buffered.Update.Slices
